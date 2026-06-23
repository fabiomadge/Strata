/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.EliminateValueInReturns


/-!
# Lift Instance Procedures

A Laurel-to-Laurel pass that lifts every instance procedure (a procedure
defined inside a `composite` block) to a top-level static procedure with a
mangled name `<CompositeName>$<methodName>`, then rewrites every call site
that resolved to such an instance procedure to use the lifted name.

After this pass:
- `CompositeType.instanceProcedures` is empty for every composite.
- `program.staticProcedures` contains the lifted procedures.
- Every `InstanceCall` (from `obj#method(args)` surface syntax) points
  at the lifted name. For `InstanceCall`, the receiver is prepended to
  the argument list to match the lifted procedure's `self : <CompositeName>`
  parameter.
-/

namespace Strata.Laurel

/-! ## Lifting + call-site rewriting

Lift instance procedures to static scope (e.g., procedure `proc`
of composite type `T` will be lifted to `T$proc`).
Then, rewrite caller-side of `obj#proc` to call the lifted procedure

-/

/-- Top-level name produced for a lifted instance procedure. -/
def liftedProcName (typeName methodName : Identifier) : Identifier :=
  {mkId s!"{typeName.text}${methodName.text}" with source := methodName.source}

/-- Rewrite a single node so that any callee resolving to an instance procedure
    is replaced by its lifted name. -/
private def rewriteCallNode (model : SemanticModel) (expr : StmtExprMd) : StmtExprMd :=
  match expr.val with
  | .StaticCall callee args =>
    match model.get? callee with
    | some (.instanceProcedure typeName _) =>
      let lifted := liftedProcName typeName callee
      { expr with val := .StaticCall lifted args }
    | _ => expr
  | .InstanceCall target callee args =>
    -- `obj#method(args)` surface syntax parses to InstanceCall. Flatten it to
    -- a static call against the lifted name, prepending the receiver as the
    -- first argument to match the lifted procedure's `self` parameter.
    match model.get? callee with
    | some (.instanceProcedure typeName _) =>
      let lifted := liftedProcName typeName callee
      { expr with val := .StaticCall lifted (target :: args) }
    | _ => expr
  | _ => expr

/-! ## Dynamic dispatch: tag-switch dispatcher generation

When a method `m` declared on a composite `D` is OVERRIDDEN by a strict descendant,
the lifted `D$m` is generated as a runtime-tag DISPATCHER rather than `D`'s body
verbatim, so a call on a `D`-typed receiver holding a more-derived value runs the
derived override (matching Java/C# semantics). Concretely:

* every declaring type `T` in the family gets its real body lifted to `T$m$impl`;
* `D$m` becomes `if self is O₁ then O₁$m$impl(self as O₁, …) else … else D$m$impl(self, …)`
  over `D`'s descendant-overriders `Oᵢ` (most-derived first), carrying `D`'s own
  contract so callers see the static contract.

This is SOUND because the separate behavioral-subtyping (Liskov) checks
(`CheckOverrideRefinement`, run just before this pass) guarantee every override
refines its parent's contract, so each branch's impl postcondition implies `D`'s.
Methods overridden nowhere keep today's plain `D$m = body` (no dispatcher, no
`$impl`), so non-inheriting code is byte-identical. -/

/-- Name for the real (non-virtual) implementation of a method on `typeName`,
    used as a dispatcher branch target. -/
def implProcName (typeName methodName : Identifier) : Identifier :=
  {mkId s!"{typeName.text}${methodName.text}$impl" with source := methodName.source}

-- The family predicates below are SHARED with `CheckOverrideRefinement` (the Liskov
-- pass), so they must be public — see `isVirtualDispatchMethod`.
public section

/-- Does `ct` declare a method named `mname` (vs inherit it)? -/
def declaresMethod (ct : CompositeType) (mname : String) : Bool :=
  ct.instanceProcedures.any (·.name.text == mname)

/-- The strict descendants of `ancestorName` that DECLARE `mname`, i.e. the
    overrides visible through an `ancestorName`-typed receiver. Ordered
    most-derived first (deeper `ancestors`-distance first), so the generated
    `is`-chain tests the most specific type before its supertypes — required
    because a value `is` all of its ancestors. -/
def descendantOverriders (model : SemanticModel) (program : Program)
    (ancestorName : Identifier) (mname : String) : List CompositeType :=
  let composites := program.types.filterMap fun td =>
    match td with | .Composite ct => some ct | _ => none
  -- T is a strict descendant of `ancestorName` iff `ancestorName` is among T's
  -- ancestors and T ≠ ancestorName. Tag each with its ancestor-distance to order.
  let tagged := composites.filterMap fun t =>
    if t.name.text == ancestorName.text then none
    else if declaresMethod t mname then
      let anc := (computeAncestors model t.name).map (·.name.text)
      if anc.contains ancestorName.text
      then some (t, anc.length)  -- deeper subtype ⇒ longer ancestor chain
      else none
    else none
  -- most-derived (longest ancestor chain) first
  (tagged.toArray.qsort (fun a b => a.2 > b.2)).toList.map (·.1)

/-! ### Dynamic-dispatch family predicates (the SINGLE source of truth for both
    the dispatcher generation here AND the Liskov refinement check in
    `CheckOverrideRefinement`). Keeping these in ONE place is load-bearing for
    SOUNDNESS: a method that gets a runtime-tag dispatcher (becomes virtual) MUST
    also get its override-refinement checked, else dynamic dispatch would run an
    override whose contract was never verified to refine the parent. The two passes
    therefore gate on the SAME `isVirtualDispatchMethod`. -/

/-- `mname` declared on `declarerName` is overridden within its inheritance family:
    some strict descendant declares it, OR some strict ancestor declares it. -/
def isOverriddenMethod (model : SemanticModel) (program : Program)
    (declarerName : Identifier) (mname : String) : Bool :=
  (! (descendantOverriders model program declarerName mname).isEmpty)
  || ((computeAncestors model declarerName).drop 1).any (fun anc =>
        anc.instanceProcedures.any (·.name.text == mname))

/-- The `mname` family rooted at `declarerName` involves a GENERIC composite
    (the declarer's ancestors that declare `m`, or any descendant overrider, carry
    type parameters). Dynamic dispatch + refinement checking are gated OFF for such
    families for now: a dispatcher/checker would reference a generic instantiation
    (`SBox<T>`) that the procedure monomorphizer cannot yet seed from `Box<int>`.
    Such families keep STATIC dispatch — sound, just not virtual. -/
def familyIsGeneric (model : SemanticModel) (program : Program)
    (declarerName : Identifier) (mname : String) : Bool :=
  (computeAncestors model declarerName).any (fun c =>
    !c.typeArgs.isEmpty && c.instanceProcedures.any (·.name.text == mname))
  || (descendantOverriders model program declarerName mname).any (fun c => !c.typeArgs.isEmpty)

/-- THE shared gate: a method dispatched virtually (gets a dispatcher) AND, by the
    same predicate, gets its override-refinement (Liskov) checked. Both passes call
    this so the two cannot drift into the unsound "dispatcher without checker" state. -/
def isVirtualDispatchMethod (model : SemanticModel) (program : Program)
    (declarerName : Identifier) (mname : String) : Bool :=
  isOverriddenMethod model program declarerName mname
    && ! familyIsGeneric model program declarerName mname

end -- public section (shared family predicates)

/-- Build the dispatcher body for `method` on `ownerType`, branching over
    `overriders` (most-derived first) and falling through to `ownerType`'s own
    impl. Each branch casts `self` to the branch type (sound: guarded by the
    preceding `is`), then calls that type's `$impl`. Mirrors the hand-verified
    `if self is Sub then (self as Sub)#m_impl else …` dispatcher shape. -/
private def buildDispatcherBody (ownerType : Identifier) (method : Procedure)
    (overriders : List CompositeType) : AstNode StmtExpr :=
  let src := method.name.source
  let selfName := (method.inputs.head?.map (·.name)).getD (mkId "self")
  -- non-self inputs, as Local-ref arguments (shared by every branch)
  let restArgs : List (AstNode StmtExpr) :=
    (method.inputs.drop 1).map fun p => ⟨ .Var (.Local p.name), src ⟩
  -- a call `Target$m$impl(recv, restArgs...)`, assigned to the outputs (if any)
  let callTo (target : Identifier) (recv : AstNode StmtExpr) : AstNode StmtExpr :=
    let call : AstNode StmtExpr := ⟨ .StaticCall target (recv :: restArgs), src ⟩
    match method.outputs with
    | [] => call
    | outs =>
      let targets : List (AstNode Variable) := outs.map fun o => ⟨ .Local o.name, src ⟩
      ⟨ .Assign targets call, src ⟩
  -- the else (fallthrough): owner's own impl, self uncast (already : ownerType)
  let fallthrough : AstNode StmtExpr :=
    callTo (implProcName ownerType method.name) ⟨ .Var (.Local selfName), src ⟩
  -- fold the overriders into a most-derived-first `is`/`as` chain
  overriders.foldr (init := fallthrough) fun ov acc =>
    -- A generic overrider must be tested AS an instantiation: `SBox<T> extends Box<T>`
    -- is tested `self is SBox<T>` (bare `SBox` is rejected as an un-applied generic).
    -- It shares the owner's type parameters, so apply it to its own declared params as
    -- `.TVar`s (which are the dispatcher's params after lifting carries them on).
    let ovTy : HighTypeMd :=
      if ov.typeArgs.isEmpty then ⟨ .UserDefined ov.name, src ⟩
      else ⟨ .Applied ⟨ .UserDefined ov.name, src ⟩ (ov.typeArgs.map (fun a => (⟨ .TVar a, src ⟩ : HighTypeMd))), src ⟩
    let isCheck : AstNode StmtExpr := ⟨ .IsType ⟨ .Var (.Local selfName), src ⟩ ovTy, src ⟩
    let castName := mkId s!"$self${ov.name.text}"
    let castDecl : AstNode StmtExpr :=
      ⟨ .Assign [⟨ .Declare ⟨castName, ovTy⟩, src ⟩]
        ⟨ .AsType ⟨ .Var (.Local selfName), src ⟩ ovTy, src ⟩, src ⟩
    let branchCall := callTo (implProcName ov.name method.name) ⟨ .Var (.Local castName), src ⟩
    let thenBlock : AstNode StmtExpr := ⟨ .Block [castDecl, branchCall] none, src ⟩
    ⟨ .IfThenElse isCheck thenBlock (some acc), src ⟩

/-- The postconditions of `D$m`'s dispatcher, tag-conditioned so each holds on the
    branch that runs. Because `m` is opaque, callers reason against these (not the body):

    * owner `D`'s own posts, guarded `(!(self is O₁) & … & !(self is Oₙ)) ==> D.post` —
      they hold on the fallthrough path. The guard is essential: an UNguarded `D.post`
      would be promised even when the body runs an override returning a different value,
      which `D$m` could not prove. (The guard uses ancestor-membership `is`; since the
      branches are checked most-derived-first the body still picks the right impl.)
    * each overrider `Oᵢ`'s posts, `(self is Oᵢ) ==> Oᵢ.post` — so a caller that knows
      the runtime tag (after `is`/`as`, or via a more-derived static type) recovers the
      override's STRONGER guarantee through a `D`-typed reference.

    SOUND: each clause is discharged by the matching dispatcher branch, whose `$impl`
    postcondition is exactly that type's post. (Cross-branch `is`-overlap — a deeper
    descendant `is` a shallower one — is handled by the body order and the guard; a
    Liskov-valid hierarchy keeps the clauses mutually consistent, since `Oᵢ.post ⟹ Oⱼ.post`
    whenever `Oᵢ <: Oⱼ`.) Overrider posts are renamed (self+outputs, positionally). -/
private def dispatcherPosts (ownerPosts : List Condition) (method : Procedure)
    (overriders : List CompositeType) : List Condition :=
  let src := method.name.source
  let selfName := (method.inputs.head?.map (·.name)).getD (mkId "self")
  let isOf (ct : CompositeType) : StmtExprMd :=
    ⟨ .IsType ⟨ .Var (.Local selfName), src ⟩ ⟨ .UserDefined ct.name, src ⟩, src ⟩
  let overriderPosts : List Condition := overriders.filterMap fun ov =>
    match ov.instanceProcedures.find? (·.name.text == method.name.text) with
    | none => none
    | some ovProc =>
      -- re-express the overrider's contract in the dispatcher's parameter names
      let rename := renameProcLocals ovProc method
      let ovPostsAll : List Condition := match ovProc.body with
        | .Opaque posts _ _ => posts
        | .Abstract posts => posts
        | _ => []
      match ovPostsAll.filter (fun c => !c.free) with
      | [] => none
      | ovPosts =>
        let conj := conjoinAnd src (ovPosts.map (fun c => rename c.condition))
        some { condition := impliesMd src (isOf ov) conj }
  let notAnyOverrider : StmtExprMd := conjoinAnd src (overriders.map (fun ov => notMd src (isOf ov)))
  let guardedOwnerPosts : List Condition := (ownerPosts.filter (fun c => !c.free)).map fun c =>
    { c with condition := impliesMd src notAnyOverrider c.condition }
  guardedOwnerPosts ++ overriderPosts

/-- Apply call-site rewriting to every expression in a procedure. -/
private def rewriteCallsInProc (model : SemanticModel) (proc : Procedure) : Procedure :=
  let f := mapStmtExpr (rewriteCallNode model)
  let resolveBody : Body → Body := fun body => match body with
    | .Transparent b => .Transparent (f b)
    | .Opaque ps impl modif =>
      .Opaque (ps.map (·.mapCondition f)) (impl.map f) (modif.map f)
    | .Abstract ps => .Abstract (ps.map (·.mapCondition f))
    | .External => .External
  { proc with
    body := resolveBody proc.body
    preconditions := proc.preconditions.map (·.mapCondition f)
    decreases := proc.decreases.map f
    invokeOn := proc.invokeOn.map f }

/-- Apply call-site rewriting to a constrained type's constraint and witness. -/
private def rewriteCallsInType (model : SemanticModel) (td : TypeDefinition) : TypeDefinition :=
  match td with
  | .Constrained ct =>
    let f := mapStmtExpr (rewriteCallNode model)
    .Constrained { ct with constraint := f ct.constraint, witness := f ct.witness }
  | _ => td

public section

/--
Lift every `proc ∈ ct.instanceProcedures` to a top-level static procedure
named via `liftedProcName`, rewrite call sites that resolved to an instance
procedure, and clear `instanceProcedures` on every composite.
-/
def liftInstanceProcedures (model : SemanticModel) (program : Program) : Program :=
  -- Step 1: collect lifted clones. The lifted proc's type params are the composite's
  -- followed by the method's own: `get(self: Box<T>)` on `composite Box<T>` becomes
  -- `Box$get<T>(self: Box<T>)`, and `id2<U>(self: Box<T>)` becomes `Box$id2<T,U>`. The
  -- result is an ordinary polymorphic procedure with a generic-composite param — the
  -- shape the procedure monomorphizer (running AFTER this pass) already handles, so no
  -- new machinery is needed. A non-generic composite contributes `[]`, leaving a
  -- non-generic method's `typeArgs` unchanged.
  --
  -- DYNAMIC DISPATCH: if a method is overridden by a strict descendant, its lifted
  -- entry `T$m` is generated as a runtime-tag DISPATCHER and the real body is lifted
  -- to `T$m$impl`; otherwise `T$m` is the body verbatim (today's static behavior).
  -- The dispatcher carries the method's own contract (preconditions kept; the body
  -- becomes the tag-switch, whose branch `$impl` postconditions imply it by the
  -- Liskov refinement checks run in the previous pass).
  --
  -- A method `m` is POLYMORPHIC if it is declared on more than one type within a
  -- single inheritance family (i.e. some type's `m` is overridden by a descendant,
  -- OR equivalently some declarer has a strict ancestor that also declares `m`).
  -- Every declarer of a polymorphic `m` emits BOTH `T$m$impl` (its real body) and a
  -- dispatcher `T$m` over its own descendant-overriders — so the `$impl` branch
  -- targets a dispatcher references always exist, even for a leaf override.
  -- Dispatcher generation uses the SHARED `isVirtualDispatchMethod` gate (defined
  -- above, also called by `CheckOverrideRefinement`) so the two passes cannot drift
  -- into a dispatcher-without-Liskov-checker (unsound) state. It is true exactly when
  -- `m` is overridden in a NON-GENERIC family. (Generic families are gated off for
  -- now: a dispatcher's `is`/`as`/`$impl` references to a generic instantiation
  -- `SBox<T>` are not yet discovered by the procedure monomorphizer from `Box<int>`.
  -- They keep STATIC dispatch — sound, just not virtual.)
  let liftedProcs : List Procedure :=
    program.types.foldl (init := []) fun acc td =>
      match td with
      | .Composite ct =>
        acc ++ ct.instanceProcedures.flatMap fun proc =>
          let tyArgs := ct.typeArgs ++ proc.typeArgs
          if ! isVirtualDispatchMethod model program ct.name proc.name.text then
            -- monomorphic method ⇒ plain static lift (unchanged behavior)
            [{ proc with name := liftedProcName ct.name proc.name, typeArgs := tyArgs }]
          else
            -- polymorphic: real body → `T$m$impl`; `T$m` → dispatcher (same contract).
            let overriders := descendantOverriders model program ct.name proc.name.text
            let impl := { proc with name := implProcName ct.name proc.name, typeArgs := tyArgs }
            -- dispatcher postconditions: owner's own posts guarded by the fallthrough
            -- condition + each overrider's posts guarded by its tag (precision).
            let dispatcherBody : Body := match proc.body with
              | .Transparent _ => .Transparent (buildDispatcherBody ct.name proc overriders)
              | .Opaque posts _ modif =>
                  .Opaque (dispatcherPosts posts proc overriders)
                    (some (buildDispatcherBody ct.name proc overriders)) modif
              | .Abstract posts =>
                  .Opaque (dispatcherPosts posts proc overriders)
                    (some (buildDispatcherBody ct.name proc overriders)) []
              | .External => .External
            let dispatcher := { proc with name := liftedProcName ct.name proc.name,
                                          typeArgs := tyArgs, body := dispatcherBody }
            [impl, dispatcher]
      | _ => acc

  if liftedProcs.isEmpty then program else

  -- Step 2: rewrite call sites in procedure bodies and constrained-type
  let rewrittenStaticProcs := program.staticProcedures.map (rewriteCallsInProc model)
  let rewrittenLiftedProcs := liftedProcs.map (rewriteCallsInProc model)
  let rewrittenTypes := program.types.map (rewriteCallsInType model)

  -- Step 3: clear instanceProcedures on every composite.
  let cleanedTypes := rewrittenTypes.map fun td =>
    match td with
    | .Composite ct => .Composite { ct with instanceProcedures := [] }
    | _ => td

  -- Step 4: append lifted procs.
  { program with
    staticProcedures := rewrittenStaticProcs ++ rewrittenLiftedProcs
    types := cleanedTypes }

end -- public section

/-- Pipeline pass: lift instance procedures to top-level static procedures
    and rewrite call sites to use the lifted names. -/
public def liftInstanceProceduresPass : LoweringPass where
  name := "LiftInstanceProcedures"
  documentation := "Lifts every procedure declared inside a `composite` block to a top-level static procedure named `<CompositeName>$<methodName>` and rewrites call sites resolved to an instance procedure (including `obj#method(args)` surface syntax) to point at the lifted name. Clears `instanceProcedures` on every composite. Must run before HeapParameterization."
  needsResolves := true
  run := fun _ p m => (liftInstanceProcedures m p, [], {})
  comesBefore := [⟨ eliminateValueInReturnsPass.meta, "eliminateValueInReturns only applies to static methods, hence all instance methods must have been lifted before." ⟩]

end Strata.Laurel
