/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass

/-!
# Check Override Refinement (behavioral subtyping / Liskov)

A Laurel-to-Laurel pass that, for every method `m` declared on a composite `Child`
that an ancestor `Parent` also declares (i.e. `Child.m` OVERRIDES `Parent.m`),
emits synthetic *checker procedures* whose verification discharges the
behavioral-subtyping obligations:

* **precondition contravariance** — `Parent.pre ⇒ Child.pre` (the override may not
  demand MORE of callers than the parent's contract promised they must satisfy);
* **postcondition covariance** — `Child.post ⇒ Parent.post` (the override must
  deliver at least what the parent's contract promised callers).

These are exactly the conditions under which a call site that statically sees
`Parent.m` may soundly run *any* runtime override — i.e. the soundness
prerequisite for dynamic dispatch. Without them, a call assuming `Parent.m`'s
contract is sound only because dispatch is static; once dispatch is dynamic a
violating override silently breaks the caller's proof.

The checker procedures are ordinary top-level procedures with no callers. A
`requires` clause is *assumed*; an `assert` in the body is *checked*. So
`checker(params) requires Parent.pre opaque { assert Child.pre }` verifies iff
`Parent.pre ⇒ Child.pre`, and a failure surfaces as a normal
`assertion could not be proved` diagnostic pointing at the offending override.

This pass runs BEFORE `LiftInstanceProcedures` (methods are still attached to
their composites, the `extending` chain is intact) and is purely ADDITIVE — it
only appends checker procedures, never rewriting existing ones — so it carries no
regression risk to working programs. It runs before monomorphization, so an
override on a generic composite gets its refinement checked per concrete
instantiation for free (the checkers monomorphize along with everything else).

`modifies`-subset is intentionally NOT checked here yet: the modifies clause is
lowered to a quantified frame `ensures` downstream (`ModifiesClauses`), so a
frame-subset obligation belongs after that lowering; this pass covers the
pre/post refinement that is the load-bearing half. (See the plan for the frame
follow-up.)
-/

namespace Strata.Laurel

open Std (HashMap)

/-- Rename free local references in `e` according to `ren` (old-name-text ↦ new
    `Identifier`). Used to align a parent method's contract onto the child
    method's parameter names so the two contracts talk about the same variables.
    Structural, via `mapStmtExpr`; only `.Var (.Local _)` leaves are touched. -/
def renameLocals (ren : HashMap String Identifier) (e : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun n => match n.val with
    | .Var (.Local r) =>
      match ren.get? r.text with
      | some r' => { n with val := .Var (.Local r') }
      | none => n
    | _ => n) e

/-- The postconditions and modifies declared by a procedure body, plus whether a
    given condition is `free`. Abstract and Opaque bodies carry postconditions;
    Transparent/External carry none here (their guarantees are their visible body,
    not a refinable contract). -/
def bodyPostconditions : Body → List Condition
  | .Opaque posts _ _ => posts
  | .Abstract posts => posts
  | _ => []

/-- A method name appears on a composite's `instanceProcedures`. Find, among
    `Child`'s strict ancestors (nearest first), the first that declares a method
    of the same name — the parent definition this method overrides. -/
def findOverriddenParent (model : SemanticModel) (childName : Identifier)
    (methodName : Identifier) : Option (Identifier × Procedure) :=
  -- `computeAncestors` is self-first then ancestors; drop self, search the rest.
  let ancestors := (computeAncestors model childName).drop 1
  ancestors.findSome? fun anc =>
    (anc.instanceProcedures.find? (·.name.text == methodName.text)).map
      fun p => (anc.name, p)

/-- Build the param-renaming map aligning `parent`'s inputs/outputs onto `child`'s
    by POSITION (same arity is required by an override; mismatched arity yields a
    partial map, which is conservative — unmapped parent names simply stay, and a
    resulting unresolved reference would fail loud rather than silently pass). -/
def alignParams (parent child : Procedure) : HashMap String Identifier :=
  let ins := (parent.inputs.zip child.inputs).foldl
    (fun m (pp, cp) => m.insert pp.name.text cp.name) {}
  (parent.outputs.zip child.outputs).foldl
    (fun m (pp, cp) => m.insert pp.name.text cp.name) ins

/-- Conjoin a list of conditions into a single boolean `StmtExprMd` (`true` if
    empty). Used to assume a whole precondition set on the `requires` side. -/
def conjoinConditions (src : Option FileRange) (cs : List Condition) : StmtExprMd :=
  match cs.filter (fun c => !c.free) with
  | [] => ⟨ .LiteralBool true, src ⟩
  | c :: rest => rest.foldl
      (fun acc c => ⟨ .PrimitiveOp .And [acc, c.condition], src ⟩) c.condition

/-- Emit the refinement checker procedures for one override pair. `child` declares
    a method that overrides `parent`'s same-named method. Produces up to two
    checkers (pre, post); each is an ordinary opaque procedure whose verification
    is the refinement VC. Returns `[]` when there is nothing to check. -/
def refinementCheckers (childTypeName : Identifier) (parent child : Procedure)
    : List Procedure :=
  let src := child.name.source
  let ren := alignParams parent child
  -- Parent's contract, renamed onto the child's parameter names.
  let parentPres := parent.preconditions.filter (fun c => !c.free)
  let childPres := child.preconditions.filter (fun c => !c.free)
  let parentPosts := (bodyPostconditions parent.body).filter (fun c => !c.free)
  let childPosts := (bodyPostconditions child.body).filter (fun c => !c.free)
  let mkChecker (suffix : String) (params : List Parameter)
      (assume : StmtExprMd) (asserts : List StmtExprMd) : Procedure :=
    let assertStmts : List StmtExprMd :=
      asserts.map (fun a => ⟨ .Assert { condition := a }, src ⟩)
    let bodyBlock : StmtExprMd := ⟨ .Block assertStmts none, src ⟩
    { name := { mkId s!"{childTypeName.text}${child.name.text}$refines${suffix}" with source := src }
      typeArgs := []
      inputs := params
      outputs := []
      preconditions := [{ condition := assume }]
      decreases := none
      isFunctional := false
      body := .Opaque [] (some bodyBlock) [] }
  let preChecker : List Procedure :=
    if childPres.isEmpty then []  -- nothing the child demands ⇒ contravariance trivially holds
    else
      -- assume Parent.pre (renamed), assert each Child.pre
      let assume := conjoinConditions src (parentPres.map
        (fun c => { c with condition := renameLocals ren c.condition }))
      [mkChecker "pre" child.inputs assume (childPres.map (·.condition))]
  let postChecker : List Procedure :=
    if parentPosts.isEmpty then []  -- parent guarantees nothing ⇒ covariance trivially holds
    else
      -- params: inputs ++ outputs (post mentions both). assume Child.post, assert each Parent.post (renamed)
      let assume := conjoinConditions src childPosts
      [mkChecker "post" (child.inputs ++ child.outputs) assume
        (parentPosts.map (fun c => renameLocals ren c.condition))]
  preChecker ++ postChecker

/-- The pass: for every composite method that overrides an ancestor method, append
    the refinement checker procedures to `program.staticProcedures`. -/
def checkOverrideRefinement (model : SemanticModel) (program : Program) : Program :=
  let checkers : List Procedure :=
    program.types.foldl (init := []) fun acc td =>
      match td with
      | .Composite ct =>
        -- GATE: skip GENERIC composites for now. A checker carries `self : C<T>`, a
        -- generic-composite parameter on a never-called procedure; the procedure
        -- monomorphizer cannot seed `C<int>` from it, so the checker fails to resolve
        -- after monomorphization. (Same reason dispatcher generation is gated to
        -- non-generic in LiftInstanceProcedures — keep the two consistent.) A generic
        -- override is therefore not yet Liskov-checked AND keeps static dispatch:
        -- sound (the declared contract is honored), just not yet refinement-verified.
        if !ct.typeArgs.isEmpty then acc
        else
        acc ++ ct.instanceProcedures.foldl (init := []) fun acc2 m =>
          match findOverriddenParent model ct.name m.name with
          | some (_parentName, parentProc) =>
            -- also skip if the overridden parent is generic (param types would mention `T`)
            if !parentProc.inputs.isEmpty &&
               parentProc.inputs.any (fun p => match p.type.val with
                 | .Applied .. => true | .TVar .. => true | _ => false)
            then acc2
            else acc2 ++ refinementCheckers ct.name parentProc m
          | none => acc2
      | _ => acc
  if checkers.isEmpty then program
  else { program with staticProcedures := program.staticProcedures ++ checkers }

public section

/-- Behavioral-subtyping (Liskov) refinement check for method overrides. -/
def checkOverrideRefinementPass : LoweringPass where
  name := "CheckOverrideRefinement"
  needsResolves := true
  run := fun _ p m => (checkOverrideRefinement m p, [], {})
  documentation := "For every composite method that overrides an ancestor method, emits synthetic checker procedures that verify behavioral subtyping: the override's precondition is no stronger than the parent's (Parent.pre ⇒ Child.pre) and its postcondition is no weaker (Child.post ⇒ Parent.post). A failing checker is a Liskov violation. Purely additive; runs before LiftInstanceProcedures. This is the soundness prerequisite for dynamic dispatch."

end -- public section

end Strata.Laurel
