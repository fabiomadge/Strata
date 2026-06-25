/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.LiftInstanceProcedures

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

`modifies`-subset is enforced as a SIDE EFFECT of the two-state-faithful post-checker
(see `refinementCheckers`): the post-checker carries the PARENT's modifies and proves
the parent post over a heap havoc'd per the CHILD's frame, so `ModifiesClauses` emits
the parent frame-`ensures` on the checker and an override that WIDENS the frame fails
to re-establish it (a frame-widening override is rejected at definition time — see
corpus `mixed_modifies_frame_widen_rejected`, which is now also caught here, not only
at the dispatch call site). This was previously deferred; the `old()` fix subsumed it.
-/

namespace Strata.Laurel

/-- The postconditions and modifies declared by a procedure body, plus whether a
    given condition is `free`. Abstract and Opaque bodies carry postconditions;
    Transparent/External carry none here (their guarantees are their visible body,
    not a refinable contract). -/
def bodyPostconditions : Body → List Condition
  | .Opaque posts _ _ => posts
  | .Abstract posts => posts
  | _ => []

/-- The `modifies` clause declared by a procedure body. Only `Opaque` bodies carry
    one; everything else has an empty frame. Used to give the post-checker's
    synthesized companion the SAME frame the override declares, so the companion is
    classified a heap-writer (`HeapParameterization.analyzeProc`: `impl.isNone &&
    !modif.isEmpty`) and `CallElim` havocs the heap per that frame. -/
def bodyModifies : Body → List StmtExprMd
  | .Opaque _ _ modifies => modifies
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

/-- Conjoin the non-`free` conditions in `cs` into a single boolean `StmtExprMd`
    (`true` if none). Used to assume a whole precondition/postcondition set on the
    `requires` side of a checker. Delegates to the shared `conjoinAnd`. -/
def conjoinConditions (src : Option FileRange) (cs : List Condition) : StmtExprMd :=
  conjoinAnd src ((nonFreeConditions cs).map (·.condition))

/-- Emit the refinement checker procedures for one override pair. `child` declares
    a method that overrides `parent`'s same-named method. Produces up to two
    checkers (pre, post); each is an ordinary opaque procedure whose verification
    is the refinement VC. Returns `[]` when there is nothing to check. -/
def refinementCheckers (childTypeName : Identifier) (childTypeArgs : List Identifier)
    (parent child : Procedure) : List Procedure :=
  let src := child.name.source
  -- Re-express the PARENT's contract in the CHILD's parameter names (load-bearing
  -- argument order: source = parent, target = child).
  let rename := renameProcLocals parent child
  let parentPres := nonFreeConditions parent.preconditions
  let childPres := nonFreeConditions child.preconditions
  let parentPosts := nonFreeConditions (bodyPostconditions parent.body)
  let childPosts := nonFreeConditions (bodyPostconditions child.body)
  let childModifies := bodyModifies child.body
  let parentModifies := bodyModifies parent.body
  -- The shared type-arg list every synthesized proc carries: the child composite's
  -- type params (+ any method-level ones) so a GENERIC override (`self : C<T>`) is
  -- indexed as a poly proc by `MonomorphizeComposites.indexGenerics` and monomorphized
  -- per instantiation — mirrors how lifted methods carry `ct.typeArgs ++ proc.typeArgs`.
  -- Empty for a non-generic family ⇒ byte-identical to before.
  let allTypeArgs := childTypeArgs ++ child.typeArgs
  let preChecker : List Procedure :=
    if childPres.isEmpty then []  -- nothing the child demands ⇒ contravariance trivially holds
    else
      -- assume Parent.pre (renamed), assert each Child.pre. The pre-checker is
      -- single-state (preconditions never reference `old`/the post-heap), so it keeps
      -- the simple assert-in-body shape — no companion / heap threading needed.
      let assume := conjoinConditions src (parentPres.map
        (fun c => { c with condition := rename c.condition }))
      let assertStmts : List StmtExprMd :=
        (childPres.map (·.condition)).map (fun a => ⟨ .Assert { condition := a }, src ⟩)
      [{ name := { refinementProcName childTypeName child.name "refines$pre" with source := src }
         typeArgs := allTypeArgs
         inputs := child.inputs
         outputs := []
         preconditions := [{ condition := assume }]
         decreases := none
         isFunctional := false
         body := .Opaque [] (some ⟨ .Block assertStmts none, src ⟩) [] }]
  -- POST-checker (covariance), TWO-STATE-FAITHFUL. The old buggy encoding emitted the
  -- checker heap-NEUTRAL (empty modifies, body only `assert`), so `HeapParameterization`
  -- never gave it an inout `$heap`; `PushOldInward` then collapsed every `old(field)` to
  -- the current heap, making any two-state Parent/Child post vacuous (assume-false /
  -- assert-trivial → a Liskov violation slipped through at definition time).
  --
  -- Fix (reuses the proven dispatcher-frame mechanism): emit a bodyless `$childspec`
  -- companion carrying the CHILD's post + modifies, and have the post-checker CALL it,
  -- then prove the PARENT's post via its own `ensures` (so `ModifiesClauses` conjoins the
  -- PARENT frame), carrying the PARENT's modifies. The checker, by calling a heap-writer
  -- companion, becomes a transitive heap-writer → gains an inout `$heap` → `old()`
  -- survives `PushOldInward`. `CallElim` havocs `$heap` per the companion's (child) frame
  -- and assumes Child.post; the checker must then re-establish Parent.post AND the parent
  -- frame over that havoc'd heap. This is the SAME path that already rejects frame-widening
  -- at dispatch call sites (corpus `mixed_modifies_frame_widen_rejected`).
  let postCheckers : List Procedure :=
    if parentPosts.isEmpty then []  -- parent guarantees nothing ⇒ covariance trivially holds
    else
      let specName := refinementProcName childTypeName child.name "childspec"
      let checkerName := refinementProcName childTypeName child.name "refines$post"
      -- Companion: child's signature, child's (renamed-to-itself = identity) post +
      -- modifies, NO implementation. `impl.isNone && !modif.isEmpty` ⇒ heap-writer.
      let companion : Procedure :=
        { name := { specName with source := src }
          typeArgs := allTypeArgs
          inputs := child.inputs
          outputs := child.outputs
          preconditions := []
          decreases := none
          isFunctional := false
          body := .Opaque childPosts none childModifies }
      -- Checker body: call `$childspec(selfArgs...)` assigning the outputs, exactly like
      -- the dispatcher's `callTo`. The call's contract-inlining havocs the heap per the
      -- companion frame and assumes Child.post.
      let selfArgs : List (AstNode StmtExpr) :=
        child.inputs.map fun p => ⟨ .Var (.Local p.name), src ⟩
      let callStmt : AstNode StmtExpr := mkCallAssigningOutputs src specName selfArgs child.outputs
      let checker : Procedure :=
        { name := { checkerName with source := src }
          typeArgs := allTypeArgs
          inputs := child.inputs
          outputs := child.outputs
          -- prove each Parent.post (renamed into child's names) as the checker's own post
          preconditions := []
          decreases := none
          isFunctional := false
          body := .Opaque (parentPosts.map (fun c => { c with condition := rename c.condition }))
                    (some ⟨ .Block [callStmt] none, src ⟩) parentModifies }
      [companion, checker]
  preChecker ++ postCheckers

/-- The pass: for every composite method that overrides an ancestor method, append
    the refinement checker procedures to `program.staticProcedures`. -/
def checkOverrideRefinement (model : SemanticModel) (program : Program) : Program :=
  let checkers : List Procedure :=
    program.types.foldl (init := []) fun acc td =>
      match td with
      | .Composite ct =>
        acc ++ ct.instanceProcedures.foldl (init := []) fun acc2 m =>
          -- SHARED GATE: emit a refinement checker for EXACTLY the methods that
          -- `LiftInstanceProcedures` will dispatch virtually (`isVirtualDispatchMethod`).
          -- This is the soundness invariant: every virtual method is Liskov-checked, so
          -- a dynamically-dispatched override can never have an unverified contract.
          -- Generic families are included (the checker carries the composite's type params
          -- so it monomorphizes per instantiation). Previously these two gates were
          -- expressed differently and DIVERGED: a method with an `.Applied`-typed parameter
          -- got a dispatcher but NO checker, so a Liskov-violating override was silently
          -- accepted. Driving both off one predicate closes that gap.
          if ! isVirtualDispatchMethod model program ct.name m.name.text then acc2
          else
            match findOverriddenParent model ct.name m.name with
            | some (_parentName, parentProc) => acc2 ++ refinementCheckers ct.name ct.typeArgs parentProc m
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
