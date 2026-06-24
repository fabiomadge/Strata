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

`modifies`-subset is intentionally NOT checked here yet: the modifies clause is
lowered to a quantified frame `ensures` downstream (`ModifiesClauses`), so a
frame-subset obligation belongs after that lowering; this pass covers the
pre/post refinement that is the load-bearing half. (See the plan for the frame
follow-up.)
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
  conjoinAnd src ((cs.filter (fun c => !c.free)).map (·.condition))

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
      -- Carry the child composite's type params (+ any method-level ones) so a checker
      -- over a GENERIC override (`self : C<T>`) is indexed as a poly proc by
      -- `MonomorphizeComposites.indexGenerics` and monomorphized per instantiation —
      -- mirrors how lifted methods carry `ct.typeArgs ++ proc.typeArgs`. Empty for a
      -- non-generic family ⇒ byte-identical to before.
      typeArgs := childTypeArgs ++ child.typeArgs
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
        (fun c => { c with condition := rename c.condition }))
      [mkChecker "pre" child.inputs assume (childPres.map (·.condition))]
  let postChecker : List Procedure :=
    if parentPosts.isEmpty then []  -- parent guarantees nothing ⇒ covariance trivially holds
    else
      -- params: inputs ++ outputs (post mentions both). assume Child.post, assert each Parent.post (renamed)
      let assume := conjoinConditions src childPosts
      [mkChecker "post" (child.inputs ++ child.outputs) assume
        (parentPosts.map (fun c => rename c.condition))]
  preChecker ++ postChecker

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
          -- a dynamically-dispatched override can never have an unverified contract. (The
          -- gate also excludes generic families, for which a checker's `self : C<T>` param
          -- can't be seeded by the monomorphizer — those keep static dispatch, no checker.)
          -- Previously these two gates were expressed differently and DIVERGED: a method
          -- with an `.Applied`-typed parameter got a dispatcher but NO checker, so a
          -- Liskov-violating override was silently accepted. Driving both off one predicate
          -- closes that gap.
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
