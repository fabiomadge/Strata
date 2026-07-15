/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.Util.TestDiagnostics
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
meta import StrataDDM.Util.IO
meta import Strata.Languages.Laurel.Grammar.LaurelGrammar
meta import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
meta import Strata.Languages.Laurel.LaurelCompilationPipeline
meta import all StrataTest.Util.LaurelCorpusHarness

/-!
# Dynamic dispatch + behavioral-subtyping (Liskov) corpus

The feature corpus for dynamic method dispatch and the behavioral-subtyping
(Liskov) check that makes it sound. Driven by the shared `Case`/`checkCase`
harness (`StrataTest.Util.LaurelCorpusHarness`), with must-fail twins pinning soundness.
-/

meta section

open StrataTest.Util
open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-! ## Dynamic dispatch + behavioral subtyping (Liskov)

Method dispatch is VIRTUAL: a call on a statically-`Parent`-typed receiver holding a
more-derived value runs the derived override (`LiftInstanceProcedures` generates a
runtime-tag dispatcher `Parent$m` over `Parent$m$impl`/`Child$m$impl`, with
tag-conditioned postconditions). This is sound because `CheckOverrideRefinement` (the
Liskov pass) rejects any override whose contract does not refine its parent's. GENERIC
inheriting families are included (the dispatcher/checker carry the composite's type
params and monomorphize per instantiation; see `generic_dispatch_*` below).
-/

def dynamicDispatchCorpus : List Case := [
  { name := "dispatch_parent_holds_child", outcome := .verifies,
    why := "`b: Parent := new Child; b#m()` runs Child's override (r==2) — dynamic dispatch through a static Parent reference"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 2 { r := 2 };
}
procedure u() opaque { var b: Parent := new Child; var r: int := b#m(); assert r == 2 };"},

  { name := "dispatch_parent_holds_child_wrong", outcome := .failsExactly 1,
    why := "the same call does NOT return the Parent value (1) — dispatch is dynamic, so asserting r==1 must FAIL"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 2 { r := 2 };
}
procedure u() opaque { var b: Parent := new Child; var r: int := b#m(); assert r == 1 };"},
  { name := "dispatch_modular_sound", outcome := .verifies,
    why := "`helper(b: Parent) ensures out>=0 { out := b#m() }` called with a Child verifies — the override (r==2) refines Parent's (r>=0), so the modular guarantee holds under dynamic dispatch"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 2 { r := 2 };
}
procedure helper(b: Parent) returns (out: int) opaque ensures out >= 0 { out := b#m() };
procedure u() opaque { var c: Child := new Child; var got: int := helper(c); assert got >= 0 };"},
  { name := "dispatch_three_level", outcome := .verifies,
    why := "3-level refining hierarchy (r>=0 ⊇ r>=1 ⊇ r>=2): GP-typed holding a C dispatches soundly, GP's contract r>=0 holds"
    src := r"
composite GP { var g: int
  procedure m(self: GP) returns (r: int) opaque ensures r >= 0 { r := 5 };
}
composite P extends GP {
  procedure m(self: P) returns (r: int) opaque ensures r >= 1 { r := 5 };
}
composite C extends P {
  procedure m(self: C) returns (r: int) opaque ensures r >= 2 { r := 5 };
}
procedure u() opaque { var x: GP := new C; var r: int := x#m(); assert r >= 0 };"},
  { name := "liskov_weaker_post_rejected", outcome := .failsExactly 1,
    why := "Child.m `ensures r == -5` does NOT refine Parent.m `ensures r >= 0` — the override-refinement (Liskov) check FAILS"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == -5 { r := -5 };
}
procedure u() opaque { assert 1 == 1 };"},
  { name := "liskov_stronger_pre_rejected", outcome := .failsExactly 2,
    why := "Child.m `requires a >= 5` is STRONGER than Parent.m `requires a >= 0` — contravariance FAILS (the pre-refinement checker fails; a 2nd VC from the dispatcher path also surfaces — both reject)"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent, a: int) returns (r: int) requires a >= 0 opaque ensures true { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child, a: int) returns (r: int) requires a >= 5 opaque ensures true { r := 1 };
}
procedure u() opaque { assert 1 == 1 };"},
  { name := "liskov_sound_override", outcome := .verifies,
    why := "Child.m `ensures r == 2` refines Parent.m `ensures r >= 0` (2>=0) — the override-refinement check passes"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent, a: int) returns (r: int) requires a >= 5 opaque ensures r >= 0 { r := 2 };
}
composite Child extends Parent {
  procedure m(self: Child, a: int) returns (r: int) requires a >= 0 opaque ensures r == 2 { r := 2 };
}
procedure u() opaque { assert 1 == 1 };"},
  -- POST-COVARIANCE UNDER THE PARENT PRECONDITION: Child.m `ensures r == a` refines
  -- Parent.m `ensures r >= 0` ONLY when `a >= 0` (the parent's `requires`). The post-checker
  -- must ASSUME Parent.pre — else this sound override is spuriously over-rejected.
  { name := "liskov_post_covariance_under_parent_pre", outcome := .verifies,
    why := "`Child.post (r==a)` implies `Parent.post (r>=0)` under `Parent.pre (a>=0)`; the post-checker assumes Parent.pre so the sound override verifies"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent, a: int) returns (r: int) requires a >= 0 opaque ensures r >= 0 { r := a };
}
composite Child extends Parent {
  procedure m(self: Child, a: int) returns (r: int) requires a >= 0 opaque ensures r == a { r := a };
}
procedure u() opaque { assert 1 == 1 };"},

  { name := "liskov_post_covariance_violation_under_pre", outcome := .failsExactly 1,
    why := "even WITH `Parent.pre (a>=0)` assumed, `Child.post (r==a-100)` can be negative, so it does NOT refine `Parent.post (r>=0)` — must still be REJECTED (the Parent.pre assumption must not weaken the checker into accepting real violations)"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent, a: int) returns (r: int) requires a >= 0 opaque ensures r >= 0 { r := a };
}
composite Child extends Parent {
  procedure m(self: Child, a: int) returns (r: int) requires a >= 0 opaque ensures r == a - 100 { r := a - 100 };
}
procedure u() opaque { assert 1 == 1 };"},
  { name := "dispatch_three_level_false", outcome := .failsExactly 1,
    why := "a false assertion (r>=100) on a dynamically-dispatched 3-level call must FAIL — dispatch is sound, not vacuous"
    src := r"
composite GP { var g: int
  procedure m(self: GP) returns (r: int) opaque ensures r >= 0 { r := 5 };
}
composite P extends GP {
  procedure m(self: P) returns (r: int) opaque ensures r >= 1 { r := 5 };
}
composite C extends P {
  procedure m(self: C) returns (r: int) opaque ensures r >= 2 { r := 5 };
}
procedure u() opaque { var x: GP := new C; var r: int := x#m(); assert r >= 100 };"},
  -- GATE-CONSISTENCY (regression for the unified dispatch/checker gate): a method with
  -- an `.Applied`-typed parameter (`b: Box<int>`) is still dispatched virtually, so it
  -- MUST be Liskov-checked. Before the gate was unified, the checker keyed on parameter
  -- types and skipped on `.Applied`, while the dispatcher keyed on composite type params
  -- and did NOT — so this violating override (r==-1 vs r>=0) was silently ACCEPTED. Both
  -- passes now gate on the single `isVirtualDispatchMethod`, so it is REJECTED.
  { name := "liskov_applied_param_violation_caught", outcome := .failsExactly 1,
    why := "a Liskov-violating override on a method with an `.Applied` (`Box<int>`) parameter is caught — the dispatch gate and the refinement-checker gate are unified (regression for the gate-divergence soundness fix)"
    src := r"
composite Box<T> { var val: T }
composite Parent { var x: int
  procedure m(self: Parent, b: Box<int>) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child, b: Box<int>) returns (r: int) opaque ensures r == 0 - 1 { r := 0 - 1 };
}
procedure u() opaque { assert 1 == 1 };"},

  { name := "liskov_applied_param_sound_ok", outcome := .verifies,
    why := "a SOUND override on an `.Applied`-param method still verifies (the unified gate does not over-reject)"
    src := r"
composite Box<T> { var val: T }
composite Parent { var x: int
  procedure m(self: Parent, b: Box<int>) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child, b: Box<int>) returns (r: int) opaque ensures r == 2 { r := 2 };
}
procedure u() opaque { assert 1 == 1 };"},
  -- GENERIC dynamic dispatch: a method on a GENERIC composite, overridden by a generic
  -- subtype, dispatches virtually. The dispatcher's is/as tag-tests use the applied
  -- form (`self is SBox<int>`) and the Liskov checker carries the composite's type
  -- params so it monomorphizes per instantiation.
  { name := "generic_dispatch_runtime_override", outcome := .verifies,
    why := "`b: Box<int> := new SBox<int>; b#get()` runs SBox's override (r==7) through a generic Box<int> reference — dynamic dispatch over a generic family"
    src := r"
composite Box<T> { var val: T
  procedure get(self: Box<T>) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
composite SBox<T> extends Box<T> {
  procedure get(self: SBox<T>) returns (r: int) opaque ensures r == 7 { r := 7 };
}
procedure u() opaque { var b: Box<int> := new SBox<int>; var r: int := b#get(); assert r == 7 };"},

  { name := "generic_dispatch_runtime_override_wrong", outcome := .failsExactly 1,
    why := "the generic dynamic call does NOT return the parent value (0) — dispatch is dynamic"
    src := r"
composite Box<T> { var val: T
  procedure get(self: Box<T>) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
composite SBox<T> extends Box<T> {
  procedure get(self: SBox<T>) returns (r: int) opaque ensures r == 7 { r := 7 };
}
procedure u() opaque { var b: Box<int> := new SBox<int>; var r: int := b#get(); assert r == 0 };"},

  { name := "generic_liskov_violation_caught", outcome := .failsExactly 1,
    why := "a Liskov-violating override on a GENERIC family (SBox.get `ensures r == -5` not refining Box.get `ensures r >= 0`) is now caught — generic Liskov checking works"
    src := r"
composite Box<T> { var val: T
  procedure get(self: Box<T>) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
composite SBox<T> extends Box<T> {
  procedure get(self: SBox<T>) returns (r: int) opaque ensures r == 0 - 5 { r := 0 - 5 };
}
procedure u() opaque { assert 1 == 1 };"},

  { name := "generic_dispatch_multi_instantiation", outcome := .verifies,
    why := "the same generic virtual method dispatched at TWO instantiations (Box<int> and Box<bool> holding SBox) — distinct monomorphs, both dispatch correctly"
    src := r"
composite Box<T> { var val: T
  procedure get(self: Box<T>) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
composite SBox<T> extends Box<T> {
  procedure get(self: SBox<T>) returns (r: int) opaque ensures r == 7 { r := 7 };
}
procedure u() opaque { var bi: Box<int> := new SBox<int>; var ri: int := bi#get(); var bb: Box<bool> := new SBox<bool>; var rb: int := bb#get(); assert ri == 7 && rb == 7 };"},
  -- VOID heap-MUTATING method, dispatched. For a void method that is BOTH overridden AND a
  -- heap-writer (`modifies`), the dispatcher's `then` branch is a block, so the `else`
  -- fallthrough must be block-wrapped too — otherwise the two branches synthesize
  -- different types for the `$heap`-threaded void call ("'if' branches have incompatible
  -- types 'Heap' and 'void'"). Block-wrapping the fallthrough keeps the branches symmetric.
  { name := "void_heapwriter_dispatch_translates", outcome := .verifies,
    why := "a void heap-mutating method that is overridden + dispatched translates + verifies (dispatcher fallthrough block-wrapped for branch-type symmetry)"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures c#v == 1 modifies c { c#v := 1 };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures c#v == 1 modifies c { c#v := 1 };
}
procedure u() opaque { var b: Parent := new Child; var cc: Cell := new Cell; b#m(cc); assert cc#v == 1 };"},

  { name := "void_heapwriter_dispatch_wrong", outcome := .failsExactly 1,
    why := "the void heap-writer dispatch conveys the override's postcondition (c#v == 1), so a false read (c#v == 2) must FAIL"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures c#v == 1 modifies c { c#v := 1 };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures c#v == 1 modifies c { c#v := 1 };
}
procedure u() opaque { var b: Parent := new Child; var cc: Cell := new Cell; b#m(cc); assert cc#v == 2 };"},
  -- MIXED modifies-status across a dispatched family: parent method heap-NEUTRAL (no
  -- modifies), override heap-WRITING (modifies c). The dispatcher's `if` then joined a
  -- $heap-threaded branch (Heap) with a void branch and failed to translate. Fixed by
  -- `unifyDispatchFamilyHeap`: a dispatch family's $impl procs share heap-status, so both
  -- branches thread $heap uniformly. The parent here ALSO declares `modifies c` (so the
  -- override does not WIDEN the frame — a frame-widening override is correctly rejected as
  -- a Liskov modifies-violation, covered by mixed_modifies_frame_widen_rejected below).
  { name := "mixed_modifies_dispatch_translates", outcome := .verifies,
    why := "a dispatched family where the parent method has an empty body but declares `modifies c` and the override mutates c — mixed heap-touching shape — now translates + the override's post is conveyed through the upcast"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures true modifies c { };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures c#v == 1 modifies c { c#v := 1 };
}
procedure u() opaque { var b: Parent := new Child; var cc: Cell := new Cell; b#m(cc); assert cc#v == 1 };"},

  { name := "mixed_modifies_frame_widen_rejected", outcome := .failsExactly 2,
    why := "an override that WIDENS the modifies frame (parent modifies nothing, child modifies c) is a Liskov frame-violation, now caught TWICE: (1) the dispatcher call-site cannot prove the parent's (empty) frame when the override mutates c, and (2) the two-state-faithful post-checker (CheckOverrideRefinement) independently rejects it at definition time — its parent-frame `ensures` over the child-spec-havoc'd heap cannot prove `c` unchanged. Both are correct rejections of the same violation"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures true { };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures c#v == 1 modifies c { c#v := 1 };
}
procedure u() opaque { var b: Parent := new Child; var cc: Cell := new Cell; b#m(cc); assert 1 == 1 };"},
  -- TWO-STATE (`old(...)`) Liskov refinement. The post-checker is two-state-faithful: it
  -- calls a heap-writer `$childspec` companion so it gains an inout `$heap` and `old()`
  -- survives `PushOldInward`. Without that, `old(c#v)` would collapse to the current heap
  -- and any two-state override contract would be checked VACUOUSLY. These pin that a
  -- violating two-state override is REJECTED and a sound one still VERIFIES. (Definition-only
  -- — `u` just asserts 1==1 — so the outcome is the static checker's, in isolation.)
  { name := "old_liskov_weaker_post_rejected", outcome := .failsExactly 1,
    why := "Child.m `ensures c#v == old(c#v) - 1` (decrements) does NOT refine Parent.m `ensures c#v >= old(c#v)` (non-decreasing) — the two-state post-checker rejects it"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures c#v >= old(c#v) modifies c { c#v := c#v + 1 };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures c#v == old(c#v) - 1 modifies c { c#v := c#v - 1 };
}
procedure u() opaque { assert 1 == 1 };"},

  { name := "old_liskov_sound_override_ok", outcome := .verifies,
    why := "Child.m `ensures c#v == old(c#v) + 2` refines Parent.m `ensures c#v >= old(c#v)` (a +2 increase satisfies non-decreasing) — the two-state post-checker accepts it (no over-rejection)"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures c#v >= old(c#v) modifies c { c#v := c#v + 1 };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures c#v == old(c#v) + 2 modifies c { c#v := c#v + 2 };
}
procedure u() opaque { assert 1 == 1 };"},

  { name := "old_liskov_nested_old_rejected", outcome := .failsExactly 1,
    why := "nested `old(old(c#v))` (idempotent with `old(c#v)`): Child decrements, Parent requires non-decrease — still rejected, so the two-state machinery handles nested old correctly"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures c#v >= old(old(c#v)) modifies c { c#v := c#v + 1 };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures c#v == old(c#v) - 1 modifies c { c#v := c#v - 1 };
}
procedure u() opaque { assert 1 == 1 };"},

  { name := "old_liskov_generic_family_rejected", outcome := .failsExactly 1,
    why := "a two-state Liskov violation on a GENERIC family (the post-checker + its `$childspec` companion carry the composite's type params and monomorphize per instantiation) is rejected"
    src := r"
composite Cell { var v: int }
composite Box<T> { var b: T
  procedure m(self: Box<T>, c: Cell) opaque ensures c#v >= old(c#v) modifies c { c#v := c#v + 1 };
}
composite SBox<T> extends Box<T> {
  procedure m(self: SBox<T>, c: Cell) opaque ensures c#v == old(c#v) - 1 modifies c { c#v := c#v - 1 };
}
procedure u() opaque { var b: Box<int> := new SBox<int>; assert 1 == 1 };"},
  -- SIBLING / non-linear hierarchy: two incomparable children both override m — equal-distance
  -- siblings, exercising the name-tiebreaker path that makes sibling dispatch order deterministic.
  -- (Branch order is irrelevant to correctness here: dispatch is by runtime tag, and a value `is`
  -- exactly one sibling's type.) A Parent-typed var holding Child2 must run Child2.m.
  { name := "dispatch_sibling_holds_child2", outcome := .verifies,
    why := "Parent with two incomparable overriders C1/C2; a Parent-typed var holding a C2 dispatches to C2.m (r==3) by runtime tag — exercises equal-distance-sibling dispatch"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child1 extends Parent {
  procedure m(self: Child1) returns (r: int) opaque ensures r == 2 { r := 2 };
}
composite Child2 extends Parent {
  procedure m(self: Child2) returns (r: int) opaque ensures r == 3 { r := 3 };
}
procedure u() opaque { var b: Parent := new Child2; var r: int := b#m(); assert r == 3 };"},

  { name := "dispatch_sibling_holds_child2_wrong", outcome := .failsExactly 1,
    why := "holding a C2 does NOT run C1's override — asserting C1's value (r==2) must FAIL (dispatch picks the runtime tag, not an arbitrary sibling)"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child1 extends Parent {
  procedure m(self: Child1) returns (r: int) opaque ensures r == 2 { r := 2 };
}
composite Child2 extends Parent {
  procedure m(self: Child2) returns (r: int) opaque ensures r == 3 { r := 3 };
}
procedure u() opaque { var b: Parent := new Child2; var r: int := b#m(); assert r == 2 };"},
  -- MULTI-OUTPUT dispatched method (returns two values): a distinct dispatcher path
  -- (`.Assign` over a list of output targets) and tag-conditioned posts over both outputs.
  { name := "dispatch_multi_output", outcome := .verifies,
    why := "an overridden method returning (a, b) dispatches with both outputs recovered through the static Parent reference (a==5)"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (a: int, b: int) opaque ensures a >= 0 { a := 1; b := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (a: int, b: int) opaque ensures a == 5 { a := 5; b := 6 };
}
procedure u() opaque { var o: Parent := new Child; assign var p: int, var q: int := o#m(); assert p == 5 };"},

  { name := "dispatch_multi_output_wrong", outcome := .failsExactly 1,
    why := "the multi-output dispatch returns the override's first value (5), not the parent's (1) — asserting the parent value must FAIL"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (a: int, b: int) opaque ensures a >= 0 { a := 1; b := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (a: int, b: int) opaque ensures a == 5 { a := 5; b := 6 };
}
procedure u() opaque { var o: Parent := new Child; assign var p: int, var q: int := o#m(); assert p == 1 };"},
  -- MULTI-ARG method whose ARGUMENT participates in the post: pins `restArgs` threading
  -- (self + 2 args forwarded in order) and positional Liskov param alignment over 3 inputs.
  { name := "dispatch_multiarg_in_post", outcome := .verifies,
    why := "`o#m(3, 4)` on an override `ensures r == a + b` dispatches with args forwarded in order (r==7); Parent.post is `true` so the override refines it"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent, a: int, b: int) returns (r: int) opaque ensures true { r := 0 };
}
composite Child extends Parent {
  procedure m(self: Child, a: int, b: int) returns (r: int) opaque ensures r == a + b { r := a + b };
}
procedure u() opaque { var o: Parent := new Child; var r: int := o#m(3, 4); assert r == 7 };"},
  { name := "dispatch_through_field", outcome := .verifies,
    why := "a composite field `h#p : Parent` holding a Child dispatches to Child.m on `h#p#m()` (r==2)"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 2 { r := 2 };
}
composite Holder { var p: Parent }
procedure u() opaque { var h: Holder := new Holder; h#p := new Child; var r: int := h#p#m(); assert r == 2 };"},
  -- TRANSITIVE dispatch: the overridden method is called from inside ANOTHER procedure's body
  -- (not the top-level test), so the call-site rewrite routes through the dispatcher as a
  -- non-top-level callee whose tag-conditioned posts the surrounding proof must consume.
  { name := "dispatch_transitive_call", outcome := .verifies,
    why := "`indirect(p: Parent) { r := p#m() }` called with a Child dispatches virtually inside the helper body; the helper's `ensures r >= 0` holds via the override's refined post"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 2 { r := 2 };
}
procedure indirect(p: Parent) returns (r: int) opaque ensures r >= 0 { r := p#m() };
procedure u() opaque { var b: Parent := new Child; var r: int := indirect(b); assert r >= 0 };"},
  -- NON-OVERRIDDEN + OVERRIDDEN method coexisting in one family: `m` is overridden (gets a
  -- dispatcher + Liskov checker), `n` is not (takes the plain-lift path, no dispatcher). Both
  -- callable through a Parent-typed reference holding a Child.
  { name := "dispatch_overridden_and_non_overridden", outcome := .verifies,
    why := "in one family `m` is overridden (virtual) and `n` is not; through a Parent var holding a Child, `m` runs the override (rm==2) and `n` runs Parent's `n` (rn==9) — method-granular dispatch gate"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
  procedure n(self: Parent) returns (r: int) opaque ensures r == 9 { r := 9 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 2 { r := 2 };
}
procedure u() opaque { var b: Parent := new Child; var rm: int := b#m(); var rn: int := b#n(); assert rm == 2 && rn == 9 };"},
  { name := "dispatch_reader_only", outcome := .verifies,
    why := "an overridden method that reads `self#x` into a local but writes nothing dispatches + verifies (heap-reader, not writer)"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r == 0 { var t: int := self#x; r := 0 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 0 { var t: int := self#x; r := 0 };
}
procedure u() opaque { var c: Child := new Child; var b: Parent := c; var r: int := b#m(); assert r == 0 };"},
  -- The complement of `mixed_modifies_dispatch_translates` above (writer parent, neutral override).
  { name := "dispatch_reverse_mixed_modifies", outcome := .verifies,
    why := "parent `modifies c` (writer), override empty body + no modifies (neutral, narrows the frame) — `unifyDispatchFamilyHeap` makes the family thread $heap uniformly so it translates + verifies"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures true modifies c { c#v := 1 };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures true { };
}
procedure u() opaque { var b: Parent := new Child; var cc: Cell := new Cell; b#m(cc); assert 1 == 1 };"} ]

def runDynamicDispatchTest : IO Unit := checkCases dynamicDispatchCorpus

#guard_msgs (drop info, error) in
#eval runDynamicDispatchTest
end Strata.Laurel
