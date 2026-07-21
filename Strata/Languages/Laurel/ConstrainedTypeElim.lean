/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Util.Tactics

/-!
# Constrained Type Elimination

A Laurel-to-Laurel pass that eliminates constrained types by:
1. Generating a constraint function per constrained type (e.g. `nat$constraint(x: int): bool`)
2. Adding `requires constraintFunc(param)` for constrained-typed inputs
3. Adding `ensures constraintFunc(result)` for constrained-typed outputs
   - Skipped for `isFunctional` procedures since the Laurel translator does not yet support
     function postconditions. Constrained return types on functions are not checked.
4. Inserting `assert constraintFunc(var)` for local variable init and reassignment
5. Assuming the constraint for uninitialized constrained-typed variables (havoc + assume)
6. Adding a synthetic witness-validation procedure per constrained type
7. Injecting constraint function calls into quantifier bodies (`forall` → `implies`, `exists` → `and`)
8. Resolving all constrained type references to their base types
-/

namespace Strata.Laurel

open Strata

abbrev ConstrainedTypeMap := Std.HashMap String ConstrainedType

def buildConstrainedTypeMap (types : List TypeDefinition) : ConstrainedTypeMap :=
  types.foldl (init := {}) fun m td =>
    match td with | .Constrained ct => m.insert ct.name.text ct | _ => m

partial def resolveBaseType (ptMap : ConstrainedTypeMap) (ty : HighType) : HighType :=
  match ty with
  | .UserDefined name => match ptMap.get? name.text with
    | some ct => resolveBaseType ptMap ct.base.val | none => ty
  | .Applied ctor args =>
    .Applied ctor (args.map fun a => ⟨resolveBaseType ptMap a.val, a.source⟩)
  | _ => ty

def resolveType (ptMap : ConstrainedTypeMap) (ty : HighTypeMd) : HighTypeMd :=
  ⟨resolveBaseType ptMap ty.val, ty.source⟩

def isConstrainedType (ptMap : ConstrainedTypeMap) (ty : HighType) : Bool :=
  match ty with | .UserDefined name => ptMap.contains name.text | _ => false

/-- Does `ty` name a composite type (peeling `.Applied`/`.UserDefined` to a base
    name and consulting the model)? Only composites should reach the
    HeapParameterization / TypeHierarchy `is`/`as` lowering; every other kind is
    eliminated here in `resolveExprNode`. -/
def isCompositeTarget (model : SemanticModel) (ty : HighType) : Bool :=
  match highBaseName? ty with
  | some name => match model.get name with
    | .compositeType _ => true
    | _ => false
  | none => false

/-- Build a call to the constraint function for a constrained type, asserting
    the constraint on the read-back expression `ref`. Returns `none` if `ty` is
    not a constrained type.

    `ref` is the expression whose value is checked (e.g. a local read
    `x` or a field read `c#count`), allowing this to serve every assignment
    target kind uniformly. -/
def constraintCallForExpr (ptMap : ConstrainedTypeMap) (ty : HighType)
    (ref : StmtExprMd) (src : Option FileRange := none) : Option StmtExprMd :=
  match ty with
  | .UserDefined name => if ptMap.contains name.text then
      some ⟨.StaticCall (mkId s!"{name.text}$constraint") [ref], src⟩
    else none
  | _ => none

/-- Build a call to the constraint function for a constrained type, checking a
    local variable read, or `none` if not constrained. -/
def constraintCallFor (ptMap : ConstrainedTypeMap) (ty : HighType)
    (varName : Identifier) (src : Option FileRange := none) : Option StmtExprMd :=
  constraintCallForExpr ptMap ty ⟨.Var (.Local varName), src⟩ src

/-- Generate a constraint function for a constrained type.
    For nested types, the function calls the parent's constraint function. -/
def mkConstraintFunc (ptMap : ConstrainedTypeMap) (ct : ConstrainedType) : Procedure :=
  let baseType := resolveType ptMap ct.base
  let bodyExpr: StmtExprMd := match ct.base.val with
    | .UserDefined parent =>
      if ptMap.contains parent.text then
        let paramId := { ct.valueName with uniqueId := none }
        let paramRef : StmtExprMd :=
          { val := .Var (.Local paramId), source := none }
        let parentCall : StmtExprMd :=
          { val := .StaticCall (mkId s!"{parent.text}$constraint") [paramRef], source := none }
        { val := .PrimitiveOp .And [ct.constraint, parentCall], source := none }
      else ct.constraint
    | _ => ct.constraint
  { name := mkId s!"{ct.name.text}$constraint"
    inputs := [{ name := ct.valueName, type := baseType }]
    outputs := [{ name := mkId "result", type := { val := .TBool, source := none } }]
    body := .Transparent { val := .Return bodyExpr, source := none }
    isFunctional := true
    decreases := none
    preconditions := [] }

/-- Generate the downcast helper for a constrained type `T` (base `B`):
    `function downcast$T(p: B): B requires T$constraint(p) { p }`.
    Emitted alongside the `T$constraint` predicate. The `x as T` arm of
    `resolveExprNode` rewrites to a call to this helper. A call is a pure term
    (works in a contract position), and its precondition is discharged by
    PrecondElim as a well-definedness obligation — exactly like the composite
    `downcast$C` helper synthesized by TypeHierarchy. -/
def mkConstraintDowncastFunc (ptMap : ConstrainedTypeMap) (ct : ConstrainedType) : Procedure :=
  let baseType := resolveType ptMap ct.base
  let pRef : StmtExprMd := ⟨.Var (.Local "p"), none⟩
  let pre : StmtExprMd := ⟨.StaticCall (mkId s!"{ct.name.text}$constraint") [pRef], none⟩
  { name := downcastProcName ct.name
    inputs := [{ name := "p", type := baseType }]
    outputs := [{ name := mkId "r", type := baseType }]
    preconditions := [{ condition := pre }]
    -- Wrap the returned value in `.Return` (as `mkConstraintFunc` does): this
    -- helper is emitted at pipeline pos 121, so it must flow through the
    -- return-handling passes (mergeAndLiftReturns, eliminateValueInReturns);
    -- a bare `.Transparent pRef` is rejected ("transparent body ending with a
    -- Var statement"). The composite `downcast$C` helper can use a bare body
    -- only because TypeHierarchy synthesizes it AFTER those passes.
    body := .Transparent ⟨.Return (some pRef), none⟩
    isFunctional := true
    decreases := none }

def resolveVariable (ptMap : ConstrainedTypeMap) (v : VariableMd) : VariableMd :=
  match v.val with
  | .Declare param => ⟨.Declare { param with type := resolveType ptMap param.type }, v.source⟩
  | _ => v

/-- Resolve constrained types in type positions, inject constraint calls into
    quantifier bodies, and FULLY eliminate `is`/`as` for every NON-composite
    target type. This is the single, consolidated home for non-composite
    `is`/`as` lowering — composites are left untouched here and flow to
    HeapParameterization / TypeHierarchy exactly as before.

    - Constrained target `T`:
      - `x is T` → `T$constraint(x)` (the generated constraint predicate).
      - `x as T` → `downcast$T(x)`, a call to a generated helper
        `function downcast$T(p: base): base requires T$constraint(p) { p }`.
        A call is a pure term, so — unlike an `{ assert …; x }` block — it works
        in a CONTRACT position; its precondition is discharged by PrecondElim as
        a well-definedness obligation (mirroring the composite `downcast$C` path).
    - Other non-composite target (primitive / alias-to-primitive / datatype):
      Resolution has already enforced the lineage check (same-or-subtype), so
      nothing remains to check at runtime — `x is T` → `true`, `x as T` → `x`.
    - Composite target: leave the `.AsType`/`.IsType` node in place (only its
      type is normalized via `resolveType`, an identity on composites) so
      HeapParameterization / TypeHierarchy lower it as today.

    Recursion into StmtExprMd children is handled by `mapStmtExpr`. -/
def resolveExprNode (ptMap : ConstrainedTypeMap) (model : SemanticModel) (expr : StmtExprMd) : StmtExprMd :=
  let source := expr.source

  match expr.val with
  | .Assign targets value =>
    ⟨.Assign (targets.map (resolveVariable ptMap)) value, source⟩
  | .Var (.Declare param) =>
    ⟨.Var (.Declare { param with type := resolveType ptMap param.type }), source⟩
  | .Quantifier mode param trigger body =>
    let param' := { param with type := resolveType ptMap param.type }
    -- With bottom-up traversal, `body` is already recursed into. The newly
    -- created `PrimitiveOp` won't be visited again, which is safe because
    -- `c` (from `constraintCallFor`) is a StaticCall with Identifier leaves
    -- that don't need further resolution.
    let combiner := match mode with | .Forall => Operation.Implies | .Exists => Operation.And
    let injected := match constraintCallFor ptMap param.type.val param.name (src := source) with
      | some c => ⟨.PrimitiveOp combiner [c, body], source⟩
      | none => body
    ⟨.Quantifier mode param' trigger injected, source⟩
  | .AsType t ty =>
    match ty.val with
    | .UserDefined name =>
      match ptMap.get? name.text with
      | some _ => ⟨.StaticCall (downcastProcName name) [t], source⟩  -- constrained: helper call
      | none =>
        if isCompositeTarget model ty.val then ⟨.AsType t ty, source⟩  -- composite: leave for HeapParam
        else t  -- datatype / non-constrained non-composite: identity
    | _ =>
      if isCompositeTarget model ty.val then ⟨.AsType t (resolveType ptMap ty), source⟩
      else t  -- primitive / alias-to-primitive: identity
  | .IsType t ty =>
    match ty.val with
    | .UserDefined name =>
      match ptMap.get? name.text with
      | some _ => ⟨.StaticCall (mkId s!"{name.text}$constraint") [t], source⟩  -- constrained predicate
      | none =>
        if isCompositeTarget model ty.val then ⟨.IsType t ty, source⟩  -- composite: leave for TypeHierarchy
        else ⟨.LiteralBool true, source⟩  -- datatype / non-composite: lineage already checked
    | _ =>
      if isCompositeTarget model ty.val then ⟨.IsType t (resolveType ptMap ty), source⟩
      else ⟨.LiteralBool true, source⟩  -- primitive / alias-to-primitive: lineage already checked
  | _ => expr

/-- Per-node constrained-type elimination, applied bottom-up (with flattening)
    by `mapStmtExprFlattenM`. `resultUsed` is `true` when the node occupies a
    value position.

    - Uninitialized constrained declaration `var x: T;` → assume its constraint.
    - Assignment to constrained target(s) → emit the assignment followed by an
      `assert T$constraint(<read-back>)` per constrained target. The constraint
      is checked on a *read-back* of the target rather than on the RHS, so the
      RHS is evaluated exactly once. In value position the read-back is also
      appended as the final statement, so the resulting value-block evaluates to
      the assigned value (this covers expression-position assignments such as
      `y := (x := -1) + 1`); in statement position it is omitted.
    - All other nodes are returned unchanged; the traversal handles recursion. -/
def elimNode (ptMap : ConstrainedTypeMap) (model : SemanticModel)
    (resultUsed : Bool) (node : StmtExprMd) : List StmtExprMd :=
  let source := node.source
  match node.val with
  | .Var (.Declare param) =>
    let check := (constraintCallFor ptMap param.type.val param.name (src := source)).toList.map
      fun c => ⟨.Assume c, source⟩
    [node] ++ check
  | .Assign targets _value =>
    let asserts: List StmtExprMd := targets.filterMap (fun target =>
      let ref : StmtExprMd := VariableMd.toReadbackExpr target
      let ty : HighType := (computeExprType model ref).val
      (constraintCallForExpr ptMap ty ref (src := source)).map (⟨.Assert { condition := · }, source⟩))
    let suffix := match targets with
      | [single] => if resultUsed then [VariableMd.toReadbackExpr single] else []
      | _ => []
    [node] ++ asserts ++ suffix
  | _ => [node]

/-- Apply `elimNode` across a body via the flattening, `resultUsed`-aware
    traversal. A procedure body is a statement, so the top-level `resultUsed`
    is `false`. -/
def elimStmts (ptMap : ConstrainedTypeMap) (model : SemanticModel) (body : StmtExprMd) : StmtExprMd :=
  mapStmtExprFlattenM (m := Id) (fun _ _ => none) (elimNode ptMap model) false body

def elimProc (ptMap : ConstrainedTypeMap) (model : SemanticModel) (proc : Procedure) : Procedure :=
  let inputRequires : List Condition := proc.inputs.filterMap fun p =>
    (constraintCallFor ptMap p.type.val p.name (src := p.type.source)).map
      fun c => { condition := c }
  let outputEnsures : List Condition := if proc.isFunctional then [] else proc.outputs.filterMap fun p =>
    (constraintCallFor ptMap p.type.val p.name (src := p.type.source)).map
      fun c => { condition := ⟨c.val, p.type.source⟩ }
  let body' := match proc.body with
  | .Transparent bodyExpr =>
    let body := elimStmts ptMap model bodyExpr
    if outputEnsures.isEmpty then .Transparent body
    else
      let retBody := if proc.isFunctional then ⟨.Return (some body), bodyExpr.source⟩ else body
      .Opaque outputEnsures (some retBody) []
  | .Opaque postconds impl modif =>
    let impl' := impl.map (elimStmts ptMap model)
    .Opaque (postconds ++ outputEnsures) impl' modif
  | .Abstract postconds => .Abstract (postconds ++ outputEnsures)
  | .External => .External
  let resolve := mapStmtExpr (resolveExprNode ptMap model)
  let resolveBody : Body → Body := fun body => match body with
    | .Transparent b => .Transparent (resolve b)
    | .Opaque ps impl modif => .Opaque (ps.map (·.mapCondition resolve)) (impl.map resolve) (modif.map resolve)
    | .Abstract ps => .Abstract (ps.map (·.mapCondition resolve))
    | .External => .External
  { proc with
    body := resolveBody body'
    inputs := proc.inputs.map fun p => { p with type := resolveType ptMap p.type }
    outputs := proc.outputs.map fun p => { p with type := resolveType ptMap p.type }
    preconditions := (proc.preconditions ++ inputRequires).map (·.mapCondition resolve) }

private def mkWitnessProc (ptMap : ConstrainedTypeMap) (ct : ConstrainedType) : Procedure :=
  let src := ct.witness.source

  let witnessId : Identifier := mkId "$witness"
  let witnessInit : StmtExprMd :=
    ⟨.Assign [⟨.Declare ⟨witnessId, resolveType ptMap ct.base⟩, src⟩] ct.witness, src⟩
  let assert : StmtExprMd :=
    ⟨.Assert { condition := (constraintCallFor ptMap (.UserDefined ct.name) witnessId (src := src)).get! }, src⟩
  { name := mkId s!"$witness_{ct.name.text}"
    inputs := []
    outputs := []
    body := .Opaque [] (some ⟨.Block [witnessInit, assert] none, src⟩) []
    preconditions := []
    isFunctional := false
    decreases := none }

/-- Eliminate constrained types within a composite type definition: resolve
    constrained field types to their base types and run constrained type
    elimination on the composite's instance procedures.

    This is necessary because `constrainedTypeElim` removes the constrained type
    definitions from the program. Any reference to a constrained type left inside
    a composite (e.g. a `count: nat` field) would otherwise dangle and fail to
    resolve in later passes and the final Core translation. -/
def elimCompositeType (ptMap : ConstrainedTypeMap) (model : SemanticModel) (ct : CompositeType) : CompositeType :=
  { ct with
    fields := ct.fields.map fun f => { f with type := resolveType ptMap f.type }
    instanceProcedures := ct.instanceProcedures.map (elimProc ptMap model) }

/-- Collect the `downcast$…` helper names actually called in `proc` (body + all
    contract positions). At this pipeline position `resolveExprNode` is the ONLY
    source of `downcast$`-prefixed calls (a `x as Composite` is still an `.AsType`
    node — its `downcast$C` is minted later by `TypeHierarchy`), so a `downcast$`
    prefix here means exactly a constrained `x as T` this pass just emitted. -/
private def collectDowncastCalls (acc : Std.HashSet String) (proc : Procedure) : Std.HashSet String :=
  let collect (e : StmtExprMd) : StateM (Std.HashSet String) StmtExprMd :=
    mapStmtExprM (fun n => do
      match n.val with
      | .StaticCall callee _ =>
          if callee.text.startsWith "downcast$" then modify (·.insert callee.text)
      | _ => pure ()
      pure n) e
  let scanBody : Body → StateM (Std.HashSet String) Unit := fun body => do
    match body with
    | .Transparent b => let _ ← collect b; pure ()
    | .Opaque ps impl modif =>
        for c in ps do let _ ← collect c.condition
        for e in impl.toList do let _ ← collect e
        for e in modif do let _ ← collect e
    | .Abstract ps => for c in ps do let _ ← collect c.condition
    | .External => pure ()
  (Id.run do
    let prog : StateM (Std.HashSet String) Unit := do
      scanBody proc.body
      for c in proc.preconditions do let _ ← collect c.condition
    pure ((prog.run acc).2))

public def constrainedTypeElim (model : SemanticModel) (program : Program)
    : Program × List DiagnosticModel :=
  let ptMap := buildConstrainedTypeMap program.types
  -- NOTE: we no longer early-return when there are no constrained types. This
  -- pass is the single home for eliminating `is`/`as` against every
  -- NON-composite target (primitive, alias, datatype), which must happen even in
  -- programs with zero constrained types. When `ptMap` is empty, all the
  -- constraint-type machinery below (constraint predicates, witnesses,
  -- requires/ensures injection, base-type resolution) is trivially empty/identity,
  -- and the only effective transform is the `is`/`as` rewrite in `resolveExprNode`.
  let constraintFuncs := program.types.filterMap fun
    | .Constrained ct => some (mkConstraintFunc ptMap ct) | _ => none
  -- Eliminate first, so we know which `downcast$T` helpers are actually called.
  let elimStatic := program.staticProcedures.map (elimProc ptMap model)
  -- A `downcast$T` helper per constrained type makes `x as T` a pure call (usable
  -- in a contract), matching the composite `downcast$C` path — but emit one ONLY
  -- when it is actually called, so a constrained type with no `as`-cast does not
  -- leave a dead helper definition all the way through to Core.
  let usedDowncasts := elimStatic.foldl collectDowncastCalls {}
  let constraintDowncasts := program.types.filterMap fun
    | .Constrained ct =>
        if usedDowncasts.contains (downcastProcName ct.name).text
        then some (mkConstraintDowncastFunc ptMap ct) else none
    | _ => none
  let witnessProcedures := program.types.filterMap fun
    | .Constrained ct => some (mkWitnessProc ptMap ct) | _ => none
  let funcDiags := program.staticProcedures.foldl (init := []) fun acc proc =>
    if proc.isFunctional && proc.outputs.any (fun p => isConstrainedType ptMap p.type.val) then
      acc.cons (diagnosticFromSource proc.name.source "constrained return types on functions are not yet supported")
    else acc
  ({ program with
    staticProcedures := constraintFuncs ++ constraintDowncasts
                        ++ elimStatic
                        ++ witnessProcedures
    types := program.types.filterMap fun
      | .Constrained _ => none
      | .Composite ct => some (.Composite (elimCompositeType ptMap model ct))
      | other => some other },
   funcDiags)

/-- Pipeline pass: constrained type elimination. -/
public def constrainedTypeElimPass : LoweringPass where
  name := "ConstrainedTypeElim"
  documentation := "Eliminates constrained types by replacing them with their base types and generating constraint-checking functions and witness procedures. Type tests against constrained types are rewritten to call the generated constraint function."
  needsResolves := true
  run := fun _ p m =>
    let (p', diags) := constrainedTypeElim m p
    (p', diags, {})

end Strata.Laurel
