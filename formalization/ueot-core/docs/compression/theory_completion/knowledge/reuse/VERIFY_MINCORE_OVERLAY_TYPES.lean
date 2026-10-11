import UEOT
open Lean Elab Command Meta

private def nameOfString (s : String) : Name :=
  (s.splitOn ".").foldl (fun n part => Name.str n part) Name.anonymous

run_cmd do
  let env ← getEnv
  let graph ← liftIO <| IO.FS.readFile "docs/compression/theory_completion/knowledge/audits/2026-10-10/all_3793_theorem_direct_reuse_graph.csv"
  let baseNames := (graph.splitOn "\n").drop 1 |>.filterMap fun line =>
    if line.isEmpty then none else
      match line.splitOn "," with
      | [] => none
      | name :: _ => some (nameOfString name)
  if baseNames.length != 3793 then
    throwError s!"BASE_GRAPH_COUNT {baseNames.length}"
  let newNames : Array Name := #[
    `UEOT.V3.Compression.TheoryCompletion.MinCore.RelationDefectPresentation.rescale_rel,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.RelationDefectPresentation.rescale_defect,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.RelationDefectPresentation.rescale_preserves_exact_relation,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.RelationDefectPresentation.rescale_zero_iff,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.RelationDefectPresentation.rescale_budget_iff,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.RelationDefectPresentation.rescale_changes_nonzero_defect,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.same_relation_arbitrary_positive_scale,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.no_relation_only_quantitative_recovery,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.exists_same_relation_different_defect,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.relationDefectPresentation_does_not_force_triangle
  ]
  let mut comparisons := 0
  let mut internalComparisons := 0
  let mut collisions : Array String := #[]
  for n in newNames do
    let some cn := env.find? n | throwError s!"NEW_SYMBOL_MISSING {n}"
    for b in baseNames do
      let some cb := env.find? b | throwError s!"BASE_SYMBOL_MISSING {b}"
      let eq ← liftTermElabM do Meta.isDefEq cn.type cb.type
      comparisons := comparisons + 1
      if eq then collisions := collisions.push s!"{n} == {b}"
  for i in [:newNames.size] do
    for j in [i+1:newNames.size] do
      let some ci := env.find? newNames[i]! | throwError "NEW_I_MISSING"
      let some cj := env.find? newNames[j]! | throwError "NEW_J_MISSING"
      let eq ← liftTermElabM do Meta.isDefEq ci.type cj.type
      internalComparisons := internalComparisons + 1
      if eq then collisions := collisions.push s!"{newNames[i]!} == {newNames[j]!}"
  liftIO <| IO.println s!"MINCORE_OVERLAY_TYPE_DISTINCTNESS new={newNames.size} base={baseNames.length} cross={comparisons} internal={internalComparisons} matches={collisions.size}"
  for m in collisions do liftIO <| IO.println m
  if !collisions.isEmpty then throwError "MINCORE_OVERLAY_TYPE_COLLISION"
