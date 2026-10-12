import UEOT
open Lean Elab Command Meta

private def nameOfString (s : String) : Name :=
  (s.splitOn ".").foldl (fun n part => Name.str n part) Name.anonymous

run_cmd do
  let env ← getEnv
  let graph ← liftIO <| IO.FS.readFile
    "docs/compression/theory_completion/knowledge/audits/2026-10-10/all_3793_theorem_direct_reuse_graph.csv"
  let baseNames := (graph.splitOn "\n").drop 1 |>.filterMap fun line =>
    if line.isEmpty then none else
      match line.splitOn "," with
      | [] => none
      | name :: _ => some (nameOfString name)
  if baseNames.length != 3793 then
    throwError s!"BASE_GRAPH_COUNT {baseNames.length}"

  /- The prior governed MINCORE overlay is immutable historical evidence.
     Its 10 theorem nodes are part of the registered comparison/dependency
     universe for this second additive overlay. -/
  let priorNames : Array Name := #[
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
  let newNames : Array Name := #[
    `UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.zero_defect_iff,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.rel_iff,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.forward_budget,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.reverse_budget,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.tendsto_zero_iff,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.rescaleCalibration,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.calibrated_weighted_chain_bound,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.same_relation_does_not_transport_unit_budget
  ]
  let registered := baseNames ++ priorNames.toList
  if registered.length != 3803 then
    throwError s!"REGISTERED_PRIOR_COUNT {registered.length}"

  let mut comparisons := 0
  let mut internalComparisons := 0
  let mut collisions : Array String := #[]
  for n in newNames do
    let some cn := env.find? n | throwError s!"NEW_SYMBOL_MISSING {n}"
    for b in registered do
      let some cb := env.find? b | throwError s!"REGISTERED_SYMBOL_MISSING {b}"
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
  liftIO <| IO.println s!"CALIBRATED_DEFECT_OVERLAY_TYPE_DISTINCTNESS new={newNames.size} registered_prior={registered.length} cross={comparisons} internal={internalComparisons} matches={collisions.size}"
  for m in collisions do liftIO <| IO.println m
  if !collisions.isEmpty then
    throwError "CALIBRATED_DEFECT_OVERLAY_TYPE_COLLISION"

  let allRegistered := registered ++ newNames.toList
  let mut registeredEdgeCount := 0
  for n in newNames do
    match env.find? n with
    | some (.thmInfo decl) =>
      let deps := decl.value.getUsedConstants.toList.filter fun x =>
        x != n && allRegistered.contains x
      let expected : List Name :=
        if n == `UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.rel_iff then
          [`UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.zero_defect_iff]
        else if n == `UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.tendsto_zero_iff then
          [`UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.reverse_budget]
        else if n == `UEOT.V3.Compression.TheoryCompletion.MinCore.calibrated_weighted_chain_bound then
          [`UEOT.V3.Compression.TransportCertificate.weighted_chain_bound]
        else
          []
      if deps.length != expected.length || !expected.all (fun x => deps.contains x) then
        throwError s!"CALIBRATED_DEFECT_OVERLAY_PROOF_DEPS_MISMATCH {n} actual={deps} expected={expected}"
      registeredEdgeCount := registeredEdgeCount + deps.length
      liftIO <| IO.println s!"CALIBRATED_DEFECT_OVERLAY_DEPS {n} -> {deps}"
    | some _ => throwError s!"NEW_SYMBOL_NOT_THEOREM {n}"
    | none => throwError s!"NEW_SYMBOL_MISSING_FOR_PROOF_AUDIT {n}"
  liftIO <| IO.println s!"CALIBRATED_DEFECT_OVERLAY_PROOF_DEPS registered_edges={registeredEdgeCount}"
  if registeredEdgeCount != 3 then
    throwError s!"CALIBRATED_DEFECT_OVERLAY_PROOF_EDGE_COUNT {registeredEdgeCount}"
