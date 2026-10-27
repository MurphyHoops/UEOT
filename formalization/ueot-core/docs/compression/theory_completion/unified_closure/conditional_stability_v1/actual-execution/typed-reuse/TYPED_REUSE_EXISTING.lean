import UEOT
import Lean.Elab.Command
open Lean Elab Command Meta
set_option maxHeartbeats 0
set_option maxRecDepth 16384
run_cmd do
  let env ← getEnv
  let names : Array Name := #[
    `PMF.filter_apply,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.NoisyFiniteRiskOracle.calibrated_reference_row,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.NoisyFiniteRiskOracle.empiricalDefect_nonneg,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_projected_path_error,
    `UEOT.V3.PathError.causalLaw_tv_bound,
    `UEOT.V3.PathError.tvDist_eq_one_sub_pmfCommonMass,
    `UEOT.V3.TotalVariation.tvDist_le_one,
    `UEOT.V3.TotalVariation.tvDist_map_le,
    `UEOT.V3.TotalVariation.tvDist_nonneg,
    `UEOT.V3.TotalVariation.tvEvent_le,
  ]
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.find? name | throwError s!"REUSE_SYMBOL_MISSING {name}"
    let rendered ← liftTermElabM do ppExpr info.type
    rows := rows.push <| Json.mkObj [("name", toJson name.toString), ("type", toJson rendered.pretty)]
  liftIO <| IO.println ("TYPED_REUSE_EXISTING_JSON " ++ (toJson rows).compress)
