import UEOT
import Lean.Elab.Command
open Lean Elab Command Meta
set_option maxHeartbeats 0
set_option maxRecDepth 16384
run_cmd do
  let env ← getEnv
  let names : Array Name := #[
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_map_mul_fiberPosterior,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_conditionedRow_mass,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_tv_bind_same_weights,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_conditionedRow_tv_le,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteWindowDoobWitnessCheck.actual_conditioned_doob_tv,
  ]
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.find? name | throwError s!"REUSE_SYMBOL_MISSING {name}"
    let rendered ← liftTermElabM do ppExpr info.type
    rows := rows.push <| Json.mkObj [("name", toJson name.toString), ("type", toJson rendered.pretty)]
  liftIO <| IO.println ("TYPED_REUSE_EXISTING_JSON " ++ (toJson rows).compress)
