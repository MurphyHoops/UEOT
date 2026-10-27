import UEOT
import Lean.Elab.Command
open Lean Elab Command Meta
set_option maxHeartbeats 0
set_option maxRecDepth 16384
run_cmd do
  let env ← getEnv
  let name := `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryPhysicalSafety.actual_state_prefix_eq
  let some info := env.find? name | throwError "LEXICAL_HINT_SYMBOL_MISSING"
  let rendered ← liftTermElabM do ppExpr info.type
  let owner := (env.getModuleIdxFor? name).map fun idx => env.header.moduleNames[idx]!.toString
  let axs ← Lean.collectAxioms name
  let report := Json.mkObj [("name", toJson name.toString), ("type", toJson rendered.pretty),
    ("source_module", toJson owner), ("axioms", toJson (axs.map Name.toString))]
  liftIO <| IO.println ("TYPED_LEXICAL_EXTRA_JSON " ++ report.compress)
