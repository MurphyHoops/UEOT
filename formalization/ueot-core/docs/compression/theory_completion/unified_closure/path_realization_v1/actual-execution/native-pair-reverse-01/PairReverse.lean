import UEOT
import Lean.Elab.Command
open Lean Elab Command Meta
set_option maxHeartbeats 0
run_cmd do
  let a ← getConstInfo `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemorySafetyWitness.safe_source_all_times_mass_one
  let b ← getConstInfo `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemorySafetyWitness.unsafe_transition_time_one_mass_zero
  liftIO <| IO.println "REVERSE_PAIR_ENTER"
  let eq ← liftTermElabM do Meta.isDefEq b.type a.type
  liftIO <| IO.println s!"REVERSE_PAIR_COMPLETE {eq}"
