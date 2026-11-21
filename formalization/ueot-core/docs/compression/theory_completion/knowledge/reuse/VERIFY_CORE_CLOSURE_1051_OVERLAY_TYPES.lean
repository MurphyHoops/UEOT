import UEOT
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command Meta
set_option maxHeartbeats 0
set_option maxRecDepth 16384

run_cmd do
  let env ← getEnv
  let newNames : Array Name := #[
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer.exact_cached_data,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer.exact_two_data,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionRegret.minimax_regret_exact,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionRealization.returned_beats_every_raw_regret
  ]
  for i in [:newNames.size] do
    let n := newNames[i]!
    let some ci := env.find? n | throwError s!"NEW_SYMBOL_MISSING {n}"
    let axs ← liftCoreM (Lean.collectAxioms n)
    for ax in axs do
      unless [`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError s!"NONSTANDARD_AXIOM {n}: {ax}"
    for j in [i+1:newNames.size] do
      let some cj := env.find? newNames[j]! | throwError s!"NEW_SYMBOL_MISSING {newNames[j]!}"
      let eq ← liftTermElabM do Meta.isDefEq ci.type cj.type
      if eq then throwError s!"INTERNAL_TYPE_COLLISION {n} == {newNames[j]!}"
  logInfo s!"CORE_CLOSURE_1051_OVERLAY_TYPES_PASS count={newNames.size}"
