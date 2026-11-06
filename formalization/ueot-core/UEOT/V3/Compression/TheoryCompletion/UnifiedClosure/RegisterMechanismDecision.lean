import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentSharp
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionRealization
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionShort
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionNativeConsumer

/-!
# Permitted experiments and minimax decision loss in two registered mechanisms

These imports expose the fixed S/G transaction, joint filter, all-experiment
testing limits, whole-policy regret certificate and literal Store execution.
The return below is the existing four-point policy; this interface neither
constructs a second controller nor adds an observation to its input.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecision

open FiniteMechanismRegretCertificate (minimax worst)
open RegisterMechanismDecisionConsumer (oracle)
open RegisterMechanismDecisionRegret (mixedJ deterministicJ)
open RegisterMechanismDecisionNativeConsumer (nativeRhoJ)

/-- Executable entry: draw the independent uniform private seed once, then
dispatch the complete returned table using the original action/receipt protocol. -/
abbrev returned := RegisterMechanismDecisionConsumer.returned

/-- Frozen H=3 consumer. The unrestricted lower bound is realized by this
same returned controller on the native Store; removing private randomization
changes the attained minimax value. -/
theorem returned_contract :
    minimax oracle mixedJ = 3/128 ∧
    worst oracle nativeRhoJ = 3/128 ∧
    minimax oracle deterministicJ = 1/32 ∧
    nativeRhoJ .S = 161/128 ∧ nativeRhoJ .G = 157/128 :=
  ⟨RegisterMechanismDecisionRegret.minimax_regret_exact.1,
   RegisterMechanismDecisionNativeConsumer.returned_native_regret,
   RegisterMechanismDecisionRegret.deterministic_minimax_exact,
   RegisterMechanismDecisionNativeConsumer.returned_native_values⟩

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecision
