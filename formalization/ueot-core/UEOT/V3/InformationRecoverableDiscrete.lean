import UEOT.V3.InformationMemoryBound
import UEOT.V3.InformationEntropyBound
import UEOT.V3.InformationDiscreteEntropy

/-!
# Recoverable countable state: mutual information equals entropy

If a measurable decoder recovers a countable discrete state `C` from `M`, then
`I(C;M)=H(C)`.  Recoverability is expressed at the law level by saying that
pushing `(C,M)` through `(c,m) ↦ (c,d(m))` gives the diagonal copy law of `C`.

This formulation is stable under conditioning and is the fiber theorem needed
for P-INFO-03.
-/

namespace UEOT.V3.InformationRecoverableDiscrete

noncomputable section

open MeasureTheory InformationTheory
open scoped ENNReal
open UEOT.V3.InformationCore
open UEOT.V3.InformationEntropyBound
open UEOT.V3.InformationDiscreteEntropy
open UEOT.V3.InformationMemoryBound

universe uC uM

variable {C : Type uC} {M : Type uM}
variable [MeasurableSpace C] [MeasurableSpace M]
variable [Countable C] [MeasurableSingletonClass C]
variable [StandardBorelSpace M] [Nonempty M]

/-- Keep the true `C` coordinate and decode a second copy from `M`. -/
def decodedCopyMap (d : M → C) : C × M → C × C :=
  fun z => (z.1, d z.2)

lemma measurable_decodedCopyMap (d : M → C) (hd : Measurable d) :
    Measurable (decodedCopyMap d) := by
  unfold decodedCopyMap
  exact measurable_fst.prodMk (hd.comp measurable_snd)

/-- Law-level recoverability implies that the decoded marginal equals the true
`C` marginal. -/
theorem decoded_marginal_eq
    (ρ : Measure (C × M)) [IsProbabilityMeasure ρ]
    (d : M → C) (hd : Measurable d)
    (hrec : ρ.map (decodedCopyMap d) = copyJoint ρ.fst) :
    ρ.snd.map d = ρ.fst := by
  have hsnd := congrArg Measure.snd hrec
  have hleft : (ρ.map (decodedCopyMap d)).snd = ρ.snd.map d := by
    unfold Measure.snd
    rw [Measure.map_map measurable_snd (measurable_decodedCopyMap d hd)]
    rw [Measure.map_map hd measurable_snd]
    rfl
  have hright : (copyJoint ρ.fst).snd = ρ.fst := by
    unfold copyJoint Measure.snd
    rw [Measure.map_map measurable_snd]
    simp
  simpa [hleft, hright] using hsnd

/-- The independent-product reference pushed through the decoder becomes two
independent copies of the `C` marginal. -/
theorem product_reference_map_decodedCopy
    (ρ : Measure (C × M)) [IsProbabilityMeasure ρ]
    (d : M → C) (hd : Measurable d)
    (hrec : ρ.map (decodedCopyMap d) = copyJoint ρ.fst) :
    (ρ.fst.prod ρ.snd).map (decodedCopyMap d) =
      ρ.fst.prod ρ.fst := by
  have hmarg : ρ.snd.map d = ρ.fst := decoded_marginal_eq ρ d hd hrec
  have hmap := Measure.map_prod_map ρ.fst ρ.snd measurable_id hd
  simpa [decodedCopyMap, hmarg] using hmap

/-- Recoverability gives the entropy lower bound `H(C) ≤ I(C;M)` by KL data
processing through the decoder. -/
theorem discreteShannonEntropy_le_mutualInfo_of_recoverable
    (ρ : Measure (C × M)) [IsProbabilityMeasure ρ]
    (d : M → C) (hd : Measurable d)
    (hrec : ρ.map (decodedCopyMap d) = copyJoint ρ.fst) :
    discreteShannonEntropy ρ.fst ≤ mutualInfo ρ := by
  have hdp := InformationTheory.klDiv_map_le
    ρ (ρ.fst.prod ρ.snd) (measurable_decodedCopyMap d hd)
  rw [hrec, product_reference_map_decodedCopy ρ d hd hrec] at hdp
  rw [copy_kl_eq_discreteShannonEntropy ρ.fst] at hdp
  simpa [mutualInfo] using hdp

/-- **Recoverable countable state identity.**  A countable discrete state that
is measurably recoverable from `M` carries exactly its Shannon entropy as mutual
information with `M`. -/
theorem mutualInfo_eq_discreteShannonEntropy_of_recoverable
    (ρ : Measure (C × M)) [IsProbabilityMeasure ρ]
    (d : M → C) (hd : Measurable d)
    (hrec : ρ.map (decodedCopyMap d) = copyJoint ρ.fst) :
    mutualInfo ρ = discreteShannonEntropy ρ.fst := by
  apply le_antisymm
  · exact mutualInfo_le_discreteShannonEntropy ρ
  · exact discreteShannonEntropy_le_mutualInfo_of_recoverable ρ d hd hrec

end

end UEOT.V3.InformationRecoverableDiscrete
