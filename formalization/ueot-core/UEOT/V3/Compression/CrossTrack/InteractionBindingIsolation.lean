import UEOT.V3.Compression.CrossTrack.DualIsolationPMetRealization
import UEOT.V3.InformationPacking
import UEOT.V3.InformationZeroTV

/-!
# Interaction-generated binding isolation

This module removes the abstract diagnostic map from the first stage of Dual
Isolation.  A richer parent assembly is identified by its family of response
laws under a finite set of probes/interventions.  The induced fingerprint
distance is the maximum total-variation separation over those probes.

For a finite nontrivial assembly space, the canonical lower gain of that
interaction fingerprint is positive exactly when the selected probe family
separates every distinct pair of candidate assemblies.
-/

namespace UEOT.V3.Compression.CrossTrack

open MeasureTheory
open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.TotalVariation
open UEOT.V3.InformationPacking
open UEOT.V3.InformationZeroTV
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe uA uI uY uP uC uX uS

noncomputable section

/-- A family of probability response laws indexed by richer assemblies and
available probes/interventions. -/
structure InteractionResponseFamily
    (A : Type uA) (I : Type uI) (Y : Type uY)
    [MeasurableSpace Y] where
  response : A → I → Measure Y
  probability : ∀ a i, IsProbabilityMeasure (response a i)

variable {A : Type uA} {I : Type uI} {Y : Type uY}
variable [MeasurableSpace Y]

/-- Maximum TV separation of two assembly response fingerprints on one finite
nonempty probe family. -/
noncomputable def interactionFingerprintDist
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (a b : A) : ℝ :=
  probes.sup' hprobes (fun i => tvDist (F.response a i) (F.response b i))

theorem interactionFingerprintDist_nonneg
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (a b : A) :
    0 ≤ interactionFingerprintDist F probes hprobes a b := by
  rcases hprobes with ⟨i, hi⟩
  let _ : IsProbabilityMeasure (F.response a i) := F.probability a i
  let _ : IsProbabilityMeasure (F.response b i) := F.probability b i
  exact (tvDist_nonneg (F.response a i) (F.response b i)).trans
    (by
      unfold interactionFingerprintDist
      exact Finset.le_sup'
        (fun j : I => (tvDist (F.response a j) (F.response b j) : ℝ)) hi)

theorem interactionFingerprintDist_symm
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (a b : A) :
    interactionFingerprintDist F probes hprobes a b =
      interactionFingerprintDist F probes hprobes b a := by
  unfold interactionFingerprintDist
  apply le_antisymm
  · apply Finset.sup'_le hprobes
    intro i hi
    let _ : IsProbabilityMeasure (F.response a i) := F.probability a i
    let _ : IsProbabilityMeasure (F.response b i) := F.probability b i
    rw [tvDist_symm]
    exact Finset.le_sup'
      (fun j : I => (tvDist (F.response b j) (F.response a j) : ℝ)) hi
  · apply Finset.sup'_le hprobes
    intro i hi
    let _ : IsProbabilityMeasure (F.response a i) := F.probability a i
    let _ : IsProbabilityMeasure (F.response b i) := F.probability b i
    rw [tvDist_symm]
    exact Finset.le_sup'
      (fun j : I => (tvDist (F.response a j) (F.response b j) : ℝ)) hi

/-- Fingerprint distance vanishes exactly when every selected probe gives the
same response law. -/
theorem interactionFingerprintDist_eq_zero_iff
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (a b : A) :
    interactionFingerprintDist F probes hprobes a b = 0 ↔
      ∀ i ∈ probes, F.response a i = F.response b i := by
  constructor
  · intro hzero i hi
    let _ : IsProbabilityMeasure (F.response a i) := F.probability a i
    let _ : IsProbabilityMeasure (F.response b i) := F.probability b i
    have hle : tvDist (F.response a i) (F.response b i) ≤ 0 := by
      have hsup : tvDist (F.response a i) (F.response b i) ≤
          interactionFingerprintDist F probes hprobes a b := by
        unfold interactionFingerprintDist
        exact Finset.le_sup'
          (fun j : I => (tvDist (F.response a j) (F.response b j) : ℝ)) hi
      simpa [hzero] using hsup
    have htv0 : tvDist (F.response a i) (F.response b i) = 0 :=
      le_antisymm hle (tvDist_nonneg _ _)
    exact measure_eq_of_tvDist_eq_zero _ _ htv0
  · intro hall
    apply le_antisymm
    · unfold interactionFingerprintDist
      apply Finset.sup'_le hprobes
      intro i hi
      let _ : IsProbabilityMeasure (F.response a i) := F.probability a i
      let _ : IsProbabilityMeasure (F.response b i) := F.probability b i
      rw [hall i hi]
      exact le_of_eq (tvDist_self_eq_zero (F.response b i))
    · exact interactionFingerprintDist_nonneg F probes hprobes a b

/-- Positive fingerprint separation is equivalent to at least one selected
probe distinguishing the two response laws. -/
theorem interactionFingerprintDist_pos_iff
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (a b : A) :
    0 < interactionFingerprintDist F probes hprobes a b ↔
      ∃ i ∈ probes, F.response a i ≠ F.response b i := by
  constructor
  · intro hpos
    by_contra hnone
    have hall : ∀ i ∈ probes, F.response a i = F.response b i := by
      intro i hi
      by_contra hne
      exact hnone ⟨i, hi, hne⟩
    have hzero :=
      (interactionFingerprintDist_eq_zero_iff F probes hprobes a b).2 hall
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · rintro ⟨i, hi, hne⟩
    let _ : IsProbabilityMeasure (F.response a i) := F.probability a i
    let _ : IsProbabilityMeasure (F.response b i) := F.probability b i
    have htvne : tvDist (F.response a i) (F.response b i) ≠ 0 := by
      intro hzero
      exact hne (measure_eq_of_tvDist_eq_zero _ _ hzero)
    have htvpos : 0 < tvDist (F.response a i) (F.response b i) :=
      lt_of_le_of_ne (tvDist_nonneg _ _) (Ne.symm htvne)
    exact htvpos.trans_le (by
      unfold interactionFingerprintDist
      exact Finset.le_sup'
        (fun j : I => (tvDist (F.response a j) (F.response b j) : ℝ)) hi)

/-- Selected probes distinguish every distinct richer assembly candidate. -/
def PairwiseInteractionSeparating
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) : Prop :=
  ∀ ⦃a b : A⦄, a ≠ b →
    ∃ i ∈ probes, F.response a i ≠ F.response b i

variable [Fintype A] [Nontrivial A] [MetricSpace A]
noncomputable local instance interactionBindingDecidableEqA : DecidableEq A :=
  Classical.decEq A

/-- Distinct-pair interaction gain. -/
noncomputable def interactionPairGain
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (p : A × A) : ℝ :=
  interactionFingerprintDist F probes hprobes p.1 p.2 / dist p.1 p.2

/-- Canonical finite interaction-generated binding isolation margin. -/
noncomputable def interactionIsolationConorm
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty) : ℝ :=
  (bindingDistinctPairs (A := A)).inf'
    (bindingDistinctPairs_nonempty (A := A))
    (interactionPairGain F probes hprobes)

theorem interactionIsolationConorm_nonneg
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty) :
    0 ≤ interactionIsolationConorm F probes hprobes := by
  unfold interactionIsolationConorm
  apply Finset.le_inf'
  intro p hp
  have hp' : p ∈ Finset.univ ∧ p.1 ≠ p.2 := by
    simpa [bindingDistinctPairs] using hp
  exact div_nonneg
    (interactionFingerprintDist_nonneg F probes hprobes p.1 p.2)
    (dist_pos.mpr hp'.2).le

theorem interactionIsolationConorm_le_pairGain
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    {a b : A} (hab : a ≠ b) :
    interactionIsolationConorm F probes hprobes ≤
      interactionFingerprintDist F probes hprobes a b / dist a b := by
  unfold interactionIsolationConorm
  have hmem : (a, b) ∈ bindingDistinctPairs (A := A) := by
    simp [bindingDistinctPairs, hab]
  change (bindingDistinctPairs (A := A)).inf'
      (bindingDistinctPairs_nonempty (A := A))
      (interactionPairGain F probes hprobes) ≤
        interactionPairGain F probes hprobes (a, b)
  exact Finset.inf'_le _ hmem

theorem interactionIsolationConorm_lower
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (a b : A) :
    interactionIsolationConorm F probes hprobes * dist a b ≤
      interactionFingerprintDist F probes hprobes a b := by
  by_cases hab : a = b
  · subst b
    simpa using interactionFingerprintDist_nonneg F probes hprobes a a
  · have hle := interactionIsolationConorm_le_pairGain
      F probes hprobes hab
    exact (le_div_iff₀ (dist_pos.mpr hab)).mp hle

/-- **Interaction separation theorem.**

For a finite nontrivial assembly space, the canonical interaction-generated
binding margin is positive exactly when the selected finite probe family
distinguishes every distinct pair of candidate assemblies. -/
theorem interactionIsolationConorm_pos_iff_pairwiseSeparating
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty) :
    0 < interactionIsolationConorm F probes hprobes ↔
      PairwiseInteractionSeparating F probes := by
  constructor
  · intro hpos a b hab
    have hlower := interactionIsolationConorm_lower
      F probes hprobes a b
    have hdist : 0 < dist a b := dist_pos.mpr hab
    have hprod : 0 < interactionIsolationConorm F probes hprobes * dist a b :=
      mul_pos hpos hdist
    have hfp : 0 < interactionFingerprintDist F probes hprobes a b :=
      hprod.trans_le hlower
    exact (interactionFingerprintDist_pos_iff F probes hprobes a b).1 hfp
  · intro hsep
    unfold interactionIsolationConorm
    obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_inf'
      (bindingDistinctPairs_nonempty (A := A))
      (interactionPairGain F probes hprobes)
    rw [heq]
    have hp' : p ∈ Finset.univ ∧ p.1 ≠ p.2 := by
      simpa [bindingDistinctPairs] using hp
    have hfp : 0 < interactionFingerprintDist F probes hprobes p.1 p.2 :=
      (interactionFingerprintDist_pos_iff F probes hprobes p.1 p.2).2
        (hsep hp'.2)
    exact div_pos hfp (dist_pos.mpr hp'.2)

/-- The canonical interaction conorm itself gives the sharp finite lower-gain
certificate. -/
theorem interactionIsolationConorm_isolation
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (hsep : PairwiseInteractionSeparating F probes) :
    0 < interactionIsolationConorm F probes hprobes ∧
      ∀ a b,
        interactionIsolationConorm F probes hprobes * dist a b ≤
          interactionFingerprintDist F probes hprobes a b := by
  exact ⟨(interactionIsolationConorm_pos_iff_pairwiseSeparating
    F probes hprobes).2 hsep,
    interactionIsolationConorm_lower F probes hprobes⟩

/-- Adding probes cannot decrease pairwise fingerprint separation. -/
theorem interactionFingerprintDist_mono_probes
    (F : InteractionResponseFamily A I Y)
    {P Q : Finset I} (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPQ : P ⊆ Q) (a b : A) :
    interactionFingerprintDist F P hP a b ≤
      interactionFingerprintDist F Q hQ a b := by
  unfold interactionFingerprintDist
  apply Finset.sup'_le hP
  intro i hi
  exact Finset.le_sup'
    (fun j : I => (tvDist (F.response a j) (F.response b j) : ℝ)) (hPQ hi)

/-- Adding probes cannot decrease the canonical interaction isolation margin. -/
theorem interactionIsolationConorm_mono_probes
    (F : InteractionResponseFamily A I Y)
    {P Q : Finset I} (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPQ : P ⊆ Q) :
    interactionIsolationConorm F P hP ≤
      interactionIsolationConorm F Q hQ := by
  unfold interactionIsolationConorm
  apply Finset.le_inf'
  intro p hp
  have hp' : p ∈ Finset.univ ∧ p.1 ≠ p.2 := by
    simpa [bindingDistinctPairs] using hp
  have hgain := interactionFingerprintDist_mono_probes
    F hP hQ hPQ p.1 p.2
  have hden : 0 < dist p.1 p.2 := dist_pos.mpr hp'.2
  have hratio : interactionPairGain F P hP p ≤
      interactionPairGain F Q hQ p := by
    exact div_le_div_of_nonneg_right hgain hden.le
  have hleft : interactionIsolationConorm F P hP ≤
      interactionPairGain F P hP p := by
    exact Finset.inf'_le _ hp
  exact hleft.trans hratio

/-- Maximum TV discrepancy between one assembly's response fingerprint and an
observed response family on the selected probes. -/
noncomputable def interactionObservationError
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (observed : I → Measure Y)
    (a : A) : ℝ :=
  probes.sup' hprobes (fun i => tvDist (F.response a i) (observed i))

theorem interactionFingerprintDist_le_observationErrors
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (observed : I → Measure Y)
    (hobserved : ∀ i, IsProbabilityMeasure (observed i))
    (a b : A) :
    interactionFingerprintDist F probes hprobes a b ≤
      interactionObservationError F probes hprobes observed a +
        interactionObservationError F probes hprobes observed b := by
  unfold interactionFingerprintDist
  apply Finset.sup'_le hprobes
  intro i hi
  let _ : IsProbabilityMeasure (F.response a i) := F.probability a i
  let _ : IsProbabilityMeasure (F.response b i) := F.probability b i
  let _ : IsProbabilityMeasure (observed i) := hobserved i
  have htri := tvDist_triangle (F.response a i) (observed i) (F.response b i)
  have hsym : tvDist (observed i) (F.response b i) =
      tvDist (F.response b i) (observed i) := tvDist_symm _ _
  rw [hsym] at htri
  have ha : tvDist (F.response a i) (observed i) ≤
      interactionObservationError F probes hprobes observed a := by
    unfold interactionObservationError
    exact Finset.le_sup'
      (fun j : I => (tvDist (F.response a j) (observed j) : ℝ)) hi
  have hb : tvDist (F.response b i) (observed i) ≤
      interactionObservationError F probes hprobes observed b := by
    unfold interactionObservationError
    exact Finset.le_sup'
      (fun j : I => (tvDist (F.response b j) (observed j) : ℝ)) hi
  exact htri.trans (add_le_add ha hb)

/-- One observed interaction fingerprint with radius `eta` identifies the
assembly up to `2 eta / beta`. -/
theorem assemblyDist_le_two_observationError_div_interactionConorm
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (hsep : PairwiseInteractionSeparating F probes)
    (observed : I → Measure Y)
    (hobserved : ∀ i, IsProbabilityMeasure (observed i))
    (eta : ℝ)
    {a b : A}
    (ha : interactionObservationError F probes hprobes observed a ≤ eta)
    (hb : interactionObservationError F probes hprobes observed b ≤ eta) :
    dist a b ≤ 2 * eta / interactionIsolationConorm F probes hprobes := by
  have hfp := interactionFingerprintDist_le_observationErrors
    F probes hprobes observed hobserved a b
  have hfpEta : interactionFingerprintDist F probes hprobes a b ≤ 2 * eta := by
    linarith
  have hlower := interactionIsolationConorm_lower F probes hprobes a b
  have hbeta : 0 < interactionIsolationConorm F probes hprobes :=
    (interactionIsolationConorm_pos_iff_pairwiseSeparating F probes hprobes).2 hsep
  have hprod : interactionIsolationConorm F probes hprobes * dist a b ≤
      2 * eta := hlower.trans hfpEta
  exact (le_div_iff₀ hbeta).2 (by simpa [mul_comm] using hprod)

/-! ## Composition with P-MET realization and Track-S semantic isolation -/

variable {P : Type uP} {C : Type uC} {X : Type uX}
variable [MeasurableSpace X]
variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance interactionBindingDecidableEqS : DecidableEq S :=
  Classical.decEq S

/-- **End-to-end interaction-generated parent semantic bound.**

The selected probe family itself supplies the canonical binding margin; a
common-Markov parent realization removes the forward Lipschitz factor; Track S
supplies the semantic-isolation margin. -/
theorem interactionGenerated_commonMarkov_fiberSemanticDiameter
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (hsep : PairwiseInteractionSeparating F probes)
    (observed : I → Measure Y)
    (hobserved : ∀ i, IsProbabilityMeasure (observed i))
    (eta : ℝ) (heta : 0 ≤ eta)
    (pi : P → C)
    (repr : P → A)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (real : CommonMarkovParentRealization X repr K hK)
    (mu : P → stdSimplex ℝ S)
    (hmu : ∀ p, mu p ∈ invariantLawSet (K p) (hK p))
    (c : C)
    (hfiberNonempty : ∃ p, pi p = c)
    (kappaMin : ℝ) (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hobs : ∀ p, pi p = c →
      interactionObservationError F probes hprobes observed (repr p) ≤ eta)
    (hisolationFloor : ∀ p, pi p = c →
      kappaMin ≤ l1ResidualConorm (K p)) :
    fiberSemanticDiameter pi mu c ≤
      (2 * eta) /
        (interactionIsolationConorm F probes hprobes * kappaMin) := by
  have hbeta : 0 < interactionIsolationConorm F probes hprobes :=
    (interactionIsolationConorm_pos_iff_pairwiseSeparating F probes hprobes).2 hsep
  have hbound := parentSemanticDiameter_of_binding
    pi repr K hK (real.toParentBinding repr K hK) mu hmu
    c hfiberNonempty
    (2 * eta / interactionIsolationConorm F probes hprobes)
    kappaMin
    (div_nonneg (mul_nonneg (by norm_num) heta) hbeta.le)
    hkappaMin hcard
    (by
      intro p q hp hq
      exact assemblyDist_le_two_observationError_div_interactionConorm
        F probes hprobes hsep observed hobserved eta (hobs p hp) (hobs q hq))
    hisolationFloor
  rw [CommonMarkovParentRealization.toParentBinding_L] at hbound
  have hbeta0 : interactionIsolationConorm F probes hprobes ≠ 0 := ne_of_gt hbeta
  have hkappa0 : kappaMin ≠ 0 := ne_of_gt hkappaMin
  convert hbound using 1
  field_simp [hbeta0, hkappa0]

end

end UEOT.V3.Compression.CrossTrack
