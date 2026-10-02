import UEOT.V3.Compression.CrossTrack.DualIsolationCore

/-!
# Canonical finite binding-isolation conorm

For a finite nontrivial assembly space, the diagnostic lower gain has a
canonical sharp value: the minimum ratio

`dist (D a) (D b) / dist a b`

over distinct assembly pairs.  This is the direct analogue, on the parent-
identification side, of Track S's canonical residual conorm on the semantic
side.
-/

namespace UEOT.V3.Compression.CrossTrack

universe uA uY

noncomputable section

variable {A : Type uA} {Y : Type uY}
variable [Fintype A] [Nontrivial A] [MetricSpace A] [MetricSpace Y]
noncomputable local instance dualIsolationConormDecidableEq : DecidableEq A :=
  Classical.decEq A

/-- Distinct ordered assembly pairs. -/
def bindingDistinctPairs : Finset (A × A) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2)

theorem bindingDistinctPairs_nonempty :
    (bindingDistinctPairs (A := A)).Nonempty := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  refine ⟨(a, b), ?_⟩
  simp [bindingDistinctPairs, hab]

/-- Diagnostic lower-gain ratio for one distinct assembly pair. -/
noncomputable def bindingPairGain
    (diagnostic : A → Y) (p : A × A) : ℝ :=
  dist (diagnostic p.1) (diagnostic p.2) / dist p.1 p.2

/-- Canonical finite binding-isolation conorm. -/
noncomputable def bindingIsolationConorm
    (diagnostic : A → Y) : ℝ :=
  (bindingDistinctPairs (A := A)).inf'
    (bindingDistinctPairs_nonempty (A := A))
    (bindingPairGain diagnostic)

theorem bindingIsolationConorm_nonneg
    (diagnostic : A → Y) :
    0 ≤ bindingIsolationConorm diagnostic := by
  unfold bindingIsolationConorm
  apply Finset.le_inf'
  intro p hp
  have hp' : p ∈ Finset.univ ∧ p.1 ≠ p.2 := by
    simpa [bindingDistinctPairs] using hp
  have hne : p.1 ≠ p.2 := hp'.2
  exact div_nonneg dist_nonneg (dist_pos.mpr hne).le

theorem bindingIsolationConorm_le_pairGain
    (diagnostic : A → Y) {a b : A} (hab : a ≠ b) :
    bindingIsolationConorm diagnostic ≤
      dist (diagnostic a) (diagnostic b) / dist a b := by
  unfold bindingIsolationConorm
  have hmem : (a, b) ∈ bindingDistinctPairs (A := A) := by
    simp [bindingDistinctPairs, hab]
  change (bindingDistinctPairs (A := A)).inf'
      (bindingDistinctPairs_nonempty (A := A))
      (bindingPairGain diagnostic) ≤ bindingPairGain diagnostic (a, b)
  exact Finset.inf'_le (bindingPairGain diagnostic) hmem

/-- The canonical conorm is itself the sharp finite lower-gain certificate. -/
theorem bindingIsolationConorm_lower
    (diagnostic : A → Y) (a b : A) :
    bindingIsolationConorm diagnostic * dist a b ≤
      dist (diagnostic a) (diagnostic b) := by
  by_cases hab : a = b
  · subst b
    simp
  · have hle := bindingIsolationConorm_le_pairGain diagnostic hab
    exact (le_div_iff₀ (dist_pos.mpr hab)).mp hle

/-- Positivity of the canonical finite binding conorm is exactly diagnostic
injectivity. -/
theorem bindingIsolationConorm_pos_iff_injective
    (diagnostic : A → Y) :
    0 < bindingIsolationConorm diagnostic ↔ Function.Injective diagnostic := by
  constructor
  · intro hpos
    exact BindingIsolation.injective diagnostic
      (bindingIsolationConorm diagnostic)
      ⟨hpos, bindingIsolationConorm_lower diagnostic⟩
  · intro hinj
    unfold bindingIsolationConorm
    obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_inf'
      (bindingDistinctPairs_nonempty (A := A)) (bindingPairGain diagnostic)
    rw [heq]
    have hp' : p ∈ Finset.univ ∧ p.1 ≠ p.2 := by
      simpa [bindingDistinctPairs] using hp
    have hpne : p.1 ≠ p.2 := hp'.2
    have hDne : diagnostic p.1 ≠ diagnostic p.2 :=
      fun h => hpne (hinj h)
    exact div_pos (dist_pos.mpr hDne) (dist_pos.mpr hpne)

/-- Canonical positive binding-isolation certificate obtained from finite
diagnostic injectivity. -/
theorem canonicalBindingIsolation_of_injective
    (diagnostic : A → Y) (hinj : Function.Injective diagnostic) :
    BindingIsolation diagnostic (bindingIsolationConorm diagnostic) := by
  refine ⟨(bindingIsolationConorm_pos_iff_injective diagnostic).2 hinj, ?_⟩
  exact bindingIsolationConorm_lower diagnostic

/-- The canonical conorm is the greatest admissible finite binding-isolation
constant. -/
theorem bindingIsolation_le_bindingIsolationConorm
    (diagnostic : A → Y) (beta : ℝ)
    (hiso : BindingIsolation diagnostic beta) :
    beta ≤ bindingIsolationConorm diagnostic := by
  unfold bindingIsolationConorm
  apply Finset.le_inf'
  intro p hp
  have hp' : p ∈ Finset.univ ∧ p.1 ≠ p.2 := by
    simpa [bindingDistinctPairs] using hp
  have hpne : p.1 ≠ p.2 := hp'.2
  have hlower := hiso.lower p.1 p.2
  simpa [bindingPairGain] using
    ((le_div_iff₀ (dist_pos.mpr hpne)).2 hlower)

end

end UEOT.V3.Compression.CrossTrack
