import UEOTQM.Effects
import UEOTQM.Transport

/-!
# All-effect response distance and actual quantum stability

The distance is the supremum of actual Born probability differences over all
effects 0 <= E <= I. Its boundedness, symmetry, triangle inequality, complete
Kraus-channel contraction, and selective-branch conditioning bound are derived
here. None is an assumed field of an abstract error-certificate structure.

This module does not identify the distance with trace norm or diamond norm.
Its zero theorem is explicitly agreement of all effect probabilities; no
separate matrix-tomography or metric-instance claim is hidden in that theorem.
The channel defect is also an actual supremum, including 0 to cover the empty
density domain, and yields a proved local perturbation recurrence.
-/

namespace UEOTQM

open scoped BigOperators

noncomputable section

variable {ι κ O A : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [Fintype O]

def effectGapSet (ρ σ : Density ι) : Set ℝ :=
  Set.range (fun E : Effect ι => |E.probability ρ - E.probability σ|)

theorem Effect.probability_abs_sub_le_one (E : Effect ι) (ρ σ : Density ι) :
    |E.probability ρ - E.probability σ| ≤ 1 := by
  apply abs_le.mpr
  have hρ0 := E.probability_nonneg ρ
  have hρ1 := E.probability_le_one ρ
  have hσ0 := E.probability_nonneg σ
  have hσ1 := E.probability_le_one σ
  constructor <;> linarith

theorem effectGapSet_nonempty (ρ σ : Density ι) : (effectGapSet ρ σ).Nonempty := by
  refine ⟨0, Effect.zero, ?_⟩
  simp

theorem effectGapSet_bddAbove (ρ σ : Density ι) : BddAbove (effectGapSet ρ σ) := by
  refine ⟨1, ?_⟩
  rintro x ⟨E, rfl⟩
  exact E.probability_abs_sub_le_one ρ σ

/-- All effects, not a finite sampled set or a selected protocol library. -/
def effectDistance (ρ σ : Density ι) : ℝ := sSup (effectGapSet ρ σ)

theorem Effect.probability_sub_le_effectDistance (E : Effect ι) (ρ σ : Density ι) :
    |E.probability ρ - E.probability σ| ≤ effectDistance ρ σ :=
  le_csSup (effectGapSet_bddAbove ρ σ) ⟨E, rfl⟩

theorem effectDistance_nonneg (ρ σ : Density ι) : 0 ≤ effectDistance ρ σ := by
  simpa using (Effect.zero : Effect ι).probability_sub_le_effectDistance ρ σ

theorem effectDistance_le_iff (ρ σ : Density ι) (r : ℝ) :
    effectDistance ρ σ ≤ r ↔ ∀ E : Effect ι, |E.probability ρ - E.probability σ| ≤ r := by
  constructor
  · intro h E
    exact (E.probability_sub_le_effectDistance ρ σ).trans h
  · intro h
    apply csSup_le (effectGapSet_nonempty ρ σ)
    rintro x ⟨E, rfl⟩
    exact h E

theorem effectDistance_le_one (ρ σ : Density ι) : effectDistance ρ σ ≤ 1 := by
  apply (effectDistance_le_iff _ _ _).mpr
  intro E
  exact E.probability_abs_sub_le_one ρ σ

@[simp] theorem effectDistance_self (ρ : Density ι) : effectDistance ρ ρ = 0 := by
  apply le_antisymm ?_ (effectDistance_nonneg ρ ρ)
  exact (effectDistance_le_iff ρ ρ 0).mpr (fun E => by simp)

theorem effectDistance_comm (ρ σ : Density ι) : effectDistance ρ σ = effectDistance σ ρ := by
  apply le_antisymm
  · apply (effectDistance_le_iff _ _ _).mpr
    intro E
    rw [abs_sub_comm]
    exact E.probability_sub_le_effectDistance σ ρ
  · apply (effectDistance_le_iff _ _ _).mpr
    intro E
    rw [abs_sub_comm]
    exact E.probability_sub_le_effectDistance ρ σ

theorem effectDistance_triangle (ρ σ τ : Density ι) :
    effectDistance ρ τ ≤ effectDistance ρ σ + effectDistance σ τ := by
  apply (effectDistance_le_iff _ _ _).mpr
  intro E
  exact (abs_sub_le (E.probability ρ) (E.probability σ) (E.probability τ)).trans
    (add_le_add (E.probability_sub_le_effectDistance ρ σ)
      (E.probability_sub_le_effectDistance σ τ))

theorem effectDistance_eq_zero_iff (ρ σ : Density ι) :
    effectDistance ρ σ = 0 ↔ ∀ E : Effect ι, E.probability ρ = E.probability σ := by
  constructor
  · intro h E
    have hg := E.probability_sub_le_effectDistance ρ σ
    rw [h] at hg
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hg)
  · intro h
    apply le_antisymm ?_ (effectDistance_nonneg ρ σ)
    apply (effectDistance_le_iff _ _ _).mpr
    intro E
    rw [h E]
    simp

theorem response_sub_le_effectDistance (I : A → Instrument ι O κ)
    (ρ σ : Density ι) (w : List (A × O)) :
    |response I ρ w - response I σ w| ≤ effectDistance ρ σ := by
  rw [response_eq_effect_probability, response_eq_effect_probability]
  exact (recordTest I w).probability_sub_le_effectDistance ρ σ

/-- Actual worst-case output gap, not a user-supplied defect conclusion.
Inserting 0 makes the definition nonempty even if the density type is empty. -/
def channelDefect (F G : Density ι → Density ι) : ℝ :=
  sSup (Set.insert 0 (Set.range (fun ρ => effectDistance (F ρ) (G ρ))))

theorem channelDefect_bddAbove (F G : Density ι → Density ι) :
    BddAbove (Set.insert 0 (Set.range (fun ρ => effectDistance (F ρ) (G ρ)))) := by
  refine ⟨1, ?_⟩
  rintro x (rfl | ⟨ρ, rfl⟩)
  · norm_num
  · exact effectDistance_le_one (F ρ) (G ρ)

theorem channelDefect_nonneg (F G : Density ι → Density ι) : 0 ≤ channelDefect F G :=
  le_csSup (channelDefect_bddAbove F G) (Set.mem_insert 0 _)

theorem channelDefect_le_one (F G : Density ι → Density ι) : channelDefect F G ≤ 1 := by
  apply csSup_le (Set.insert_nonempty 0 _)
  rintro x (rfl | ⟨ρ, rfl⟩)
  · norm_num
  · exact effectDistance_le_one (F ρ) (G ρ)

theorem effectDistance_le_channelDefect (F G : Density ι → Density ι) (ρ : Density ι) :
    effectDistance (F ρ) (G ρ) ≤ channelDefect F G :=
  le_csSup (channelDefect_bddAbove F G) (Set.mem_insert_of_mem 0 ⟨ρ, rfl⟩)

@[simp] theorem channelDefect_self (F : Density ι → Density ι) : channelDefect F F = 0 := by
  apply le_antisymm ?_ (channelDefect_nonneg F F)
  apply csSup_le (Set.insert_nonempty 0 _)
  rintro x (rfl | ⟨ρ, rfl⟩)
  · exact le_rfl
  · simp

namespace Instrument

/-- Complete Kraus channels contract the actual all-effect response distance. -/
theorem channelState_effectDistance_le (I : Instrument ι O κ) (ρ σ : Density ι) :
    effectDistance (I.channelState ρ) (I.channelState σ) ≤ effectDistance ρ σ := by
  apply (effectDistance_le_iff _ _ _).mpr
  intro E
  rw [I.probability_channelState E ρ, I.probability_channelState E σ]
  exact (I.pullbackEffect E).probability_sub_le_effectDistance ρ σ

theorem probability_sub_le_effectDistance (I : Instrument ι O κ)
    (o : O) (ρ σ : Density ι) :
    |I.probability ρ o - I.probability σ o| ≤ effectDistance ρ σ := by
  rw [← I.probability_branchEffect_one o ρ, ← I.probability_branchEffect_one o σ]
  exact (I.branchEffect o Effect.one).probability_sub_le_effectDistance ρ σ

theorem probability_pos_of_effectDistance_lt (I : Instrument ι O κ)
    (o : O) (ρ σ : Density ι) (h : effectDistance ρ σ < I.probability ρ o) :
    0 < I.probability σ o := by
  have hgap := (le_abs_self (I.probability ρ o - I.probability σ o)).trans
    (I.probability_sub_le_effectDistance o ρ σ)
  linarith

/-- An actual local perturbation bound, derived from contraction and the
defined channel defect; it supplies the missing quantum-side recurrence. -/
theorem channelState_perturbation_bound {O' κ' : Type*} [Fintype O'] [Fintype κ']
    (I : Instrument ι O κ) (J : Instrument ι O' κ') (ρ σ : Density ι) :
    effectDistance (I.channelState ρ) (J.channelState σ) ≤
      effectDistance ρ σ + channelDefect I.channelState J.channelState := by
  exact (effectDistance_triangle (I.channelState ρ) (I.channelState σ) (J.channelState σ)).trans
    (add_le_add (I.channelState_effectDistance_le ρ σ)
      (effectDistance_le_channelDefect I.channelState J.channelState σ))

end Instrument

/-- Elementary normalization bound. The second unnormalized event weight
lies in [0,q]; both event masses must be strictly positive. -/
theorem normalized_probability_difference_le (a b p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hb : 0 ≤ b) (hbq : b ≤ q) :
    |a / p - b / q| ≤ (|a - b| + |p - q|) / p := by
  have hratio0 : 0 ≤ b / q := div_nonneg hb hq.le
  have hratio1 : b / q ≤ 1 := (div_le_one hq).mpr hbq
  have hid : a / p - b / q = (a - b + (q - p) * (b / q)) / p := by
    field_simp [hp.ne', hq.ne']
    ring
  rw [hid, abs_div, abs_of_pos hp]
  apply (div_le_div_iff_of_pos_right hp).mpr
  calc
    |a - b + (q - p) * (b / q)| ≤ |a - b| + |(q - p) * (b / q)| := abs_add_le _ _
    _ = |a - b| + |q - p| * (b / q) := by rw [abs_mul, abs_of_nonneg hratio0]
    _ ≤ |a - b| + |q - p| :=
      add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) hratio1)
    _ = |a - b| + |p - q| := by rw [abs_sub_comm q p]

namespace Instrument

/-- Selective conditioning is not asserted contractive. Its amplification is
bounded using the actual Born mass of the first state. -/
theorem posterior_effectDistance_le (I : Instrument ι O κ) (o : O) (ρ σ : Density ι)
    (hρ : 0 < I.probability ρ o) (hσ : 0 < I.probability σ o) :
    effectDistance (I.posterior ρ o hρ) (I.posterior σ o hσ) ≤
      2 * effectDistance ρ σ / I.probability ρ o := by
  apply (effectDistance_le_iff _ _ _).mpr
  intro E
  have hbq : (I.branchEffect o E).probability σ ≤ I.probability σ o := by
    change pairing (I.branchEffect o E).matrix σ.matrix ≤ mass (I.branch o σ.matrix)
    rw [I.pairing_branchEffect]
    exact E.pairing_le_mass (I.branch_posSemidef o σ.positive)
  rw [I.probability_posterior o E ρ hρ, I.probability_posterior o E σ hσ]
  calc
    |(I.branchEffect o E).probability ρ / I.probability ρ o -
        (I.branchEffect o E).probability σ / I.probability σ o| ≤
        (|(I.branchEffect o E).probability ρ - (I.branchEffect o E).probability σ| +
          |I.probability ρ o - I.probability σ o|) / I.probability ρ o :=
      normalized_probability_difference_le _ _ _ _ hρ hσ
        ((I.branchEffect o E).probability_nonneg σ) hbq
    _ ≤ (effectDistance ρ σ + effectDistance ρ σ) / I.probability ρ o :=
      div_le_div_of_nonneg_right
        (add_le_add ((I.branchEffect o E).probability_sub_le_effectDistance ρ σ)
          (I.probability_sub_le_effectDistance o ρ σ)) hρ.le
    _ = 2 * effectDistance ρ σ / I.probability ρ o := by ring

theorem posterior_effectDistance_le_of_probability_lower_bound
    (I : Instrument ι O κ) (o : O) (ρ σ : Density ι)
    (hρ : 0 < I.probability ρ o) (hσ : 0 < I.probability σ o)
    {η : ℝ} (hη : 0 < η) (hηρ : η ≤ I.probability ρ o) :
    effectDistance (I.posterior ρ o hρ) (I.posterior σ o hσ) ≤
      2 * effectDistance ρ σ / η := by
  apply (I.posterior_effectDistance_le o ρ σ hρ hσ).trans
  exact div_le_div_of_nonneg_left
    (mul_nonneg (by norm_num) (effectDistance_nonneg ρ σ)) hη hηρ

end Instrument

/-- The actual chronological sequence of complete Kraus channels. -/
def channelTrajectory (I : ℕ → Instrument ι O κ) (ρ : Density ι) : ℕ → Density ι
  | 0 => ρ
  | n + 1 => (I n).channelState (channelTrajectory I ρ n)

@[simp] theorem channelTrajectory_zero (I : ℕ → Instrument ι O κ) (ρ : Density ι) :
    channelTrajectory I ρ 0 = ρ := rfl

@[simp] theorem channelTrajectory_succ (I : ℕ → Instrument ι O κ) (ρ : Density ι) (n : ℕ) :
    channelTrajectory I ρ (n + 1) = (I n).channelState (channelTrajectory I ρ n) := rfl

/-- The existing Core M-TC certificate now receives an error trace and local
recurrence proved from actual quantum channel definitions. -/
theorem channelTrajectory_transport_certificate {O' κ' : Type*} [Fintype O'] [Fintype κ']
    (I : ℕ → Instrument ι O κ) (J : ℕ → Instrument ι O' κ')
    (ρ σ : Density ι) (n : ℕ) :
    0 ≤ effectDistance (channelTrajectory I ρ n) (channelTrajectory J σ n) ∧
    effectDistance (channelTrajectory I ρ n) (channelTrajectory J σ n) ≤
      Transport.scalarBudget (effectDistance ρ σ) (fun _ => 1)
        (fun t => channelDefect (I t).channelState (J t).channelState) n ∧
    0 ≤ Transport.scalarBudget (effectDistance ρ σ) (fun _ => 1)
      (fun t => channelDefect (I t).channelState (J t).channelState) n := by
  apply Transport.scalar_transport_certificate
    (initial := effectDistance ρ σ)
    (e := fun t => effectDistance (channelTrajectory I ρ t) (channelTrajectory J σ t))
    (L := fun _ => 1)
    (ε := fun t => channelDefect (I t).channelState (J t).channelState)
    (hinitial := effectDistance_nonneg ρ σ)
    (he := fun _ => effectDistance_nonneg _ _)
    (hL := fun _ => by norm_num)
    (hε := fun _ => channelDefect_nonneg _ _)
    (hbase := le_rfl)
  intro t
  simpa only [channelTrajectory_succ, one_mul] using
    (I t).channelState_perturbation_bound (J t) (channelTrajectory I ρ t) (channelTrajectory J σ t)

theorem scalarBudget_one_eq_sum (initial : ℝ) (ε : ℕ → ℝ) (n : ℕ) :
    Transport.scalarBudget initial (fun _ => 1) ε n = initial + ∑ j ∈ Finset.range n, ε j := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Transport.scalarBudget_succ, one_mul, ih, Finset.sum_range_succ, add_assoc]

theorem channelTrajectory_effectDistance_le_sum {O' κ' : Type*} [Fintype O'] [Fintype κ']
    (I : ℕ → Instrument ι O κ) (J : ℕ → Instrument ι O' κ')
    (ρ σ : Density ι) (n : ℕ) :
    effectDistance (channelTrajectory I ρ n) (channelTrajectory J σ n) ≤
      effectDistance ρ σ +
        ∑ j ∈ Finset.range n, channelDefect (I j).channelState (J j).channelState := by
  have h := (channelTrajectory_transport_certificate I J ρ σ n).2.1
  rwa [scalarBudget_one_eq_sum] at h

/-- The transported bound controls every subsequent finite record, with no
finite test collection substituted for the all-effect supremum. -/
theorem channelTrajectory_response_sub_le_sum {O' κ' : Type*} [Fintype O'] [Fintype κ']
    (I : ℕ → Instrument ι O κ) (J : ℕ → Instrument ι O' κ')
    (Q : A → Instrument ι O κ) (ρ σ : Density ι) (n : ℕ) (w : List (A × O)) :
    |response Q (channelTrajectory I ρ n) w - response Q (channelTrajectory J σ n) w| ≤
      effectDistance ρ σ +
        ∑ j ∈ Finset.range n, channelDefect (I j).channelState (J j).channelState :=
  (response_sub_le_effectDistance Q _ _ w).trans (channelTrajectory_effectDistance_le_sum I J ρ σ n)

end

end UEOTQM
