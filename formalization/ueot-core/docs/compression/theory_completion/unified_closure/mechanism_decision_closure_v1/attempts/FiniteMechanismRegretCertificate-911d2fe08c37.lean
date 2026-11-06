import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSupportedPolicy

/-!
# A finite fixed-mechanism regret certificate

The mechanism is chosen once and is not allowed to depend on a controller's
private random seed. `J p m` is the whole-run value of ONE shared policy `p` in
mechanism `m`, with the same information, wallet, horizon and evaluation.
Weights below are a lower-bound witness, not an assertion about nature's prior.
The source consumer proves the oracle and weighted-value bounds separately.
No minimax solver, compactness or unproved attainment claim is introduced.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMechanismRegretCertificate

open scoped BigOperators

variable {M : Type*} [Fintype M] [Nonempty M]

noncomputable def worst (oracle J : M → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun m => oracle m - J m)

 theorem regret_le_worst (oracle J : M → ℝ) (m : M) :
    oracle m - J m ≤ worst oracle J :=
  Finset.le_sup' _ (Finset.mem_univ m)

 theorem worst_le (oracle J : M → ℝ) (u : ℝ)
    (h : ∀ m, oracle m - J m ≤ u) : worst oracle J ≤ u := by
  apply Finset.sup'_le
  intro m _
  exact h m

 theorem weighted_regret_le (oracle J w : M → ℝ)
    (hn : ∀ m, 0 ≤ w m) (ht : ∑ m, w m = 1) :
    (∑ m, w m * (oracle m - J m)) ≤ worst oracle J := by
  calc
    _ ≤ ∑ m, w m * worst oracle J :=
      Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left
        (regret_le_worst oracle J m) (hn m)
    _ = worst oracle J := by rw [← Finset.sum_mul, ht, one_mul]

/-- A weighted all-policy Bayes upper bound is a worst-regret lower bound.
Its hypothesis is discharged by the existing full-history source theorem in
the concrete S/G consumer, not by comparing its two proposed components. -/
 theorem lower_bound (oracle J w : M → ℝ) (bayes : ℝ)
    (hn : ∀ m, 0 ≤ w m) (ht : ∑ m, w m = 1)
    (hb : (∑ m, w m * J m) ≤ bayes) :
    (∑ m, w m * oracle m) - bayes ≤ worst oracle J := by
  have hw := weighted_regret_le oracle J w hn ht
  have heq : (∑ m, w m * (oracle m - J m)) =
      (∑ m, w m * oracle m) - (∑ m, w m * J m) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [heq] at hw
  linarith

noncomputable def minimax {Policy : Type*} (oracle : M → ℝ)
    (J : Policy → M → ℝ) : ℝ := sInf (Set.range (fun p => worst oracle (J p)))

/-- The lower/upper interval for an arbitrary nonempty shared policy class.
Only the displayed attaining candidate is needed to prove the upper bound. -/
 theorem certificate {Policy : Type*} (oracle w : M → ℝ)
    (J : Policy → M → ℝ) (bayes : ℝ) (rho : Policy)
    (hn : ∀ m, 0 ≤ w m) (ht : ∑ m, w m = 1)
    (hb : ∀ p, (∑ m, w m * J p m) ≤ bayes) :
    (∑ m, w m * oracle m) - bayes ≤ minimax oracle J ∧
      minimax oracle J ≤ worst oracle (J rho) := by
  have hl (p : Policy) : (∑ m, w m * oracle m) - bayes ≤ worst oracle (J p) :=
    lower_bound oracle (J p) w bayes hn ht (hb p)
  have hbdd : BddBelow (Set.range (fun p => worst oracle (J p))) := by
    refine ⟨(∑ m, w m * oracle m) - bayes, ?_⟩
    rintro y ⟨p, rfl⟩
    exact hl p
  have hne : (Set.range (fun p => worst oracle (J p))).Nonempty := ⟨_, rho, rfl⟩
  constructor
  · apply le_csInf hne
    rintro y ⟨p, rfl⟩
    exact hl p
  · exact csInf_le hbdd ⟨rho, rfl⟩

/-- Matching source-derived bounds certify THIS returned policy and the infimum
simultaneously. This is an explicit attained result, not an abstract existence
claim for an unspecified optimizer. -/
 theorem matched_certificate {Policy : Type*} (oracle w : M → ℝ)
    (J : Policy → M → ℝ) (bayes target : ℝ) (rho : Policy)
    (hn : ∀ m, 0 ≤ w m) (ht : ∑ m, w m = 1)
    (hb : ∀ p, (∑ m, w m * J p m) ≤ bayes)
    (hl : (∑ m, w m * oracle m) - bayes = target)
    (hu : worst oracle (J rho) = target) :
    minimax oracle J = target ∧ worst oracle (J rho) = target := by
  have h := certificate oracle w J bayes rho hn ht hb
  rw [hl, hu] at h
  exact ⟨le_antisymm h.2 h.1, hu⟩

/-- This iff concerns a specified shared policy. It does not assert that a
zero infimum over a general policy class must be attained. -/
 theorem worst_zero_iff (oracle J : M → ℝ) (hu : ∀ m, J m ≤ oracle m) :
    worst oracle J = 0 ↔ ∀ m, J m = oracle m := by
  constructor
  · intro h m
    have hm := regret_le_worst oracle J m
    rw [h] at hm
    linarith [hu m]
  · intro h
    apply le_antisymm
    · exact worst_le oracle J 0 (fun m => by rw [h m]; simp)
    · let m : M := Classical.choice inferInstance
      simpa [h m] using regret_le_worst oracle J m

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMechanismRegretCertificate
