import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionRegret
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismTableLaw

/-!
# Full-history real kernels have the same fixed-mechanism decision values

The finite response-table law is only a mathematical realization of the old
arbitrary-memory real causal kernel. It is sampled without any mechanism or
world argument, and the same law preserves BOTH S and G values. Positive-mass
sampled tables inherit supported-only legality. This closes the comparison-class
connection used by the attained minimax certificate; no policy enumeration is
performed by the executable H3 consumer.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionRealization

open scoped BigOperators
open RegisterJointDecisionSource (Act Obs Noise)
open RegisterMechanismDecisionSource RegisterMechanismDecisionConsumer
open RegisterMechanismDecisionRegret RegisterMechanismTableLaw
open FiniteJointDecisionBelief FiniteJointDecisionSolver
open FiniteJointDecisionFilteredModel FiniteJointDecisionSupportedPolicy

private noncomputable def average {X : Type*} [Fintype X] (p : PMF X) (f : X → ℝ) : ℝ :=
  ∑ x, (p x).toReal * f x

private theorem real_total {X : Type*} [Fintype X] (p : PMF X) :
    (∑ x, (p x).toReal) = 1 := by
  have h := congrArg ENNReal.toReal (PMF.tsum_coe p)
  rw [tsum_fintype, ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top p x)] at h
  simpa using h

private theorem average_pure {X : Type*} [Fintype X] (x : X) (f : X → ℝ) :
    average (PMF.pure x) f = f x := by
  classical
  simp [average, PMF.pure_apply]

private theorem average_const {X : Type*} [Fintype X] (p : PMF X) (c : ℝ) :
    average p (fun _ => c) = c := by
  rw [average, ← Finset.sum_mul, real_total, one_mul]

private theorem average_add {X : Type*} [Fintype X] (p : PMF X) (f g : X → ℝ) :
    average p (fun x => f x + g x) = average p f + average p g := by
  simp [average, mul_add, Finset.sum_add_distrib]

private theorem average_mul {X : Type*} [Fintype X] (p : PMF X) (c : ℝ) (f : X → ℝ) :
    average p (fun x => c * f x) = c * average p f := by
  simp only [average, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem average_sum {X Y : Type*} [Fintype X] [Fintype Y]
    (p : PMF X) (f : Y → X → ℝ) :
    average p (fun x => ∑ y, f y x) = ∑ y, average p (f y) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem average_bind {X Y : Type*} [Fintype X] [Fintype Y]
    (p : PMF X) (q : X → PMF Y) (f : Y → ℝ) :
    average (p.bind q) f = average p (fun x => average (q x) f) := by
  have hb (y : Y) : ((p.bind q) y).toReal = ∑ x, (p x).toReal * (q x y).toReal := by
    rw [PMF.bind_apply, tsum_fintype,
      ENNReal.toReal_sum (fun x _ => ENNReal.mul_ne_top (PMF.apply_ne_top p x) (PMF.apply_ne_top (q x) y))]
    simp only [ENNReal.toReal_mul]
  unfold average
  simp_rw [hb, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

private theorem average_map {X Y : Type*} [Fintype X] [Fintype Y]
    (p : PMF X) (f : X → Y) (g : Y → ℝ) :
    average (p.map f) g = average p (fun x => g (f x)) := by
  change average (p.bind (fun x => PMF.pure (f x))) g = _
  rw [average_bind]
  simp only [average_pure]

private theorem average_sampleChildren {T : Type*} [Fintype T]
    (p : Obs → PMF T) (o : Obs) (f : T → ℝ) :
    average (sampleChildren p) (fun cs => f (cs o)) = average (p o) f := by
  calc
    _ = average ((sampleChildren p).map (fun cs => cs o)) f :=
      (average_map (sampleChildren p) (fun cs => cs o) f).symm
    _ = average (p o) f := by rw [sampleChildren_map]

/-- Value realization for arbitrary memory and real action probabilities, on
EVERY actual hidden world. No known-mechanism or feasibility premise is needed
for this identity; legality is transported separately below. -/
 theorem sampled_source_value (pi : RawCausalPolicy (model parameters)) :
    ∀ H (h : pi.Memory) (w : World),
      (∑ t : Table Act Obs H, (sampleTable pi H h t).toReal *
        (sourceValue (source parameters) (gain parameters) parameters.discount t w : ℝ)) =
      rawSourceValue (source parameters) (gain parameters) parameters.discount pi H h w := by
  intro H
  induction H with
  | zero =>
      intro h w
      change average (sampleTable pi 0 h) (fun t =>
        (sourceValue (source parameters) (gain parameters) parameters.discount t w : ℝ)) = _
      rw [sampleTable, average_pure]
      rfl
  | succ H ih =>
      intro h w
      change average (sampleTable pi (H+1) h) (fun t =>
        (sourceValue (source parameters) (gain parameters) parameters.discount t w : ℝ)) = _
      rw [sampleTable, average_bind, rawSourceValue]
      simp_rw [average_map]
      change (∑ a, (actionLaw pi h a).toReal *
        average (sampleChildren (fun o => sampleTable pi H (pi.advance h a o)))
          (fun cs => (sourceValue (source parameters) (gain parameters)
            parameters.discount (.node a cs) w : ℝ))) = _
      simp only [actionLaw_toReal]
      apply Finset.sum_congr rfl
      intro a _
      apply congrArg (fun v : ℝ => pi.actionProb h a * v)
      simp only [sourceValue, Rat.cast_sum, Rat.cast_mul, Rat.cast_add]
      rw [average_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [average_mul, average_add, average_const, average_mul, average_sampleChildren]
      have ht := ih (pi.advance h a ((source parameters).observe w a z))
        ((source parameters).next w a z)
      exact congrArg (fun v : ℝ => ((source parameters).chance w z : ℝ) *
        ((gain parameters a ((source parameters).observe w a z) : ℝ) +
          (parameters.discount : ℝ) * v)) ht

/-- Reindex the original full-history experiment as one finite private law.
Its seed distribution and every table are shared across the fixed mechanisms. -/
noncomputable def realize (pi : RawCausalPolicy (model parameters)) (h : pi.Memory)
    (hi : pi.info h = registeredInfo .dual)
    (hl : SupportedAdmissible (model parameters) pi 3 h) : MixedPolicy where
  Seed := Table Act Obs 3
  seeds := tableFintype 3
  weight := fun t => (sampleTable pi 3 h t).toReal
  nonneg := fun _ => ENNReal.toReal_nonneg
  total := real_total _
  table := id
  legal := by
    intro t ht
    rw [← hi]
    apply sampleTable_supported pi 3 h t hl
    apply PMF.mem_support_iff.mpr
    intro hz
    exact ht (by rw [hz]; simp)

 theorem realize_values (pi : RawCausalPolicy (model parameters)) (h : pi.Memory)
    (hi : pi.info h = registeredInfo .dual)
    (hl : SupportedAdmissible (model parameters) pi 3 h) (m : FaultMechanism) :
    mixedJ (realize pi h hi hl) m = actualJ pi h m :=
  sampled_source_value pi 3 h (initialWorld parameters.goal m)

/-- The same finite law realizes both actual mechanism values, not merely a
weighted Bayes number. It preserves the entire payoff comparison used by regret. -/
 theorem every_raw_has_shared_realization (pi : RawCausalPolicy (model parameters)) (h : pi.Memory)
    (hi : pi.info h = registeredInfo .dual)
    (hl : SupportedAdmissible (model parameters) pi 3 h) :
    ∃ p : MixedPolicy, ∀ m, mixedJ p m = actualJ pi h m :=
  ⟨realize pi h hi hl, realize_values pi h hi hl⟩

/-- Explicit all-raw comparison with the actual private-randomized return.
Together with minimax_regret_exact, no alternative real full-history kernel is
excluded by the finite-law presentation of the attained optimum. -/
 theorem returned_beats_every_raw_regret (pi : RawCausalPolicy (model parameters)) (h : pi.Memory)
    (hi : pi.info h = registeredInfo .dual)
    (hl : SupportedAdmissible (model parameters) pi 3 h) :
    FiniteMechanismRegretCertificate.worst oracle (mixedJ rho) ≤
      FiniteMechanismRegretCertificate.worst oracle (actualJ pi h) := by
  rw [rho_worst]
  exact all_shared_regret_lower pi h hi hl

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionRealization
