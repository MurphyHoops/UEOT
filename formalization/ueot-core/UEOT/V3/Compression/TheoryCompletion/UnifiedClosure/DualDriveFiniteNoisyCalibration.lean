import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveNoisyOperationalCalibration
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples
import UEOT.V3.BoundedLossTwoSided
import Mathlib.Order.Interval.Finset.Fin

/-!
Original gap: C5 source bounds still required deterministic anchor/query error premises.
Actual source: one frozen four-row product, 32 reads per row, all 128 fair signs retained, sensor noise +-1/10.
Premise reduced: derive ONE simultaneous mean-error Good, then bind SAME measured inverse/action to original action-gap consumer.
Models: unknown positive rational diagonal gains and unknown distinct latent action order in [-1,1]; independent unit anchors/evaluation.
Consumer: executable rational inverse/gap reject-or-action, joint Accept-and-Wrong bound8*exp(-4)<1, same-data nonzero-noise witness.

Additional iid/finite bounded mean-zero sensor and independently calibrated
unit-anchor permissions are explicit. No real batch is drawn or replaced, no
old A-F data/thresholds change, and no retry/success filtering is performed.
True parameters, true means/latent order and latent sign flags are absent from
select. Cross coordinates are zero by THIS registered diagonal source class;
this is not arbitrary full-matrix, nonlinear/rank-deficient or dynamic GOA.
The registration/budget is frozen before formal witnesses. For the formal
positive word, row1 has first17 signs true; the other rows first16 true, then
false. No observed outcome was used to choose another word or threshold.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveFiniteNoisyCalibration
open MeasureTheory ProbabilityTheory Filter Topology
open UEOT.V3.BoundedLossSampling UEOT.V3.BoundedLossTwoSided
open VariableRegisteredSamples DualDriveNoisyOperationalCalibration
open scoped BigOperators ENNReal

abbrev Row := Fin 4
abbrev Index (N : ℕ) := SampleCoordinate (fun _ : Row => N)
abbrev Data (N : ℕ) := Index N → ℚ
abbrev Raw (N : ℕ) := Index N → Bool

def registeredBudget : ℕ := 32

def mean {N : ℕ} (data : Data N) (j : Row) : ℚ := (∑ k : Fin N, data ⟨j,k⟩)/(N : ℚ)
def conditioning {N : ℕ} (data : Data N) : ℚ := max |(mean data 0)⁻¹| |(mean data 1)⁻¹|
def estimate {N : ℕ} (data : Data N) (a : Bool) : ℚ := mean data (if a then 3 else 2)/mean data 1

/-- Executable data-only rejection/selection: no truth/mean/source/Good input.
The exact rational diagonal inverse is computed from the SAME observed means. -/
def select {N : ℕ} (data : Data N) : Option Bool :=
  if N=0 ∨ mean data 0=0 ∨ mean data 1=0 then none else
  if (3/10 : ℚ)*conditioning data < estimate data true-estimate data false then some true else
  if (3/10 : ℚ)*conditioning data < estimate data false-estimate data true then some false else none

structure Parameters where
  gain : Fin 2 → ℚ
  latent : Bool → ℚ

/-- Registered physical class, not selector information. -/
def Valid (p : Parameters) : Prop :=
  (∀ i, 0 < p.gain i) ∧ (∀ a, |p.latent a| ≤ 1) ∧ p.latent false ≠ p.latent true

def trueMean (p : Parameters) (j : Row) : ℚ :=
  if j=0 then p.gain 0 else if j=1 then p.gain 1 else
  p.gain 1 * p.latent (decide (j=3))

def bit (b : Bool) : ℚ := if b then 1 else 0
def sensor (p : Parameters) (j : Row) (b : Bool) : ℚ := trueMean p j+(1/10 : ℚ)*(2*bit b-1)
def sourceData {N : ℕ} (p : Parameters) (omega : Raw N) : Data N := fun j => sensor p j.1 (omega j)


/-- Fixed formal population word registered before evaluation: every noise
sign is retained; only row1 is 17/15, all others are16/16. This is not a real draw. -/
def registeredRaw : Raw registeredBudget := fun j => decide ((j.2 : ℕ) < if j.1=1 then 17 else 16)
def regularParameters : Parameters := ⟨fun _ => 2,fun a => if a then 1 else 0⟩
def reverseParameters : Parameters := ⟨fun _ => 2,fun a => if a then 0 else 1⟩

noncomputable section

def rawLaw (N : ℕ) : Measure (Raw N) :=
  productRowLaw (fun _ : Row => PMF.uniformOfFintype Bool) (fun _ => N)
instance rawLaw_probability (N : ℕ) : IsProbabilityMeasure (rawLaw N) := by unfold rawLaw; infer_instance

def observedRow (p : Parameters) (j : Row) : PMF ℚ := (PMF.uniformOfFintype Bool).map (sensor p j)
def observedLaw (p : Parameters) (N : ℕ) : Measure (Data N) := (rawLaw N).map (sourceData p)

/-- SAME complete observed-data law is a genuine row product from the sensor
interpreter, not an externally supplied sampling/independence certificate. -/
theorem observedLaw_product (p : Parameters) (N : ℕ) :
    observedLaw p N=productRowLaw (observedRow p) (fun _ : Row => N) := by
  unfold observedLaw rawLaw productRowLaw sourceData observedRow
  rw [Measure.pi_map_pi (f:=fun (j : Index N) (b : Bool) => sensor p j.1 b)
    (fun j => (measurable_of_finite (sensor p j.1)).aemeasurable)]
  simp_rw [PMF.toMeasure_map _ _ (measurable_of_finite _)]

def bitScore (b : Bool) : ℝ := if b then 1 else 0

def Good (N : ℕ) : Set (Raw N) := {omega | ∀ j : Row,
  |empiricalRisk bitScore (productRowSample (N:=fun _ : Row => N) j) omega-1/2| ≤ 1/4}

private theorem bit_mean : trueRisk (PMF.uniformOfFintype Bool).toMeasure bitScore=(1/2 : ℝ) := by
  unfold trueRisk
  rw [PMF.integral_eq_sum]
  norm_num [Fintype.sum_bool,bitScore,PMF.uniformOfFintype_apply]

/-- Original two-sided Hoeffding plus finite row union. Every coordinate law
and iid fact is proved by the original registered product source. -/
theorem bad_good_probability_le (N : ℕ) (hN : 0 < N) :
    (rawLaw N).real (Good N)ᶜ ≤ 8*Real.exp (-(N : ℝ)/8) := by
  have hrow : ∀ j : Row, (rawLaw N).real {omega |
      (1/4 : ℝ) < |empiricalRisk bitScore (productRowSample (N:=fun _ : Row => N) j) omega-1/2|} ≤
      2*Real.exp (-2*(N : ℝ)*(1/4)^2) := by
    intro j
    have h := measure_empiricalRisk_bad_le hN (rawLaw N) (PMF.uniformOfFintype Bool).toMeasure
      bitScore (measurable_of_finite _) (by intro b; cases b <;> norm_num [bitScore])
      (productRowSample (N:=fun _ : Row => N) j) (fun k => productRowSample_measurable (X:=Bool) (N:=fun _ : Row => N) j k)
      (productRowSample_independent (fun _ : Row => PMF.uniformOfFintype Bool) (fun _ => N) j)
      (fun k => by simpa only [rawLaw] using productRowSample_law (fun _ : Row => PMF.uniformOfFintype Bool) (fun _ => N) j k) (by norm_num : (0 : ℝ) ≤ 1/4)
    simpa only [bit_mean] using h
  have hset : (Good N)ᶜ=⋃ j : Row, {omega |
      (1/4 : ℝ) < |empiricalRisk bitScore (productRowSample (N:=fun _ : Row => N) j) omega-1/2|} := by
    ext omega
    simp [Good]
  rw [hset]
  calc
    _ ≤ ∑ j : Row, (rawLaw N).real {omega |
      (1/4 : ℝ) < |empiricalRisk bitScore (productRowSample (N:=fun _ : Row => N) j) omega-1/2|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : Row, (2*Real.exp (-2*(N : ℝ)*(1/4)^2)) := Finset.sum_le_sum (fun j _ => hrow j)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rw [show -2*(N : ℝ)*(1/4)^2= -(N : ℝ)/8 by ring]
      ring

private theorem bit_average_real {N : ℕ} (omega : Raw N) (j : Row) :
    (mean (fun k => bit (omega k)) j : ℝ)=
      empiricalRisk bitScore (productRowSample (N:=fun _ : Row => N) j) omega := by
  unfold mean empiricalRisk productRowSample bit bitScore
  push_cast
  apply congrArg (fun x : ℝ => x/(N : ℝ))
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> norm_num

private theorem mean_sensor {N : ℕ} (p : Parameters) (omega : Raw N) (j : Row) (hN : 0 < N) :
    mean (sourceData p omega) j=trueMean p j+(1/10 : ℚ)*(2*mean (fun k => bit (omega k)) j-1) := by
  have hq : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hs : (∑ k : Fin N, sensor p j (omega ⟨j,k⟩))=
      (N : ℚ)*trueMean p j+(1/10 : ℚ)*(2*(∑ k : Fin N, bit (omega ⟨j,k⟩))-(N : ℚ)) := by
    calc
      _ = ∑ k : Fin N, (trueMean p j-1/10+(1/5 : ℚ)*bit (omega ⟨j,k⟩)) := by
        apply Finset.sum_congr rfl
        intro k _
        unfold sensor
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum]
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
  change (∑ k : Fin N, sensor p j (omega ⟨j,k⟩))/(N : ℚ)=_
  rw [hs]
  unfold mean
  field_simp [hq]

/-- ONE actual product Good supplies ALL deterministic anchor/query mean
errors for the SAME data. True means are proof parameters, never selector inputs. -/
theorem good_mean_errors {N : ℕ} (p : Parameters) (omega : Raw N) (hN : 0 < N) (hg : omega ∈ Good N) (j : Row) :
    |(mean (sourceData p omega) j : ℝ)-(trueMean p j : ℝ)| ≤ (1/20 : ℝ) := by
  have hm := mean_sensor p omega j hN
  have hmR := congrArg (fun q : ℚ => (q : ℝ)) hm
  push_cast at hmR
  rw [hmR]
  have hb := (hg j)
  rw [← bit_average_real omega j] at hb
  have heq : (trueMean p j : ℝ)+(1/10 : ℝ)*(2*(mean (fun k => bit (omega k)) j : ℝ)-1)-(trueMean p j : ℝ)=
      (1/5 : ℝ)*((mean (fun k => bit (omega k)) j : ℝ)-1/2) := by ring
  rw [heq,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 1/5)]
  nlinarith


/-- Noise is genuinely mean-zero and bounded for every unknown source mean. -/
theorem sensor_centered_mean (p : Parameters) (j : Row) :
    trueRisk (PMF.uniformOfFintype Bool).toMeasure (fun b => ((sensor p j b-trueMean p j : ℚ) : ℝ))=0 := by
  unfold trueRisk
  rw [PMF.integral_eq_sum]
  norm_num [Fintype.sum_bool,sensor,bit,PMF.uniformOfFintype_apply]

theorem sensor_noise_size (p : Parameters) (j : Row) (b : Bool) :
    |sensor p j b-trueMean p j|=(1/10 : ℚ) := by
  cases b <;> norm_num [sensor,bit]

/-- Acceptance supplies exact nonzero measured diagonals and an OBSERVED
rational gap. No source value or true order is queried by select. -/
theorem select_spec {N : ℕ} (data : Data N) (chosen : Bool) (hs : select data=some chosen) :
    N ≠ 0 ∧ mean data 0 ≠ 0 ∧ mean data 1 ≠ 0 ∧
      (3/10 : ℚ)*conditioning data < estimate data chosen-estimate data (!chosen) := by
  by_cases hb : N=0 ∨ mean data 0=0 ∨ mean data 1=0
  · simp [select,hb] at hs
  · refine ⟨(not_or.mp hb).1,(not_or.mp (not_or.mp hb).2).1,(not_or.mp (not_or.mp hb).2).2,?_⟩
    by_cases ht : (3/10 : ℚ)*conditioning data < estimate data true-estimate data false
    · have hc : chosen=true := by simpa [select,hb,ht] using hs.symm
      subst chosen
      exact ht
    · by_cases hf : (3/10 : ℚ)*conditioning data < estimate data false-estimate data true
      · have hc : chosen=false := by simpa [select,hb,ht,hf] using hs.symm
        subst chosen
        exact hf
      · simp [select,hb,ht,hf] at hs

theorem conditioning_nonneg {N : ℕ} (data : Data N) : 0 ≤ conditioning data :=
  (abs_nonneg _).trans (le_max_left _ _)

def sourceDecoder (p : Parameters) : Coordinate 2 →L[ℝ] Coordinate 2 := diagonal (fun i => (p.gain i : ℝ))
def actionInput (p : Parameters) (a : Bool) : Coordinate 2 := (p.latent a : ℝ) • unit 1

def measuredMatrix {N : ℕ} (data : Data N) : Coordinate 2 →L[ℝ] Coordinate 2 :=
  diagonal (fun i => (mean data (if i=0 then 0 else 1) : ℝ))
def measuredSamples {N : ℕ} (data : Data N) (i : Fin 2) : Coordinate 2 := measuredMatrix data (unit i)
/-- Native inverse coefficients are EXACT rational reciprocals of sample means. -/
def computedInverse {N : ℕ} (data : Data N) : Coordinate 2 →L[ℝ] Coordinate 2 :=
  diagonal (fun i => ((mean data (if i=0 then 0 else 1))⁻¹ : ℚ))
def measuredQueries {N : ℕ} (data : Data N) (a : Bool) : Coordinate 2 :=
  (mean data (if a then 3 else 2) : ℝ) • unit 1

theorem computed_inverse_left {N : ℕ} (data : Data N) (h0 : mean data 0 ≠ 0) (h1 : mean data 1 ≠ 0) (z : Coordinate 2) :
    computedInverse data (columns (measuredSamples data) z)=z := by
  have hr0 : (mean data 0 : ℝ) ≠ 0 := by exact_mod_cast h0
  have hr1 : (mean data 1 : ℝ) ≠ 0 := by exact_mod_cast h1
  change computedInverse data (columns (fun i => measuredMatrix data (unit i)) z)=z
  rw [columns_of_map]
  ext i
  fin_cases i <;> simp [computedInverse,measuredMatrix,diagonal_apply,hr0,hr1]

theorem computed_inverse_right {N : ℕ} (data : Data N) (h0 : mean data 0 ≠ 0) (h1 : mean data 1 ≠ 0) (z : Coordinate 2) :
    columns (measuredSamples data) (computedInverse data z)=z := by
  have hr0 : (mean data 0 : ℝ) ≠ 0 := by exact_mod_cast h0
  have hr1 : (mean data 1 : ℝ) ≠ 0 := by exact_mod_cast h1
  change columns (fun i => measuredMatrix data (unit i)) (computedInverse data z)=z
  rw [columns_of_map]
  ext i
  fin_cases i <;> simp [computedInverse,measuredMatrix,diagonal_apply,hr0,hr1]

/-- Exact native same-data inverse; singular data are rejected by select. -/
def dataChecked {N : ℕ} (data : Data N) (h0 : mean data 0 ≠ 0) (h1 : mean data 1 ≠ 0) : Coordinate 2 ≃L[ℝ] Coordinate 2 :=
  checkedMeasuredEquiv (measuredSamples data) (computedInverse data)
    (computed_inverse_left data h0 h1) (computed_inverse_right data h0 h1)

theorem computed_inverse_norm_le {N : ℕ} (data : Data N) : ‖computedInverse data‖ ≤ (conditioning data : ℝ) := by
  apply diagonal_norm_le _ _ (by exact_mod_cast conditioning_nonneg data)
  intro i
  fin_cases i
  · exact_mod_cast (le_max_left |(mean data 0)⁻¹| |(mean data 1)⁻¹|)
  · exact_mod_cast (le_max_right |(mean data 0)⁻¹| |(mean data 1)⁻¹|)

/-- Actual reconstructed evaluation equals the selector's literal rational score. -/
theorem estimated_score_eq {N : ℕ} (data : Data N) (a : Bool) :
    regularEvaluation (encoderEstimate regularBasis (computedInverse data) (measuredQueries data a))=(estimate data a : ℝ) := by
  cases a <;>
    simp [regularEvaluation,encoderEstimate,coefficients,regularBasis,computedInverse,measuredQueries,unit,estimate,div_eq_mul_inv,mul_comm]

theorem source_evaluation_eq (p : Parameters) (a : Bool) :
    regularEvaluation (regularEncoder (actionInput p a))=(p.latent a : ℝ) := by
  simp [regularEvaluation,regularEncoder,actionInput,unit]

private theorem actual_query_source (p : Parameters) (a : Bool) :
    sourceDecoder p (regularEncoder (actionInput p a))=(trueMean p (if a then 3 else 2) : ℝ) • unit 1 := by
  cases a <;>
    simp [sourceDecoder,regularEncoder,actionInput,map_smul,diagonal_unit,trueMean,smul_smul,mul_comm]

/-- Each mean error is consumed by the actual SAME calibrated anchor column. -/
theorem good_anchor_error {N : ℕ} (p : Parameters) (omega : Raw N) (hN : 0 < N) (hg : omega ∈ Good N) (i : Fin 2) :
    ‖measuredSamples (sourceData p omega) i-sourceDecoder p (regularEncoder (unit i))‖ ≤ (1/20 : ℝ) := by
  change ‖measuredMatrix (sourceData p omega) (unit i)-sourceDecoder p (unit i)‖ ≤ (1/20 : ℝ)
  rw [measuredMatrix,sourceDecoder,diagonal_unit,diagonal_unit,← sub_smul,norm_smul,norm_unit,mul_one,Real.norm_eq_abs]
  fin_cases i
  · simpa [trueMean] using good_mean_errors p omega hN hg 0
  · simpa [trueMean] using good_mean_errors p omega hN hg 1

theorem good_query_error {N : ℕ} (p : Parameters) (omega : Raw N) (hN : 0 < N) (hg : omega ∈ Good N) (a : Bool) :
    ‖measuredQueries (sourceData p omega) a-sourceDecoder p (regularEncoder (actionInput p a))‖ ≤ (1/20 : ℝ) := by
  rw [actual_query_source,measuredQueries,← sub_smul,norm_smul,norm_unit,mul_one,Real.norm_eq_abs]
  exact good_mean_errors p omega hN hg (if a then 3 else 2)

theorem valid_action_domain (p : Parameters) (hp : Valid p) (a : Bool) :
    ‖regularBasis.symm (regularEncoder (actionInput p a))‖ ≤ (1 : ℝ) := by
  have h : |(p.latent a : ℝ)| ≤ 1 := by exact_mod_cast hp.2.1 a
  change ‖(p.latent a : ℝ) • unit (1 : Fin 2)‖ ≤ 1
  rw [norm_smul,norm_unit,mul_one,Real.norm_eq_abs]
  exact h


/-- True source is nondegenerate in the registered family; no numeric rank
criterion is used, and its true gain is not a selector input. -/
theorem valid_source_nondegenerate (p : Parameters) (hp : Valid p) : Function.Bijective (sourceDecoder p) := by
  have hc : ∀ i : Fin 2, (p.gain i : ℝ) ≠ 0 := fun i => by exact_mod_cast ne_of_gt (hp.1 i)
  let E := (driveAxisScaling (fun i => (p.gain i : ℝ)) hc).toContinuousLinearEquiv
  have he : sourceDecoder p=E.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro z
    ext i
    simp [sourceDecoder,E,diagonal_apply,driveAxisScaling]
  rw [he]
  simpa using E.bijective

theorem valid_distinct_inputs (p : Parameters) (hp : Valid p) : actionInput p false ≠ actionInput p true := by
  intro h
  have hh := congrFun h 1
  have hu : (p.latent false : ℝ)=(p.latent true : ℝ) := by simpa [actionInput,unit] using hh
  exact hp.2.2 (by exact_mod_cast hu)

/-- Observable conditioning computes the SAME radius used by rational select. -/
theorem measured_radius_le {N : ℕ} (data : Data N) :
    ‖regularEvaluation‖*‖regularBasis.toContinuousLinearMap‖*‖computedInverse data‖*
      ((1/20 : ℝ)+(2 : ℝ)*(1/20)*1) ≤ (3/20 : ℝ)*(conditioning data : ℝ) := by
  have he : ‖regularEvaluation‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro z
    simpa [regularEvaluation] using norm_le_pi_norm z (1 : Fin 2)
  have hb : ‖regularBasis.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro z
    simp [regularBasis]
  have hi := computed_inverse_norm_le data
  have hk : (0 : ℝ) ≤ conditioning data := by exact_mod_cast conditioning_nonneg data
  calc
    _ ≤ 1*1*(conditioning data : ℝ)*((1/20 : ℝ)+(2 : ℝ)*(1/20)*1) := by gcongr
    _ = _ := by ring

/-- Actual source-calibrated measured means, SAME computed inverse and SAME
returned action consume the original action-gap theorem. No error/goodness
certificate or true ordering is an input of the executable selector. -/
theorem good_selected_action_correct {N : ℕ} (p : Parameters) (hp : Valid p) (omega : Raw N)
    (hN : 0 < N) (hg : omega ∈ Good N) (chosen : Bool) (hs : select (sourceData p omega)=some chosen) :
    ∀ a : Bool, a ≠ chosen → p.latent a < p.latent chosen := by
  let data := sourceData p omega
  have hspec := select_spec data chosen hs
  have hgapR : (3/10 : ℝ)*(conditioning data : ℝ) < (estimate data chosen : ℝ)-(estimate data (!chosen) : ℝ) := by
    have hh : (((3/10 : ℚ)*conditioning data : ℚ) : ℝ) <
        ((estimate data chosen-estimate data (!chosen) : ℚ) : ℝ) := by exact_mod_cast hspec.2.2.2
    push_cast at hh
    exact hh
  have h := actual_action_gap regularEncoder (sourceDecoder p) regularBasis (@unit 2) (fun _ => rfl)
    (measuredSamples data) (1/20) (by norm_num) (good_anchor_error p omega hN hg)
    (actionInput p) (measuredQueries data) regularEvaluation (computedInverse data)
    (computed_inverse_left data hspec.2.1 hspec.2.2.1) (1/20) 1
    (good_query_error p omega hN hg) (valid_action_domain p hp) chosen (by
      intro a ha
      have heq : a= !chosen := by cases a <;> cases chosen <;> simp_all
      subst a
      rw [estimated_score_eq,estimated_score_eq]
      linarith [measured_radius_le data])
  intro a ha
  have hr : (p.latent a : ℝ)<(p.latent chosen : ℝ) := by simpa only [source_evaluation_eq] using h a ha
  exact_mod_cast hr

def AcceptWrong {N : ℕ} (p : Parameters) (data : Data N) : Prop :=
  ∃ chosen : Bool, select data=some chosen ∧ ¬ ∀ a : Bool, a ≠ chosen → p.latent a < p.latent chosen

/-- Joint acceptance AND wrong ranking, over the complete registered raw
source. Rejected runs remain in the measure; this is NOT P(Wrong|Accept). -/
theorem accept_wrong_probability_le (p : Parameters) (hp : Valid p) (N : ℕ) (hN : 0 < N) :
    (rawLaw N).real {omega | AcceptWrong p (sourceData p omega)} ≤ 8*Real.exp (-(N : ℝ)/8) := by
  apply (measureReal_mono ?_).trans (bad_good_probability_le N hN)
  intro omega herr hg
  obtain ⟨chosen,hs,hbad⟩ := herr
  exact hbad (good_selected_action_correct p hp omega hN hg chosen hs)

/-- Frozen budget is32 per each of four registered rows; no post-data change. -/
theorem registered_joint_risk_le (p : Parameters) (hp : Valid p) :
    (rawLaw registeredBudget).real {omega | AcceptWrong p (sourceData p omega)} ≤ 8*Real.exp (-4) := by
  have h := accept_wrong_probability_le p hp registeredBudget (by decide)
  norm_num [registeredBudget] at h
  exact h

theorem registered_bound_nonvacuous : 8*Real.exp (-4 : ℝ) < 1 := by
  have he2 : (3 : ℝ)<Real.exp 2 := by
    have h := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
    linarith
  have he4 : (8 : ℝ)<Real.exp 4 := by
    rw [show (4 : ℝ)=2+2 by norm_num,Real.exp_add]
    nlinarith
  rw [Real.exp_neg,← div_eq_mul_inv]
  exact (div_lt_one (Real.exp_pos 4)).mpr he4


private theorem prefix_card (k : Fin 32) :
    (Finset.univ.filter (fun x : Fin 32 => (x : ℕ)<(k : ℕ))).card=(k : ℕ) := by
  have heq : Finset.univ.filter (fun x : Fin 32 => (x : ℕ)<(k : ℕ))=Finset.Iio k := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio,Fin.lt_def]
  rw [heq,Fin.card_Iio]

/-- Formal word is the immutable preregistered full128-sign batch. Exact
counts are computed from that word, not inserted as an estimated answer. -/
theorem registered_bit_means (j : Row) :
    mean (fun k => bit (registeredRaw k)) j=(if j=1 then (17/32 : ℚ) else 1/2) := by
  have h17 : (Finset.univ.filter (fun x : Fin 32 => (x : ℕ)<17)).card=17 := prefix_card 17
  have h16 : (Finset.univ.filter (fun x : Fin 32 => (x : ℕ)<16)).card=16 := prefix_card 16
  unfold mean registeredRaw
  by_cases hj : j=1
  · simp only [hj,ite_true]
    norm_num [registeredBudget,Fin.sum_univ_succ,bit]
    exact_mod_cast h17
  · simp only [hj,ite_false]
    norm_num [registeredBudget,Fin.sum_univ_succ,bit]
    apply (div_eq_iff (by norm_num : (32 : ℚ) ≠ 0)).mpr
    norm_num
    exact_mod_cast h16

theorem registered_means (p : Parameters) (j : Row) :
    mean (sourceData p registeredRaw) j=trueMean p j+(if j=1 then (1/160 : ℚ) else 0) := by
  rw [mean_sensor p registeredRaw j (by decide),registered_bit_means]
  by_cases h : j=1 <;> norm_num [h]

theorem registered_good : registeredRaw ∈ Good registeredBudget := by
  intro j
  rw [← bit_average_real registeredRaw j,registered_bit_means]
  by_cases h : j=1 <;> norm_num [h]

theorem regular_valid : Valid regularParameters := by
  refine ⟨?_,?_,?_⟩
  · intro i; norm_num [regularParameters]
  · intro a; cases a <;> norm_num [regularParameters]
  · norm_num [regularParameters]

theorem reverse_valid : Valid reverseParameters := by
  refine ⟨?_,?_,?_⟩
  · intro i; norm_num [reverseParameters]
  · intro a; cases a <;> norm_num [reverseParameters]
  · norm_num [reverseParameters]

/-- SAME raw word and SAME unknown-source protocol, with positive regular
parameters. Actual means/reciprocals/gap are computed from observed data. -/
theorem registered_regular_output :
    select (sourceData regularParameters registeredRaw)=some true ∧
    mean (sourceData regularParameters registeredRaw) 0=2 ∧
    mean (sourceData regularParameters registeredRaw) 1=321/160 ∧
    (mean (sourceData regularParameters registeredRaw) 0)⁻¹=1/2 ∧
    (mean (sourceData regularParameters registeredRaw) 1)⁻¹=160/321 ∧
    estimate (sourceData regularParameters registeredRaw) true=320/321 := by
  norm_num [select,conditioning,estimate,registered_means,registeredBudget,trueMean,regularParameters,Fin.ext_iff]

/-- Reverse legal parameters change the actual observed query data under the
SAME registered signword/protocol. The selector changes its returned action;
this is NOT identical observed data supporting opposite true ranks. -/
theorem registered_reverse_output : select (sourceData reverseParameters registeredRaw)=some false := by
  norm_num [select,conditioning,estimate,registered_means,registeredBudget,trueMean,reverseParameters,Fin.ext_iff]

/-- SAME actual accepted regular artifact consumes source-derived Good and
original action-gap endpoint; the selector does not read the true order. -/
theorem registered_regular_action_correct : regularParameters.latent false < regularParameters.latent true :=
  good_selected_action_correct regularParameters regular_valid registeredRaw (by decide)
    registered_good true registered_regular_output.1 false (by decide)

theorem registered_reverse_action_correct : reverseParameters.latent true < reverseParameters.latent false :=
  good_selected_action_correct reverseParameters reverse_valid registeredRaw (by decide)
    registered_good false registered_reverse_output true (by decide)

/-- Complete formal word really has positive mass in the ORIGINAL registered
source. It is a witness within that law, not the law conditioned on this word. -/
theorem registered_word_mass : (rawLaw registeredBudget).real {registeredRaw}=(1/2 : ℝ)^128 := by
  rw [Measure.real,rawLaw,productRowLaw,Measure.pi_singleton,ENNReal.toReal_prod]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [PMF.uniformOfFintype_apply,Fintype.prod_sigma,Finset.prod_const,registeredBudget]

theorem registered_word_positive_mass : 0 < (rawLaw registeredBudget).real {registeredRaw} := by
  rw [registered_word_mass]
  positivity

@[simp] theorem zero_budget_reject (data : Data 0) : select data=none := rfl

theorem singular_data_reject {N : ℕ} (data : Data N) (h : mean data 0=0 ∨ mean data 1=0) : select data=none := by
  have hb : N=0 ∨ mean data 0=0 ∨ mean data 1=0 := Or.inr h
  simp [select,hb]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveFiniteNoisyCalibration
