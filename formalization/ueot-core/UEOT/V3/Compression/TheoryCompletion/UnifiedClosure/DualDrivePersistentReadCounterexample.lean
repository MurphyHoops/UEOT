import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveAdaptiveReadCalibration

/-!
Original commitment: replacing independent streams by correlated reads must not silently inherit calibration risk.
Existing result: actual adaptive reader/decoder/select is source-bound; original uniform-prefix Good uses iid latent streams.
Premise tested: each row now repeats ONE fair sign, so per-read marginals alone do not supply independent concentration.
Model/counter: NEW row-persistent common-shock law, SAME sensor/unknown positive diagonal parameters and SAME actual adaptive reader/select.
Consumer: Good has probability0 at every positive prefix, and SAME returned decision has wrong mass>=1/16 for every warmup/budget; no all-correlated no-go.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDrivePersistentReadCounterexample
open MeasureTheory ProbabilityTheory Set
open DualDriveFiniteNoisyCalibration DualDriveAdaptiveReadCalibration VariableRegisteredSamples
open UEOT.V3.BoundedLossSampling UEOT.V3.BoundedLossTwoSided
open scoped BigOperators ENNReal

/-- Four fair shocks, each reused within its own row; indices are still fresh. -/
def repeatRaw {N : ℕ} (z : Raw 1) : Raw N := fun q => z ⟨q.1,0⟩

theorem repeat_prefix {n N : ℕ} (hn : n ≤ N) (z : Raw 1) : prefixRaw hn (repeatRaw z)=repeatRaw z := rfl

theorem mean_repeat (N : ℕ) (hN : 0 < N) (p : Parameters) (z : Raw 1) (j : Row) :
    mean (sourceData p (repeatRaw (N:=N) z)) j=sensor p j (z ⟨j,0⟩) := by
  have hn : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  simp only [mean,sourceData,repeatRaw,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

/-- No positive row prefix lies in original iid Good, for ANY common shock. -/
theorem repeat_not_good (N : ℕ) (hN : 0 < N) (z : Raw 1) : repeatRaw (N:=N) z ∉ Good N := by
  intro h
  have hh := h (0 : Row)
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  cases hz : z ⟨0,0⟩ <;>
    norm_num [empiricalRisk,productRowSample,repeatRaw,bitScore,hz,hn] at hh

noncomputable section

def persistentLaw (N : ℕ) : Measure (Raw N) := (rawLaw 1).map (repeatRaw (N:=N))

instance persistentLaw_probability (N : ℕ) : IsProbabilityMeasure (persistentLaw N) :=
  Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

/-- Every individual unread/read coordinate remains a fair sign; the missing
condition is joint within-row independence, not a changed marginal sensor. -/
theorem persistent_coordinate_law (N : ℕ) (q : Index N) :
    (persistentLaw N).map (fun omega => omega q)=(PMF.uniformOfFintype Bool).toMeasure := by
  rw [persistentLaw,Measure.map_map (measurable_pi_apply q) (measurable_of_finite _)]
  change (rawLaw 1).map (fun z => z ⟨q.1,0⟩)=(PMF.uniformOfFintype Bool).toMeasure
  exact (measurePreserving_eval (fun _ : Index 1 => (PMF.uniformOfFintype Bool).toMeasure) ⟨q.1,0⟩).map_eq

theorem repeat_good_event_empty (N : ℕ) (hN : 0 < N) : {z : Raw 1 | repeatRaw (N:=N) z ∈ Good N}=∅ := by
  ext z
  simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
  exact repeat_not_good N hN z

theorem persistent_good_probability_zero (N : ℕ) (hN : 0 < N) : (persistentLaw N).real (Good N)=0 := by
  rw [persistentLaw,map_measureReal_apply (measurable_of_finite _) ((Set.toFinite (Good N)).measurableSet)]
  change (rawLaw 1).real {z | repeatRaw (N:=N) z ∈ Good N}=0
  rw [repeat_good_event_empty N hN]
  simp

theorem repeat_not_allGood (m K : ℕ) (hm : 0 < m) (z : Raw 1) :
    repeatRaw (N:=m+K) z ∉ AllGood m K := by
  intro hg
  have h := allGood_at m K (repeatRaw (N:=m+K) z) hg m le_rfl (Nat.le_add_right m K)
  rw [repeat_prefix] at h
  exact repeat_not_good m hm z h

theorem persistent_allGood_probability_zero (m K : ℕ) (hm : 0 < m) :
    (rawLaw 1).real {z | repeatRaw (N:=m+K) z ∈ AllGood m K}=0 := by
  have he : {z : Raw 1 | repeatRaw (N:=m+K) z ∈ AllGood m K}=∅ := by
    ext z
    simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
    exact repeat_not_allGood m K hm z
  rw [he]
  simp

end

def fragileParameters : Parameters := ⟨![1,9/100],fun a => if a then 1 else -1⟩
def shockWord : Raw 1 := fun q => q.1=0 || q.1=3

theorem fragile_valid : Valid fragileParameters := by
  constructor
  · intro i; fin_cases i <;> norm_num [fragileParameters]
  · constructor
    · intro a; cases a <;> norm_num [fragileParameters]
    · norm_num [fragileParameters]

/-- SAME old selector; negative measured anchor is legal and produces error.
Increasing N repeats this same observation, not independent evidence. -/
theorem repeat_selects_wrong (N : ℕ) (hN : 0 < N) :
    select (sourceData fragileParameters (repeatRaw (N:=N) shockWord))=some false := by
  have hn : N ≠ 0 := Nat.ne_of_gt hN
  simp only [select,conditioning,estimate]
  simp_rw [mean_repeat N hN]
  norm_num [hn,sensor,trueMean,fragileParameters,shockWord,bit,Fin.ext_iff]

theorem adaptive_repeat_selects_wrong (m K : ℕ) (hm : 0 < m) (route : Router) :
    returned m K route (sourceData fragileParameters (repeatRaw (N:=m+K) shockWord))=some false := by
  have hb := run_minCount_bounds m K route (sourceData fragileParameters (repeatRaw (N:=m+K) shockWord))
  unfold returned
  rw [decoded_source_prefix,repeat_prefix]
  exact repeat_selects_wrong _ (hm.trans_le hb.1)

noncomputable section

theorem shock_mass : (rawLaw 1).real {shockWord}=(1/16 : ℝ) := by
  rw [Measure.real,rawLaw,productRowLaw,Measure.pi_singleton,ENNReal.toReal_prod]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [PMF.uniformOfFintype_apply,Fintype.prod_sigma,Fin.prod_univ_succ]

/-- Under THIS declared correlated source, actual adaptive decision error
has positive mass not decreasing with the number of repeated reads. -/
theorem adaptive_persistent_joint_risk_ge (m K : ℕ) (hm : 0 < m) (route : Router) :
    (1/16 : ℝ) ≤ (rawLaw 1).real {z | ActualWrong m K route fragileParameters (repeatRaw (N:=m+K) z)} := by
  rw [← shock_mass]
  apply measureReal_mono (h₂ := by finiteness)
  intro z hz
  have he : z=shockWord := Set.mem_singleton_iff.mp hz
  subst z
  refine ⟨false,adaptive_repeat_selects_wrong m K hm route,?_⟩
  intro h
  have hh := h true (by decide)
  norm_num [fragileParameters] at hh

end
end DualDrivePersistentReadCounterexample
