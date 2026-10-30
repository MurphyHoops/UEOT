import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepShiftedSource

/-!
Original commitment: each actual finite prefix must supply the Brownian source used by the next action.
Existing result: native Gaussian fiber Esscher permits any actual base measure, but the old full-path proof fixed the initial source.
Premise reduced: expose that same full finite-path derivation for an actually proved measured Brownian source and its own natural past.
Model/witness: real Brownian B on P, measurable coordinates, one real coefficient H from the whole natural START past; same-time allowed.
Consumer: actual finite-prefix Q/B induction; this lemma does not assume a desired shifted-law or an abstract Girsanov certificate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianMeasuredStepTransport
open MeasureTheory ProbabilityTheory Set Filter
open BrownianPastStepGaussianResidualSource BrownianPastStepTiltKernelSource BrownianGaussianTiltSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def natural (B : ℝ≥0 → Ω → ℝ) (hB : ∀ t, Measurable (B t)) :=
  Filtration.natural B (fun t => (hB t).stronglyMeasurable)
def inc (B : ℝ≥0 → Ω → ℝ) (a b : ℝ≥0) (ω : Ω) : ℝ := B b ω-B a ω
def resid (B : ℝ≥0 → Ω → ℝ) (a b t : ℝ≥0) (ω : Ω) : ℝ :=
  B t ω-coefficient a b t*inc B a b ω
def residVector (B : ℝ≥0 → Ω → ℝ) (a b : ℝ≥0) (I : Finset ℝ≥0) (ω : Ω) : I → ℝ := fun i => resid B a b i ω

def tilted (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (H : Ω → ℝ) (a b : ℝ≥0) : Measure Ω :=
  P.withDensity (fun ω => gaussianTiltWeight (H ω) (b-a) (inc B a b ω))
def shifted (B : ℝ≥0 → Ω → ℝ) (H : Ω → ℝ) (a b t : ℝ≥0) (ω : Ω) : ℝ :=
  B t ω-H ω*overlap a b t

private theorem inc_hasLaw (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hBM : IsPreBrownianReal B P)
    (a b : ℝ≥0) (hab : a ≤ b) : HasLaw (inc B a b) (gaussianReal 0 (b-a)) P := by
  have hd : nndist (b : ℝ) (a : ℝ)=b-a := by
    apply NNReal.coe_injective
    rw [coe_nndist,Real.dist_eq,NNReal.coe_sub hab,abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast hab)
  rw [← hd]
  exact hBM.hasLaw_sub b a

private theorem resid_measurable (B : ℝ≥0 → Ω → ℝ) (hB : ∀ t, Measurable (B t)) (a b t : ℝ≥0) :
    Measurable (resid B a b t) := (hB t).sub (measurable_const.mul ((hB b).sub (hB a)))
private theorem obs_inc_cov (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hBM : IsPreBrownianReal B P) (a b t : ℝ≥0) :
    cov[B t,inc B a b;P]=overlap a b t := by
  let _ := hBM.isGaussianProcess.isProbabilityMeasure
  have hL (t : ℝ≥0) := (hBM.hasLaw_eval t).hasGaussianLaw.memLp_two
  change cov[B t,fun ω => B b ω-B a ω;P]=_
  rw [covariance_fun_sub_right (hL t) (hL b) (hL a),hBM.covariance_eval,hBM.covariance_eval]
  rfl
private theorem resid_inc_cov (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hB : ∀ t, Measurable (B t))
    (hBM : IsPreBrownianReal B P) (a b t : ℝ≥0) (hab : a < b) : cov[resid B a b t,inc B a b;P]=0 := by
  let _ := hBM.isGaussianProcess.isProbabilityMeasure
  have hL (t : ℝ≥0) := (hBM.hasLaw_eval t).hasGaussianLaw.memLp_two
  have hI : MemLp (inc B a b) 2 P := (hBM.hasLaw_sub b a).hasGaussianLaw.memLp_two
  have hv : cov[inc B a b,inc B a b;P]=(b : ℝ)-(a : ℝ) := by
    rw [covariance_self (show AEMeasurable (inc B a b) P from ((hB b).sub (hB a)).aemeasurable),(inc_hasLaw P B hBM a b hab.le).variance_eq,
      variance_id_gaussianReal,NNReal.coe_sub hab.le]
  change cov[fun ω => B t ω-coefficient a b t*inc B a b ω,inc B a b;P]=0
  rw [covariance_fun_sub_left (hL t) (hI.const_mul _) hI,obs_inc_cov P B hBM,covariance_const_mul_left,hv]
  have hd : (b : ℝ)-(a : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr (show (a : ℝ)<(b : ℝ) from hab))
  unfold coefficient
  field_simp [hd]
  ring

private theorem jointGaussian (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hBM : IsPreBrownianReal B P)
    (a b : ℝ≥0) (I : Finset ℝ≥0) :
    IsGaussianProcess (Sum.elim (fun _ : Unit => inc B a b)
      (Sum.elim (fun i : I => resid B a b i) (fun r : Iic a => B r))) P := by
  classical
  apply hBM.isGaussianProcess.of_isGaussianProcess
  rintro (_ | (i | r))
  · exact ⟨{a,b},
      { toFun x := x ⟨b,by simp⟩-x ⟨a,by simp⟩
        map_add' x y := by simp; ring
        map_smul' c x := by simp; ring },fun _ => rfl⟩
  · exact ⟨{(i : ℝ≥0),a,b},
      { toFun x := x ⟨i,by simp⟩-coefficient a b i*(x ⟨b,by simp⟩-x ⟨a,by simp⟩)
        map_add' x y := by simp; ring
        map_smul' c x := by simp; ring },fun _ => rfl⟩
  · exact ⟨{(r : ℝ≥0)},
      { toFun x := x ⟨r,by simp⟩
        map_add' x y := rfl
        map_smul' c x := rfl },fun _ => rfl⟩

private theorem resid_H_indep (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hB : ∀ t, Measurable (B t))
    (hBM : IsPreBrownianReal B P) (H : Ω → ℝ) (a b : ℝ≥0) (hab : a < b)
    (hH : StronglyMeasurable[(@natural Ω mΩ B hB) a] H) (I : Finset ℝ≥0) :
    IndepFun (fun ω => (residVector B a b I ω,H ω)) (inc B a b) P := by
  let Z : Sum I (Iic a) → Ω → ℝ := Sum.elim (fun i : I => resid B a b i) (fun r : Iic a => B r)
  have hi := (jointGaussian P B hBM a b I).indepFun_of_covariance_eq_zero
    (fun _ => ((hB b).sub (hB a)).aemeasurable)
    (fun q => by cases q with
      | inl i => exact (resid_measurable B hB a b i).aemeasurable
      | inr r => exact (hB r).aemeasurable) (fun _ q => by
        cases q with
        | inl i => exact (covariance_comm _ _).trans (resid_inc_cov P B hB hBM a b i hab)
        | inr r =>
          change cov[inc B a b,B r;P]=0
          rw [covariance_comm,obs_inc_cov P B hBM]
          unfold overlap
          rw [min_eq_left (r.property.trans hab.le),min_eq_left r.property]
          simp)
  have hzind : IndepFun (inc B a b) (fun ω q => Z q ω) P := hi.comp (measurable_pi_apply ()) measurable_id
  let mZ := MeasurableSpace.comap (fun ω q => Z q ω) inferInstance
  have hmZ : @Measurable Ω (Sum I (Iic a) → ℝ) mZ inferInstance (fun ω q => Z q ω) :=
    measurable_iff_comap_le.mpr le_rfl
  have hR : @Measurable Ω (I → ℝ) mZ inferInstance (residVector B a b I) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply (Sum.inl i)).comp hmZ)
  have hPast : @Measurable Ω (Iic a → ℝ) mZ inferInstance (fun ω r => B r ω) :=
    measurable_pi_lambda _ (fun r => (measurable_pi_apply (Sum.inr r)).comp hmZ)
  have hStart : (@natural Ω mΩ B hB) a ≤ mZ := by
    change (⨆ (j : ℝ≥0) (_ : j ≤ a),MeasurableSpace.comap (B j) inferInstance) ≤ mZ
    refine iSup₂_le (fun j hj => ?_)
    exact ((measurable_pi_apply ⟨j,hj⟩).comp hPast).comap_le
  have hX : @Measurable Ω ((I → ℝ) × ℝ) mZ inferInstance (fun ω => (residVector B a b I ω,H ω)) :=
    hR.prodMk (hH.measurable.mono hStart le_rfl)
  have hI : Indep (MeasurableSpace.comap (inc B a b) inferInstance) mZ P := hzind
  exact (indep_of_indep_of_le_right hI hX.comap_le).symm

theorem shifted_measurable (B : ℝ≥0 → Ω → ℝ) (hB : ∀ t, Measurable (B t))
    (H : Ω → ℝ) (a b t : ℝ≥0) (hH : StronglyMeasurable[(@natural Ω mΩ B hB) a] H) :
    Measurable (shifted B H a b t) :=
  (hB t).sub ((hH.mono (((@natural Ω mΩ B hB)).le a)).measurable.mul_const _)

/-- Genuine whole finite-law transport from a proved base source. -/
theorem shifted_finite_map (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : ∀ t, Measurable (B t)) (hBM : IsPreBrownianReal B P) (H : Ω → ℝ) (a b : ℝ≥0) (hab : a < b)
    (hH : StronglyMeasurable[(@natural Ω mΩ B hB) a] H) (I : Finset ℝ≥0) :
    (tilted P B H a b).map (fun ω => I.restrict (shifted B H a b · ω)) =
      P.map (fun ω => I.restrict (B · ω)) := by
  let X := fun ω => (residVector B a b I ω,H ω)
  have hX : Measurable X := by
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ (fun i => resid_measurable B hB a b i)
    · exact (hH.mono (((@natural Ω mΩ B hB)).le a)).measurable
  have h := independent_gaussian_random_tilt_joint P X hX (inc B a b) ((hB b).sub (hB a)) (b-a)
    (inc_hasLaw P B hBM a b hab.le) (resid_H_indep P B hB hBM H a b hab hH I) Prod.snd measurable_snd
  change (tilted P B H a b).map (fun ω => ((residVector B a b I ω,H ω),inc B a b ω-H ω*((b-a : ℝ≥0) : ℝ))) =
    P.map (fun ω => ((residVector B a b I ω,H ω),inc B a b ω)) at h
  let F : ((I → ℝ) × ℝ) × ℝ → I → ℝ := fun p i => p.1.1 i+coefficient a b i*p.2
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro i
    exact ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).add (measurable_const.mul measurable_snd)
  have hmL : Measurable (fun ω => ((residVector B a b I ω,H ω),inc B a b ω-H ω*((b-a : ℝ≥0) : ℝ))) :=
    hX.prodMk (((hB b).sub (hB a)).sub ((hH.mono (((@natural Ω mΩ B hB)).le a)).measurable.mul_const _))
  have hmR : Measurable (fun ω => ((residVector B a b I ω,H ω),inc B a b ω)) := hX.prodMk ((hB b).sub (hB a))
  have hh := congrArg (fun μ : Measure (((I → ℝ) × ℝ) × ℝ) => μ.map F) h
  rw [Measure.map_map hF hmL,Measure.map_map hF hmR] at hh
  have hl : F ∘ (fun ω => ((residVector B a b I ω,H ω),inc B a b ω-H ω*((b-a : ℝ≥0) : ℝ))) =
      fun ω => I.restrict (shifted B H a b · ω) := by
    funext ω i
    change B i ω-coefficient a b i*inc B a b ω+
      coefficient a b i*(inc B a b ω-H ω*((b-a : ℝ≥0) : ℝ))=B i ω-H ω*overlap a b i
    rw [NNReal.coe_sub hab.le]
    have hd : (b : ℝ)-(a : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr (show (a : ℝ)<(b : ℝ) from hab))
    unfold coefficient
    field_simp [hd]
    ring
  have hr : F ∘ (fun ω => ((residVector B a b I ω,H ω),inc B a b ω))=fun ω => I.restrict (B · ω) := by
    funext ω i
    change B i ω-coefficient a b i*inc B a b ω+coefficient a b i*inc B a b ω=B i ω
    ring
  rw [hl,hr] at hh
  exact hh

theorem shifted_isPreBrownian (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : ∀ t, Measurable (B t)) (hBM : IsPreBrownianReal B P) (H : Ω → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[(@natural Ω mΩ B hB) a] H) : IsPreBrownianReal (shifted B H a b) (tilted P B H a b) := by
  constructor
  intro I
  have hm : Measurable (fun ω => I.restrict (shifted B H a b · ω)) :=
    measurable_pi_lambda _ (fun i => shifted_measurable B hB H a b i hH)
  refine ⟨hm.aemeasurable,?_⟩
  rcases hab.eq_or_lt with h | h
  · subst b
    have ht : tilted P B H a a=P := by
      simp [tilted,gaussianTiltWeight,inc]
    rw [ht]
    simpa only [shifted,overlap,sub_self,mul_zero,sub_zero] using (hBM.hasLaw I).map_eq
  · exact (shifted_finite_map P B hB hBM H a b h hH I).trans (hBM.hasLaw I).map_eq

omit mΩ in
/-- The actual readout is literally unchanged through START. -/
theorem shifted_before (B : ℝ≥0 → Ω → ℝ) (H : Ω → ℝ) (a b t : ℝ≥0) (hab : a ≤ b) (ht : t ≤ a) (ω : Ω) :
    shifted B H a b t ω=B t ω := by
  simp only [shifted,overlap,min_eq_left (ht.trans hab),min_eq_left ht,sub_self,mul_zero,sub_zero]

theorem shifted_stronglyAdapted (B : ℝ≥0 → Ω → ℝ) (hB : ∀ t, Measurable (B t))
    (H : Ω → ℝ) (a b : ℝ≥0) (hab : a ≤ b) (hH : StronglyMeasurable[(@natural Ω mΩ B hB) a] H) :
    StronglyAdapted (@natural Ω mΩ B hB) (shifted B H a b) := by
  have hBA := Filtration.stronglyAdapted_natural (fun t => (hB t).stronglyMeasurable)
  intro t
  by_cases ht : t ≤ a
  · have he : shifted B H a b t=B t := funext (shifted_before B H a b t hab ht)
    rw [he]
    exact hBA t
  · exact (hBA t).sub ((hH.mono ((@natural Ω mΩ B hB).mono (le_of_not_ge ht))).mul stronglyMeasurable_const)

/-- Exact natural-past equality under the supplied START permission. It is
an equality of sigma algebras, with no null-set completion or filtration enlargement. -/
theorem shifted_natural_eq (B : ℝ≥0 → Ω → ℝ) (hB : ∀ t, Measurable (B t))
    (H : Ω → ℝ) (a b : ℝ≥0) (hab : a ≤ b) (hH : StronglyMeasurable[(@natural Ω mΩ B hB) a] H) :
    natural (shifted B H a b) (fun t => shifted_measurable B hB H a b t hH)=natural B hB := by
  let F := natural (shifted B H a b) (fun t => shifted_measurable B hB H a b t hH)
  have hWA : StronglyAdapted F (shifted B H a b) :=
    Filtration.stronglyAdapted_natural (fun t => (shifted_measurable B hB H a b t hH).stronglyMeasurable)
  have hs : F a=natural B hB a := by
    rw [show F a=MeasurableSpace.comap (fun ω (s : Iic a) => shifted B H a b s ω) inferInstance from
      Filtration.natural_eq_comap _ _ a,
      show natural B hB a=MeasurableSpace.comap (fun ω (s : Iic a) => B s ω) inferInstance from
      Filtration.natural_eq_comap _ _ a]
    congr 1
    funext ω r
    exact shifted_before B H a b r hab r.property ω
  have hHF : StronglyMeasurable[F a] H := by rw [hs]; exact hH
  have hBF : StronglyAdapted F B := by
    intro t
    by_cases ht : t ≤ a
    · have he : B t=shifted B H a b t := funext (fun ω => (shifted_before B H a b t hab ht ω).symm)
      rw [he]
      exact hWA t
    · have hh := hHF.mono (F.mono (le_of_not_ge ht))
      have he : B t=fun ω => shifted B H a b t ω+H ω*overlap a b t := by
        funext ω
        unfold shifted
        ring
      rw [he]
      exact (hWA t).add (hh.mul stronglyMeasurable_const)
  apply Filtration.ext
  funext t
  apply le_antisymm
  · change (⨆ (j : ℝ≥0) (_ : j ≤ t),MeasurableSpace.comap (shifted B H a b j) inferInstance) ≤ natural B hB t
    refine iSup₂_le (fun j hj => ?_)
    exact ((shifted_stronglyAdapted B hB H a b hab hH j).mono ((natural B hB).mono hj)).measurable.comap_le
  · change (⨆ (j : ℝ≥0) (_ : j ≤ t),MeasurableSpace.comap (B j) inferInstance) ≤ F t
    refine iSup₂_le (fun j hj => ?_)
    exact ((hBF j).mono (F.mono hj)).measurable.comap_le

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianMeasuredStepTransport
