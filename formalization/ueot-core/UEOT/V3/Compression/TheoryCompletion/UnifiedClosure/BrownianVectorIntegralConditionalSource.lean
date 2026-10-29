import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralTimeSource

/-!
Original commitment: the SAME vector noise full integral needs a derived conditional prefix under its true joint past.
Existing result: genuine full native Euclidean domain, actual cutoff classes and whole-joint one-step tower/projection identities.
Premise reduced: bind supplied finite interval outputs and transfer literal conditional prefixes by proved native dense extension.
Model/witness: original productLaw d/inputLaw d T and jointNaturalFiltration, including d0/T0/repeats; no future coefficient pull.
Consumer: actual full-input joint-past conditional projection/adapted process; continuous samples and general vector Itô remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralConditionalSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorSimplePredictableIntegral
open BrownianVectorTimeInput BrownianVectorIntegralClosure BrownianVectorPredictableInputs
open BrownianVectorPredictableDensity BrownianVectorIntegralTimeSource
open BrownianCommonRefinement
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ)

/-- Actual finite input record with zero before/after the one allowed block.
Only H's original START permission is supplied; no integral certificate is a field. -/
def intervalRecord (T a b : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : Fin d → Sample d → ℝ) (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d a] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) : ElementaryInput d T where
  n := 3
  clock := ![0,a,b,T]
  coefficient := ![fun _ _ => 0,H,fun _ _ => 0]
  clock_mono := by
    have haT := hab.trans hbT
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  clock_zero := rfl
  clock_end := rfl
  coefficient_past := by
    intro i k
    fin_cases i
    · exact stronglyMeasurable_const
    · exact hHpast k
    · exact stronglyMeasurable_const
  coefficient_bounded := by
    intro i k
    fin_cases i
    · exact MemLp.zero
    · exact hH k
    · exact MemLp.zero

/-- Actual interval class inside the independently defined full predictable L2. -/
def intervalInput (T a b : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : Fin d → Sample d → ℝ) (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d a] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) : (fullPredictableL2 d) T :=
  (literalPredictableInput d) ((intervalRecord d) T a b hab hbT H hHpast hH)

theorem intervalInput_coe (T a b : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : Fin d → Sample d → ℝ) (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d a] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) :
    ((intervalInput d) T a b hab hbT H hHpast hH : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)) =ᵐ[(inputLaw d) T] BrownianVectorTimeInput.intervalInput d H a b := by
  let r := (intervalRecord d) T a b hab hbT H hHpast hH
  apply (integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp.trans
  apply Filter.Eventually.of_forall
  intro p
  change (∑ i : Fin 3, BrownianVectorTimeInput.intervalInput d (![fun _ _ => 0,H,fun _ _ => 0] i)
    (![0,a,b,T] i.castSucc) (![0,a,b,T] i.succ) p) = BrownianVectorTimeInput.intervalInput d H a b p
  apply (EuclideanSpace.equiv (Fin d) ℝ).injective
  funext k
  simp [Fin.sum_univ_succ,BrownianVectorTimeInput.intervalInput_apply]

theorem intervalRecord_output (T a b : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : Fin d → Sample d → ℝ) (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d a] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) :
    outputValue ((intervalRecord d) T a b hab hbT H hHpast hH) =
      (oneStep_memLp_two hH a b).toLp (oneStep d H a b) := by
  let r := (intervalRecord d) T a b hab hbT H hHpast hH
  apply Lp.ext
  apply (simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp.trans
  apply Filter.EventuallyEq.trans _ (oneStep_memLp_two hH a b).coeFn_toLp.symm
  apply Filter.Eventually.of_forall
  intro ω
  change (∑ i : Fin 3, oneStep d (![fun _ _ => 0,H,fun _ _ => 0] i)
    (![0,a,b,T] i.castSucc) (![0,a,b,T] i.succ) ω) = oneStep d H a b ω
  simp [Fin.sum_univ_succ,oneStep,component]

/-- Full predictableIntegral returns the SAME literal H times actual source
increment for the explicit supplied block input. -/
theorem integral_interval_literal (T a b : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : Fin d → Sample d → ℝ) (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d a] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) :
    (predictableIntegral d) T ((intervalInput d) T a b hab hbT H hHpast hH) =
      (oneStep_memLp_two hH a b).toLp (oneStep d H a b) := by
  rw [intervalInput,(predictableIntegral_returns_literal d),(intervalRecord_output d)]

private theorem cutoff_interval_eq (T a b u : ℝ≥0) (hbT : b ≤ T)
    (H : Fin d → Sample d → ℝ) :
    ((timeSet d) T u).indicator (BrownianVectorTimeInput.intervalInput d H a b) = BrownianVectorTimeInput.intervalInput d H a (clamp a b u) := by
  funext p
  have hmem : (p ∈ (timeSet d) T u ∧ p.1 ∈ Ioc (a : ℝ) (b : ℝ)) ↔
      p.1 ∈ Ioc (a : ℝ) (clamp a b u : ℝ≥0) := by
    simp only [timeSet,mem_prod,mem_Ioc,mem_univ,and_true,clamp,NNReal.coe_max,NNReal.coe_min]
    constructor
    · intro h
      exact ⟨h.2.1,(le_min h.2.2 (h.1.2.trans (min_le_left _ _))).trans (le_max_right _ _)⟩
    · intro h
      have hx : p.1 ≤ min (b : ℝ) (u : ℝ) := (le_max_iff.mp h.2).resolve_left (not_le.mpr h.1)
      have hbt : (b : ℝ) ≤ (T : ℝ) := by exact_mod_cast hbT
      exact ⟨⟨a.coe_nonneg.trans_lt h.1,
        le_min (hx.trans (min_le_right _ _)) ((hx.trans (min_le_left _ _)).trans hbt)⟩,
        ⟨h.1,hx.trans (min_le_left _ _)⟩⟩
  by_cases hc : p ∈ (timeSet d) T u
  · by_cases hi : p.1 ∈ Ioc (a : ℝ) (b : ℝ)
    · have hp := hmem.mp ⟨hc,hi⟩
      simp [BrownianVectorTimeInput.intervalInput,hc,hi,hp]
    · have hp : p.1 ∉ Ioc (a : ℝ) (clamp a b u : ℝ≥0) := fun hp => hi (hmem.mpr hp).2
      simp [BrownianVectorTimeInput.intervalInput,hc,hi,hp]
  · have hp : p.1 ∉ Ioc (a : ℝ) (clamp a b u : ℝ≥0) := fun hp => hc (hmem.mpr hp).1
    simp [BrownianVectorTimeInput.intervalInput,hc,hp]

/-- The ACTUAL cutoff operator on a supplied interval input is precisely the
same interval input with its source endpoint clamped. -/
theorem truncate_intervalInput (T a b u : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : Fin d → Sample d → ℝ) (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d a] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) :
    (truncate d) T u ((intervalInput d) T a b hab hbT H hHpast hH) =
      (intervalInput d) T a (clamp a b u) (clamp_bounds a b u hab).1
        ((clamp_bounds a b u hab).2.trans hbT) H hHpast hH := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [(truncate_coe d) T u ((intervalInput d) T a b hab hbT H hHpast hH),
    (intervalInput_coe d) T a b hab hbT H hHpast hH,
    (intervalInput_coe d) T a (clamp a b u) (clamp_bounds a b u hab).1
      ((clamp_bounds a b u hab).2.trans hbT) H hHpast hH] with p hp hi hj
  rw [hp,hj]
  calc
    _ = ((timeSet d) T u).indicator (BrownianVectorTimeInput.intervalInput d H a b) p := by
      by_cases hc : p ∈ (timeSet d) T u <;> simp [hc,hi]
    _ = _ := congrFun ((cutoff_interval_eq d) T a b u hbT H) p

/-- The actual truncated full-integral source agrees with the genuine natural
conditional projection of the original SAME interval output. -/
theorem projection_integral_interval (T a b u : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : Fin d → Sample d → ℝ) (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d a] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) :
    (naturalProjection d) u ((predictableIntegral d) T ((intervalInput d) T a b hab hbT H hHpast hH)) =
      (integralClassProcess d) T ((intervalInput d) T a b hab hbT H hHpast hH) u := by
  rw [(integral_interval_literal d),(oneStep_projection_prefix d) a b u hab hHpast hH,
    integralClassProcess,(truncate_intervalInput d),(integral_interval_literal d)]

private theorem part_order {T : ℝ≥0} (r : ElementaryInput d T) (i : Fin r.n) :
    r.clock i.castSucc ≤ r.clock i.succ := r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))

private theorem part_horizon {T : ℝ≥0} (r : ElementaryInput d T) (i : Fin r.n) :
    r.clock i.succ ≤ T := (r.clock_mono (Fin.le_last i.succ)).trans r.clock_end.le

private def partInput {T : ℝ≥0} (r : ElementaryInput d T) (i : Fin r.n) : (fullPredictableL2 d) T :=
  (intervalInput d) T (r.clock i.castSucc) (r.clock i.succ) ((part_order d) r i) ((part_horizon d) r i)
    (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)

/-- The actual original finite input equals the sum of its actual permitted
interval inputs in the ORIGINAL native full predictable L2 space. -/
private theorem literalInput_decomposition {T : ℝ≥0} (r : ElementaryInput d T) :
    (literalPredictableInput d) r = ∑ i : Fin r.n, (partInput d) r i := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  apply Lp.ext
  have hall : ∀ᵐ p ∂(inputLaw d) T, ∀ i : Fin r.n,
      ((partInput d) r i : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)) p =
        BrownianVectorTimeInput.intervalInput d (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) p :=
    ae_all_iff.mpr (fun i => (intervalInput_coe d) T _ _ ((part_order d) r i) ((part_horizon d) r i)
      (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i))
  filter_upwards [(integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp,
    Lp.coeFn_fun_finsetSum (μ := (inputLaw d) T) Finset.univ (fun i => ((partInput d) r i : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T))),hall] with p hp hs hi
  change ((integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).toLp
    (integrand d r.clock r.coefficient)) p = (∑ i : Fin r.n, ((partInput d) r i : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T))) p
  rw [hp,hs]
  exact Finset.sum_congr rfl (fun i _ => (hi i).symm)

private theorem literal_projection (T u : ℝ≥0) (r : ElementaryInput d T) :
    (naturalProjection d) u ((predictableIntegral d) T ((literalPredictableInput d) r)) =
      (integralAt d) T u ((literalPredictableInput d) r) := by
  let A := ((naturalProjection d) u).comp ((predictableIntegral d) T)
  let B := (integralAt d) T u
  have hi (i : Fin r.n) : A ((partInput d) r i) = B ((partInput d) r i) :=
    (projection_integral_interval d) T _ _ u ((part_order d) r i) ((part_horizon d) r i)
      (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)
  change A ((literalPredictableInput d) r) = B ((literalPredictableInput d) r)
  rw [(literalInput_decomposition d),map_sum,map_sum]
  exact Finset.sum_congr rfl (fun i _ => hi i)

private def domainToPredictable (T : ℝ≥0) : (integralDomain d) T →ₗᵢ[ℝ] (fullPredictableL2 d) T :=
  { Submodule.inclusion ((integralDomain_le_fullPredictableL2 d) T) with norm_map' := fun _ => rfl }

private theorem domainToPredictable_surjective (T : ℝ≥0) : Function.Surjective ((domainToPredictable d) T) := by
  intro f
  exact ⟨(predictableInclusion d) T f,Subtype.ext rfl⟩

private theorem literal_span_dense (T : ℝ≥0) :
    Dense (Submodule.span ℝ (Set.range (literalPredictableInput d (T := T))) : Set ((fullPredictableL2 d) T)) := by
  let S := Submodule.span ℝ (Set.range (literalPredictableInput d (T := T)))
  have hd : DenseRange (fun x : (elementarySpan d) T => (domainToPredictable d) T ((inclusionIsometry d) T x)) :=
    ((domainToPredictable_surjective d) T).denseRange.comp ((inclusion_dense d) T) ((domainToPredictable d) T).continuous
  have hmap : (elementarySpan d) T ≤ S.map ((fullPredictableL2 d) T).subtype := by
    rw [(elementarySpan_eq_span d)]
    apply Submodule.span_le.mpr
    rintro _ ⟨r,rfl⟩
    exact ⟨(literalPredictableInput d) r,Submodule.subset_span ⟨r,rfl⟩,rfl⟩
  apply hd.mono
  rintro y ⟨x,rfl⟩
  obtain ⟨z,hz,he⟩ := hmap x.property
  have heq : (domainToPredictable d) T ((inclusionIsometry d) T x) = z := Subtype.ext he.symm
  change (domainToPredictable d) T ((inclusionIsometry d) T x) ∈ S
  rw [heq]
  exact hz

/-- Actual full-input conditional identity. Native continuous linear maps
agree on the ACTUAL finite inputs, then on their PROVED dense span. -/
theorem integral_projection_identity (T u : ℝ≥0) (f : (fullPredictableL2 d) T) :
    (naturalProjection d) u ((predictableIntegral d) T f) = (integralClassProcess d) T f u := by
  have he : ((naturalProjection d) u).comp ((predictableIntegral d) T) = (integralAt d) T u := by
    apply ContinuousLinearMap.ext_on ((literal_span_dense d) T)
    rintro _ ⟨r,rfl⟩
    exact (literal_projection d) T u r
  exact congrArg (fun L : (fullPredictableL2 d) T →L[ℝ] Lp ℝ 2 (productLaw d) => L f) he

private theorem naturalProjection_condExp (u : ℝ≥0) (g : Lp ℝ 2 (productLaw d)) :
    ((naturalProjection d) u g : (Sample d) → ℝ) =ᵐ[(productLaw d)] (productLaw d)[g | (jointNaturalFiltration d) u] := by
  have h := (Lp.memLp g).condExpL2_ae_eq_condExp (𝕜 := ℝ) ((jointNaturalFiltration d).le u)
  have he : (Lp.memLp g).toLp g = g := Lp.ext (Lp.memLp g).coeFn_toLp
  rw [he] at h
  exact h

/-- Strongly adapted canonical version of the ACTUAL integral process.
Its identity with the actual cutoff source is proved immediately below. -/
def integralProcess (T : ℝ≥0) (f : (fullPredictableL2 d) T) (u : ℝ≥0) : (Sample d) → ℝ :=
  (productLaw d)[((predictableIntegral d) T f : (Sample d) → ℝ) | (jointNaturalFiltration d) u]

/-- EACH fixed-time canonical value is the SAME actual truncated integral
class. This is derived from literal source steps and L2 continuity, not assumed. -/
theorem integralProcess_eq_truncated (T u : ℝ≥0) (f : (fullPredictableL2 d) T) :
    (integralProcess d) T f u =ᵐ[(productLaw d)] ((integralClassProcess d) T f u : (Sample d) → ℝ) := by
  have h := (naturalProjection_condExp d) u ((predictableIntegral d) T f)
  rw [(integral_projection_identity d) T u f] at h
  exact h.symm

/-- The actual truncated integral class is genuinely L2-adapted to the source
natural past, not merely measurable in the full source sigma algebra. -/
theorem integralClassProcess_adapted (T u : ℝ≥0) (f : (fullPredictableL2 d) T) :
    (integralClassProcess d) T f u ∈ lpMeas ℝ ℝ ((jointNaturalFiltration d) u) 2 (productLaw d) := by
  rw [← (integral_projection_identity d) T u f]
  exact (condExpL2 ℝ ℝ ((jointNaturalFiltration d).le u) ((predictableIntegral d) T f)).property

/-- The canonical actual process is a genuine natural-filtration martingale;
its actual integral binding is the proved fixed-time identity above. -/
theorem integralProcess_martingale (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    Martingale ((integralProcess d) T f) (jointNaturalFiltration d) (productLaw d) :=
  martingale_condExp ((predictableIntegral d) T f) (jointNaturalFiltration d) (productLaw d)

theorem integralProcess_stronglyAdapted (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    StronglyAdapted (jointNaturalFiltration d) ((integralProcess d) T f) :=
  ((integralProcess_martingale d) T f).stronglyAdapted

theorem integralProcess_memLp_two (T u : ℝ≥0) (f : (fullPredictableL2 d) T) :
    MemLp ((integralProcess d) T f u) 2 (productLaw d) :=
  (memLp_congr_ae ((integralProcess_eq_truncated d) T u f)).mpr (Lp.memLp ((integralClassProcess d) T f u))

/-- Actual source-process energy, transferred through the proved integral
identity. It is not a quadratic-variation or sample-path continuity assertion. -/
theorem integralProcess_energy (T u : ℝ≥0) (f : (fullPredictableL2 d) T) :
    (∫ ω, (integralProcess d) T f u ω ^ 2 ∂(productLaw d)) =
      ∫ p in (timeSet d) T u, ‖(f : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)) p‖ ^ 2 ∂(inputLaw d) T := by
  have he : (fun ω => (integralProcess d) T f u ω ^ 2) =ᵐ[(productLaw d)]
      (fun ω => (integralClassProcess d) T f u ω ^ 2) :=
    ((integralProcess_eq_truncated d) T u f).mono (fun _ h => congrArg (fun x : ℝ => x^2) h)
  rw [integral_congr_ae he,(integralClassProcess_energy d)]

theorem integralProcess_zero (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    (integralProcess d) T f 0 =ᵐ[(productLaw d)] fun _ => 0 := by
  have h := (integralProcess_eq_truncated d) T 0 f
  rw [(integralClassProcess_zero d)] at h
  exact h.trans (Lp.coeFn_zero ℝ 2 (productLaw d))

theorem integralProcess_horizon (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    (integralProcess d) T f T =ᵐ[(productLaw d)] ((predictableIntegral d) T f : (Sample d) → ℝ) := by
  have h := (integralProcess_eq_truncated d) T T f
  rw [(integralClassProcess_horizon d)] at h
  exact h

/-- Original finite input returns its original literal finite output at the
horizon, on the SAME source sample space. -/
theorem integralProcess_returns_literal {T : ℝ≥0} (r : ElementaryInput d T) :
    (integralProcess d) T ((literalPredictableInput d) r) T =ᵐ[(productLaw d)]
      BrownianVectorSimplePredictableIntegral.simpleIntegral d r.clock r.coefficient := by
  have h := (integralProcess_horizon d) T ((literalPredictableInput d) r)
  rw [(predictableIntegral_returns_literal d)] at h
  exact h.trans (simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp

/-- For EACH actual observation time, the same supplied finite input
returns its literal source prefix. No uncountable common-AE claim is needed. -/
theorem integralProcess_returns_literal_prefix {T : ℝ≥0} (r : ElementaryInput d T) (u : ℝ≥0) :
    integralProcess d T (literalPredictableInput d r) u =ᵐ[productLaw d]
      fun ω => ∑ i : Fin r.n, oneStep d (r.coefficient i) (r.clock i.castSucc)
        (clamp (r.clock i.castSucc) (r.clock i.succ) u) ω := by
  unfold integralProcess
  rw [predictableIntegral_returns_literal]
  apply (condExp_congr_ae
    (simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp).trans
  have hs : (productLaw d)[simpleIntegral d r.clock r.coefficient | jointNaturalFiltration d u] =ᵐ[productLaw d]
      fun ω => ∑ i : Fin r.n, (productLaw d)[oneStep d (r.coefficient i) (r.clock i.castSucc)
        (r.clock i.succ) | jointNaturalFiltration d u] ω := by
    have he : simpleIntegral d r.clock r.coefficient =
        ∑ i : Fin r.n, oneStep d (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) := by
      funext ω
      simp only [simpleIntegral,Finset.sum_apply]
    rw [he]
    apply (condExp_finsetSum
      (s := Finset.univ) (f := fun i : Fin r.n => oneStep d (r.coefficient i)
        (r.clock i.castSucc) (r.clock i.succ))
      (fun i _ => (oneStep_memLp_two (r.coefficient_bounded i) _ _).integrable (by norm_num))
      (jointNaturalFiltration d u)).trans
    exact ae_of_all _ (fun ω => by simp only [Finset.sum_apply])
  apply hs.trans
  have hall : ∀ᵐ ω ∂productLaw d, ∀ i : Fin r.n,
      (productLaw d)[oneStep d (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) |
          jointNaturalFiltration d u] ω = oneStep d (r.coefficient i) (r.clock i.castSucc)
        (clamp (r.clock i.castSucc) (r.clock i.succ) u) ω :=
    ae_all_iff.mpr (fun i => oneStep_condExp_prefix d _ _ u (part_order d r i)
      (r.coefficient_past i) (r.coefficient_bounded i))
  exact hall.mono (fun _ h => Finset.sum_congr rfl (fun i _ => h i))

/-- The actual process starts at zero and hence has zero mean at every time,
with no separate mean-zero stochastic-integral premise. -/
theorem integralProcess_mean_zero (T u : ℝ≥0) (f : (fullPredictableL2 d) T) :
    (∫ ω, (integralProcess d) T f u ω ∂(productLaw d)) = 0 := by
  have h := ((integralProcess_martingale d) T f).setIntegral_eq
    (show (0 : ℝ≥0) ≤ u from bot_le) MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  rw [integral_congr_ae ((integralProcess_zero d) T f),integral_zero] at h
  exact h.symm

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralConditionalSource
