import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

/-!
# P-ALI-01 — global exactness from closed periods

The frozen Core 3 theorem concerns a `C¹` one-form on a connected smooth
manifold.  It is globally exact exactly when its integral vanishes on every
piecewise-smooth closed curve.  The reverse direction below constructs the
potential from a fixed-basepoint path integral, derives path independence from
closed periods, and obtains the endpoint derivative in local coordinates.

`IsExactForm` intentionally asks only for manifold differentiability of the
potential together with `dV = form`; no stronger `CMDiff 1` hypothesis is
exposed at the source-facing theorem.
-/

open scoped Manifold Bundle ContDiff Topology
open Set Function Filter MeasureTheory

namespace UEOT.V3.AlignmentGlobalExactness

noncomputable section

variable {E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

abbrev CotangentFiber (x : M) := TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ

abbrev C1OneForm :=
  ContMDiffSection 𝓘(ℝ, E) (E →L[ℝ] ℝ) 1 (fun x : M => CotangentFiber (E := E) x)

structure SmoothArc (x y : M) where
  toFun : ℝ → M
  source : toFun 0 = x
  target : toFun 1 = y
  smooth : CMDiff[Set.Icc (0 : ℝ) 1] ∞ toFun

instance {x y : M} : CoeFun (SmoothArc (E := E) x y) (fun _ => ℝ → M) :=
  ⟨SmoothArc.toFun⟩

inductive PiecewiseSmoothPath (E M : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] : M → M → Type _
  | refl (x : M) : PiecewiseSmoothPath E M x x
  | atom {x y : M} (γ : SmoothArc (E := E) x y) : PiecewiseSmoothPath E M x y
  | trans {x y z : M} : PiecewiseSmoothPath E M x y → PiecewiseSmoothPath E M y z →
      PiecewiseSmoothPath E M x z
  | symm {x y : M} : PiecewiseSmoothPath E M x y → PiecewiseSmoothPath E M y x

noncomputable def arcIntegral (form : C1OneForm (E := E) (M := M))
    {x y : M} (γ : SmoothArc (E := E) x y) : ℝ :=
  ∫ t in (0 : ℝ)..1, form (γ t) ((mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t) 1)

noncomputable def pathIntegral (form : C1OneForm (E := E) (M := M)) :
    {x y : M} → PiecewiseSmoothPath E M x y → ℝ
  | _, _, .refl _ => 0
  | _, _, .atom γ => arcIntegral form γ
  | _, _, .trans γ δ => pathIntegral form γ + pathIntegral form δ
  | _, _, .symm γ => - pathIntegral form γ

@[simp] theorem pathIntegral_refl (form : C1OneForm (E := E) (M := M)) (x : M) :
    pathIntegral form (.refl x) = 0 := rfl

@[simp] theorem pathIntegral_trans (form : C1OneForm (E := E) (M := M))
    {x y z : M} (γ : PiecewiseSmoothPath E M x y) (δ : PiecewiseSmoothPath E M y z) :
    pathIntegral form (.trans γ δ) = pathIntegral form γ + pathIntegral form δ := rfl

@[simp] theorem pathIntegral_symm (form : C1OneForm (E := E) (M := M))
    {x y : M} (γ : PiecewiseSmoothPath E M x y) :
    pathIntegral form (.symm γ) = -pathIntegral form γ := rfl

def IsExactForm (form : C1OneForm (E := E) (M := M)) : Prop :=
  ∃ V : M → ℝ, MDiff V ∧ ∀ x, mvfderiv 𝓘(ℝ, E) V x = form x

def ClosedPeriods (form : C1OneForm (E := E) (M := M)) : Prop :=
  ∀ x (γ : PiecewiseSmoothPath E M x x), pathIntegral form γ = 0

theorem pathIndependent (form : C1OneForm (E := E) (M := M))
    (hperiod : ClosedPeriods form) {x y : M}
    (γ δ : PiecewiseSmoothPath E M x y) :
    pathIntegral form γ = pathIntegral form δ := by
  have hloop := hperiod x (.trans γ (.symm δ))
  rw [pathIntegral_trans, pathIntegral_symm] at hloop
  linarith

noncomputable def oneFormCoordAt (form : C1OneForm (E := E) (M := M))
    (x y : M) : E →L[ℝ] ℝ :=
  ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E)) ℝ (fun _ : M => ℝ)
    x y x y (form y)

lemma contMDiffOn_oneFormCoordAt (form : C1OneForm (E := E) (M := M)) (x : M) :
    CMDiff[(trivializationAt (E →L[ℝ] ℝ)
      (fun y : M => CotangentFiber (E := E) y) x).baseSet]
      1 (oneFormCoordAt form x) := by
  let eh := trivializationAt (E →L[ℝ] ℝ)
    (fun y : M => CotangentFiber (E := E) y) x
  have hsec := form.contMDiff.contMDiffOn (s := Set.univ)
  have hsec' := hsec.mono (show eh.baseSet ⊆ Set.univ from Set.subset_univ _)
  have hcoord := (eh.contMDiffOn_section_baseSet_iff).mp hsec'
  change CMDiff[eh.baseSet] 1
    (fun y => ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E)) ℝ
      (fun _ : M => ℝ) x y x y (form y))
  exact hcoord

noncomputable def coordOneFormAt (form : C1OneForm (E := E) (M := M))
    (x : M) (z : E) : E →L[ℝ] ℝ :=
  oneFormCoordAt form x ((extChartAt 𝓘(ℝ, E) x).symm z)

lemma coordOneForm_eventually_continuousAt
    (form : C1OneForm (E := E) (M := M)) (x : M) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ, E) x x), ContinuousAt (coordOneFormAt form x) z := by
  let e := extChartAt 𝓘(ℝ, E) x
  let eh := trivializationAt (E →L[ℝ] ℝ)
    (fun y : M => CotangentFiber (E := E) y) x
  have hcoord : CMDiff[eh.baseSet] 1 (oneFormCoordAt form x) := by
    simpa [eh] using contMDiffOn_oneFormCoordAt (form := form) x
  have hinv : CMDiff[e.target] 1 (e.symm : E → M) := by
    exact contMDiffOn_extChartAt_symm (n := 1) x
  have hmaps : MapsTo (e.symm : E → M) e.target eh.baseSet := by
    intro z hz
    have hzsrc : e.symm z ∈ e.source := e.map_target hz
    change e.symm z ∈
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).baseSet ∩
        (trivializationAt ℝ (fun _ : M => ℝ) x).baseSet
    constructor
    · rw [TangentBundle.trivializationAt_baseSet]
      simpa [e, extChartAt_source] using hzsrc
    · simp
  have hcomp : CMDiff[e.target] 1 (coordOneFormAt form x) := by
    change CMDiff[e.target] 1 (oneFormCoordAt form x ∘ e.symm)
    exact hcoord.comp hinv hmaps
  have htarget : e.target ∈ 𝓝 (e x) := extChartAt_target_mem_nhds x
  filter_upwards [htarget] with z hz
  exact hcomp.continuousOn.continuousAt ((isOpen_extChartAt_target x).mem_nhds hz)

lemma oneFormCoordAt_comp_chart_self (form : C1OneForm (E := E) (M := M)) (x : M) :
    (oneFormCoordAt form x x).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) x) = form x := by
  have hinv := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := 𝓘(ℝ, E)) (x := x) (y := x) (mem_extChartAt_source x)
  ext v
  have hv := congrArg (fun L => L v) hinv
  simp [oneFormCoordAt, ContinuousLinearMap.inCoordinates,
    TangentBundle.symmL_trivializationAt,
    Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization] at ⊢ hv
  exact congrArg (fun w => form x w) hv

lemma coordOneForm_apply_mfderiv_symm
    (form : C1OneForm (E := E) (M := M)) (x : M) {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E) x).target) (v : E) :
    coordOneFormAt form x z v =
      form ((extChartAt 𝓘(ℝ, E) x).symm z)
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
          ((extChartAt 𝓘(ℝ, E) x).symm : E → M) z) v) := by
  let e := extChartAt 𝓘(ℝ, E) x
  have hsrc : e.symm z ∈ (chartAt E x).source := by
    have := e.map_target hz
    simpa [e, extChartAt_source] using this
  unfold coordOneFormAt oneFormCoordAt ContinuousLinearMap.inCoordinates
  rw [TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ, E)) (x₀ := x)
    (x := e.symm z) hsrc]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_comp]
  have hright : e (e.symm z) = z := e.right_inv hz
  rw [hright]
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ]
  rfl

noncomputable def coordSegmentPotential (form : C1OneForm (E := E) (M := M))
    (x : M) (z : E) : ℝ :=
  ∫ᶜ w in Path.segment (extChartAt 𝓘(ℝ, E) x x) z, coordOneFormAt form x w

lemma hasFDerivAt_coordSegmentPotential (form : C1OneForm (E := E) (M := M)) (x : M) :
    HasFDerivAt (coordSegmentPotential form x)
      (coordOneFormAt form x (extChartAt 𝓘(ℝ, E) x x))
      (extChartAt 𝓘(ℝ, E) x x) := by
  exact HasFDerivAt.curveIntegral_segment_source'
    (coordOneForm_eventually_continuousAt (form := form) x)

lemma hasMFDerivAt_chartSegmentPotential
    (form : C1OneForm (E := E) (M := M)) (x : M) :
    HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ)
      (fun y : M => coordSegmentPotential form x (extChartAt 𝓘(ℝ, E) x y)) x (form x) := by
  let e := extChartAt 𝓘(ℝ, E) x
  have hseg := (hasFDerivAt_coordSegmentPotential (form := form) x).hasMFDerivAt
  have he : MDiffAt (e : M → E) x := by
    exact mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E)) (x := x) (y := x) (by simp)
  have hcomp := hseg.comp x he.hasMFDerivAt
  have hcoordbase : coordOneFormAt form x (e x) = oneFormCoordAt form x x := by
    unfold coordOneFormAt
    rw [e.left_inv (mem_extChartAt_source x)]
  rw [hcoordbase] at hcomp
  have hderiv : (oneFormCoordAt form x x).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e : M → E) x) = form x := by
    change (oneFormCoordAt form x x).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) x) = form x
    exact oneFormCoordAt_comp_chart_self (form := form) x
  have hcomp2 := hcomp.congr_mfderiv hderiv
  change HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ)
    (coordSegmentPotential form x ∘ (extChartAt 𝓘(ℝ, E) x : M → E)) x (form x)
  exact hcomp2

noncomputable def chartArc (x y : M)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) x).source)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AffineMap.lineMap (extChartAt 𝓘(ℝ, E) x x) (extChartAt 𝓘(ℝ, E) x y) t ∈
        (extChartAt 𝓘(ℝ, E) x).target) : SmoothArc (E := E) x y := by
  let e := extChartAt 𝓘(ℝ, E) x
  let line : ℝ → E := fun t => AffineMap.lineMap (e x) (e y) t
  let γ : ℝ → M := e.symm ∘ line
  have hline : CMDiff ∞ line := by
    rw [contMDiff_iff_contDiff]
    exact AffineMap.contDiff_lineMap (e x) (e y)
  have hγ : CMDiff[Set.Icc (0 : ℝ) 1] ∞ γ := by
    apply (contMDiffOn_extChartAt_symm x).comp hline.contMDiffOn
    intro t ht
    exact hseg t ht
  refine ⟨γ, ?_, ?_, hγ⟩
  · dsimp [γ, line]
    simp only [AffineMap.lineMap_apply_zero]
    exact e.left_inv (mem_extChartAt_source x)
  · dsimp [γ, line]
    simp only [AffineMap.lineMap_apply_one]
    exact e.left_inv hy

lemma mfderiv_lineMap_apply_one (a b : E) (t : ℝ) :
    (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (AffineMap.lineMap a b) t) 1 = b - a := by
  rw [mfderiv_eq_fderiv]
  change deriv (AffineMap.lineMap a b) t = b - a
  exact AffineMap.hasDerivAt_lineMap.deriv

lemma arcIntegral_chartArc_eq_coordSegmentPotential
    (form : C1OneForm (E := E) (M := M)) (x y : M)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) x).source)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AffineMap.lineMap (extChartAt 𝓘(ℝ, E) x x) (extChartAt 𝓘(ℝ, E) x y) t ∈
        (extChartAt 𝓘(ℝ, E) x).target) :
    arcIntegral form (chartArc (E := E) x y hy hseg) =
      coordSegmentPotential form x (extChartAt 𝓘(ℝ, E) x y) := by
  let e := extChartAt 𝓘(ℝ, E) x
  let line : ℝ → E := fun t => AffineMap.lineMap (e x) (e y) t
  rw [arcIntegral, coordSegmentPotential, curveIntegral_segment]
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro t ht
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hzt : line t ∈ e.target := by
    exact hseg t htI
  have hsymmWithin := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, E)) hzt
  rw [ModelWithCorners.range_eq_univ] at hsymmWithin
  have hsymm : MDiffAt (e.symm : E → M) (line t) :=
    hsymmWithin.mdifferentiableAt univ_mem
  have hline : MDiffAt line t := by
    exact AffineMap.hasDerivAt_lineMap.differentiableAt.mdifferentiableAt
  have hchain := mfderiv_comp_apply t hsymm hline (1 : TangentSpace 𝓘(ℝ) t)
  have hlineDeriv : (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) line t) 1 = e y - e x := by
    simpa [line] using mfderiv_lineMap_apply_one (a := e x) (b := e y) t
  have hcoord := coordOneForm_apply_mfderiv_symm (form := form) x hzt (e y - e x)
  change form ((e.symm ∘ line) t)
      ((mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (e.symm ∘ line) t) 1) =
    coordOneFormAt form x (line t) (e y - e x)
  rw [hchain, hlineDeriv]
  exact hcoord.symm

lemma exists_local_chartIntegralArc
    (form : C1OneForm (E := E) (M := M)) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∃ γ : SmoothArc (E := E) x y,
        pathIntegral form (.atom γ) =
          coordSegmentPotential form x (extChartAt 𝓘(ℝ, E) x y) := by
  let e := extChartAt 𝓘(ℝ, E) x
  have htarget : e.target ∈ 𝓝 (e x) := extChartAt_target_mem_nhds x
  rcases Metric.mem_nhds_iff.1 htarget with ⟨r, hr, hball⟩
  let U : Set M := e.source ∩ e ⁻¹' Metric.ball (e x) r
  refine ⟨U, ?_, ?_, ?_⟩
  · simpa [U, e] using
      (isOpen_extChartAt_preimage (I := 𝓘(ℝ, E)) x
        (Metric.isOpen_ball : IsOpen (Metric.ball (e x) r)))
  · exact ⟨mem_extChartAt_source x, Metric.mem_ball_self hr⟩
  · intro y hyU
    have hy : y ∈ e.source := hyU.1
    have hyball : e y ∈ Metric.ball (e x) r := hyU.2
    have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        AffineMap.lineMap (e x) (e y) t ∈ e.target := by
      intro t ht
      apply hball
      exact (convex_ball (e x) r).segment_subset (Metric.mem_ball_self hr) hyball
        (lineMap_mem_segment ℝ (e x) (e y) ht)
    let γ := chartArc (E := E) x y hy hseg
    refine ⟨γ, ?_⟩
    change arcIntegral form γ = coordSegmentPotential form x (e y)
    exact arcIntegral_chartArc_eq_coordSegmentPotential form x y hy hseg

def HasLocalEndpointPrimitive (form : C1OneForm (E := E) (M := M)) : Prop :=
  ∀ x : M, ∃ L : M → ℝ,
    MDiffAt L x ∧
    mvfderiv 𝓘(ℝ, E) L x = form x ∧
    ∀ᶠ y in 𝓝 x, ∃ γ : PiecewiseSmoothPath E M x y, pathIntegral form γ = L y

theorem hasLocalEndpointPrimitive (form : C1OneForm (E := E) (M := M)) :
    HasLocalEndpointPrimitive form := by
  intro x
  let L : M → ℝ := fun y => coordSegmentPotential form x (extChartAt 𝓘(ℝ, E) x y)
  have hLderiv := hasMFDerivAt_chartSegmentPotential (form := form) x
  refine ⟨L, hLderiv.mdifferentiableAt, ?_, ?_⟩
  · unfold mvfderiv
    rw [hLderiv.mfderiv]
    rfl
  · rcases exists_local_chartIntegralArc (form := form) x with ⟨U, hUopen, hxU, hU⟩
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    rcases hU y hy with ⟨γ, hγ⟩
    refine ⟨.atom γ, ?_⟩
    simpa [L] using hγ

def smoothReachableSet (x₀ : M) : Set M :=
  {y | Nonempty (PiecewiseSmoothPath E M x₀ y)}

lemma exists_local_smoothArc (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, Nonempty (SmoothArc (E := E) x y) := by
  let e := extChartAt 𝓘(ℝ, E) x
  have htarget : e.target ∈ 𝓝 (e x) := extChartAt_target_mem_nhds x
  rcases Metric.mem_nhds_iff.1 htarget with ⟨r, hr, hball⟩
  let U : Set M := e.source ∩ e ⁻¹' Metric.ball (e x) r
  refine ⟨U, ?_, ?_, ?_⟩
  · simpa [U, e] using
      (isOpen_extChartAt_preimage (I := 𝓘(ℝ, E)) x
        (Metric.isOpen_ball : IsOpen (Metric.ball (e x) r)))
  · exact ⟨mem_extChartAt_source x, Metric.mem_ball_self hr⟩
  · intro y hyU
    have hy : y ∈ e.source := hyU.1
    have hyball : e y ∈ Metric.ball (e x) r := hyU.2
    have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        AffineMap.lineMap (e x) (e y) t ∈ e.target := by
      intro t ht
      apply hball
      exact (convex_ball (e x) r).segment_subset (Metric.mem_ball_self hr) hyball
        (lineMap_mem_segment ℝ (e x) (e y) ht)
    exact ⟨chartArc (E := E) x y hy hseg⟩

lemma isOpen_smoothReachableSet (x₀ : M) :
    IsOpen (smoothReachableSet (E := E) x₀) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rcases exists_local_smoothArc (E := E) y with ⟨U, hUopen, hyU, hU⟩
  apply Filter.mem_of_superset (hUopen.mem_nhds hyU)
  intro z hz
  rcases hy with ⟨p⟩
  rcases hU z hz with ⟨γ⟩
  exact ⟨.trans p (.atom γ)⟩

lemma isClosed_smoothReachableSet (x₀ : M) :
    IsClosed (smoothReachableSet (E := E) x₀) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  rcases exists_local_smoothArc (E := E) y with ⟨U, hUopen, hyU, hU⟩
  apply Filter.mem_of_superset (hUopen.mem_nhds hyU)
  intro z hz
  simp only [smoothReachableSet, Set.mem_compl_iff, Set.mem_ofPred_eq] at hy ⊢
  intro hzReach
  rcases hzReach with ⟨p⟩
  rcases hU z hz with ⟨γ⟩
  exact hy ⟨.trans p (.symm (.atom γ))⟩

theorem piecewiseSmooth_connected [ConnectedSpace M] (x y : M) :
    Nonempty (PiecewiseSmoothPath E M x y) := by
  let R := smoothReachableSet (E := E) x
  have hRclopen : IsClopen R :=
    ⟨isClosed_smoothReachableSet (E := E) x, isOpen_smoothReachableSet (E := E) x⟩
  have hRnonempty : R.Nonempty := ⟨x, ⟨.refl x⟩⟩
  have hRuniv : R = Set.univ := hRclopen.eq_univ hRnonempty
  have hy : y ∈ R := by simp [hRuniv]
  exact hy

noncomputable def chosenPath [ConnectedSpace M] (x y : M) :
    PiecewiseSmoothPath E M x y :=
  Classical.choice (piecewiseSmooth_connected (E := E) x y)

theorem closedPeriods_exact [ConnectedSpace M]
    (form : C1OneForm (E := E) (M := M))
    (hperiod : ClosedPeriods form) : IsExactForm form := by
  let x₀ : M := Classical.choice (inferInstance : Nonempty M)
  let V : M → ℝ := fun x => pathIntegral form (chosenPath (E := E) x₀ x)
  have hlocal := hasLocalEndpointPrimitive (form := form)
  have hVlocal (x : M) :
      ∃ L : M → ℝ,
        MDiffAt L x ∧
        mvfderiv 𝓘(ℝ, E) L x = form x ∧
        V =ᶠ[𝓝 x] (fun y => V x + L y) := by
    rcases hlocal x with ⟨L, hL, hdL, hcurves⟩
    refine ⟨L, hL, hdL, ?_⟩
    filter_upwards [hcurves] with y hy
    rcases hy with ⟨γ, hγ⟩
    have hpi := pathIndependent form hperiod
      (chosenPath (E := E) x₀ y)
      (.trans (chosenPath (E := E) x₀ x) γ)
    rw [pathIntegral_trans, hγ] at hpi
    exact hpi
  have hVdiff : MDiff V := by
    intro x
    rcases hVlocal x with ⟨L, hL, -, hEq⟩
    have hmodel : MDiffAt (fun y : M => V x + L y) x :=
      mdifferentiableAt_const.add hL
    exact hmodel.congr_of_eventuallyEq hEq
  have hdV : ∀ x, mvfderiv 𝓘(ℝ, E) V x = form x := by
    intro x
    rcases hVlocal x with ⟨L, hL, hdL, hEq⟩
    have hconst : MDiffAt (fun _ : M => V x) x := mdifferentiableAt_const
    have hmv :
        mvfderiv 𝓘(ℝ, E) V x =
          mvfderiv 𝓘(ℝ, E) (fun y : M => V x + L y) x := by
      have hmf :
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ) V x =
            mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (fun y : M => V x + L y) x :=
        hEq.mfderiv_eq
      ext v
      unfold mvfderiv
      simp only [ContinuousLinearMap.comp_apply]
      rw [hmf]
      rfl
    rw [hmv]
    change mvfderiv 𝓘(ℝ, E) ((fun _ : M => V x) + L) x = form x
    rw [mvfderiv_add hconst hL, mvfderiv_const]
    simpa using hdL
  exact ⟨V, hVdiff, hdV⟩

lemma contMDiff_oneTangentSection :
    CMDiff 1 (fun t : ℝ =>
      (Bundle.TotalSpace.mk' ℝ t (1 : TangentSpace 𝓘(ℝ) t) : TangentBundle 𝓘(ℝ) ℝ)) := by
  intro t
  rw [Bundle.contMDiffAt_section]
  simp
  exact contMDiffAt_const

noncomputable def oneTangentSection (t : ℝ) : TangentBundle 𝓘(ℝ) ℝ :=
  Bundle.TotalSpace.mk' ℝ t (1 : TangentSpace 𝓘(ℝ) t)

lemma continuousOn_arcTangentWithin {x y : M} (γ : SmoothArc (E := E) x y) :
    ContinuousOn
      (fun t : ℝ =>
        (Bundle.TotalSpace.mk' E (γ t)
          ((mfderiv[Set.Icc (0 : ℝ) 1] γ t) 1) :
          TangentBundle 𝓘(ℝ, E) M))
      (Set.Icc (0 : ℝ) 1) := by
  have hγ1 : CMDiff[Set.Icc (0 : ℝ) 1] 1 γ := γ.smooth.of_le (by simp)
  have huniq : UniqueMDiff[Set.Icc (0 : ℝ) 1] := by
    rw [uniqueMDiffOn_iff_uniqueDiffOn]
    exact uniqueDiffOn_Icc zero_lt_one
  have htan := hγ1.continuousOn_tangentMapWithin (by simp) huniq
  have hs : ContinuousOn oneTangentSection (Set.Icc (0 : ℝ) 1) :=
    contMDiff_oneTangentSection.continuous.continuousOn
  have hmaps : MapsTo oneTangentSection (Set.Icc (0 : ℝ) 1)
      ((fun p : TangentBundle 𝓘(ℝ) ℝ => p.proj) ⁻¹' Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact ht
  have hcomp := htan.comp hs hmaps
  change ContinuousOn
    (tangentMapWithin 𝓘(ℝ) 𝓘(ℝ, E) γ (Set.Icc (0 : ℝ) 1) ∘ oneTangentSection)
    (Set.Icc (0 : ℝ) 1)
  exact hcomp

lemma continuousOn_arcIntegrandWithin (form : C1OneForm (E := E) (M := M))
    {x y : M} (γ : SmoothArc (E := E) x y) :
    ContinuousOn
      (fun t : ℝ => form (γ t) ((mfderiv[Set.Icc (0 : ℝ) 1] γ t) 1))
      (Set.Icc (0 : ℝ) 1) := by
  have hγcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1) := γ.smooth.continuousOn
  have hform : ContinuousOn
      (fun t : ℝ =>
        (Bundle.TotalSpace.mk' (E →L[ℝ] ℝ) (γ t) (form (γ t)) :
          Bundle.TotalSpace (E →L[ℝ] ℝ)
            (fun z : M => TangentSpace 𝓘(ℝ, E) z →L[ℝ] ℝ)))
      (Set.Icc (0 : ℝ) 1) := by
    exact form.contMDiff.continuous.comp_continuousOn hγcont
  have hvec := continuousOn_arcTangentWithin (E := E) γ
  have happly := hform.clm_bundle_apply hvec
  intro t ht
  have hout := happly t ht
  rw [FiberBundle.continuousWithinAt_totalSpace] at hout
  simpa [Bundle.Trivial.fiberBundle_trivializationAt'] using hout.2

lemma mvfderiv_real_apply_one (f : ℝ → ℝ) (t : ℝ) :
    mvfderiv 𝓘(ℝ) f t 1 = deriv f t := by
  unfold mvfderiv
  rw [mfderiv_eq_fderiv]
  rfl

lemma arcIntegrand_intervalIntegrable (form : C1OneForm (E := E) (M := M))
    {x y : M} (γ : SmoothArc (E := E) x y) :
    IntervalIntegrable
      (fun t : ℝ => form (γ t) ((mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t) 1)) volume 0 1 := by
  let gw : ℝ → ℝ := fun t => form (γ t) ((mfderiv[Set.Icc (0 : ℝ) 1] γ t) 1)
  let g : ℝ → ℝ := fun t => form (γ t) ((mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t) 1)
  have hw : IntervalIntegrable gw volume 0 1 := by
    have hc : ContinuousOn gw (Set.uIcc (0 : ℝ) 1) := by
      simpa [gw, Set.uIcc_of_le zero_le_one] using
        (continuousOn_arcIntegrandWithin (form := form) γ)
    exact hc.intervalIntegrable
  have heq : Set.EqOn gw g (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    simp only [gw, g]
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  have heq' : Set.EqOn gw g (Set.uIoo (0 : ℝ) 1) := by
    simpa [Set.uIoo_of_le zero_le_one] using heq
  exact hw.congr_uIoo heq'

theorem arcIntegral_exact (form : C1OneForm (E := E) (M := M))
    (V : M → ℝ) (hV : MDiff V)
    (hdV : ∀ x, mvfderiv 𝓘(ℝ, E) V x = form x)
    {x y : M} (γ : SmoothArc (E := E) x y) :
    arcIntegral form γ = V y - V x := by
  let g : ℝ → ℝ := fun t => form (γ t) ((mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t) 1)
  have hγ1 : CMDiff[Set.Icc (0 : ℝ) 1] 1 γ := γ.smooth.of_le (by simp)
  have hcont : ContinuousOn (V ∘ γ) (Set.Icc (0 : ℝ) 1) :=
    hV.continuous.comp_continuousOn hγ1.continuousOn
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (V ∘ γ) (g t) t := by
    intro t ht
    have hγtC : CMDiffAt 1 γ t :=
      (hγ1 t ⟨ht.1.le, ht.2.le⟩).contMDiffAt (Icc_mem_nhds ht.1 ht.2)
    have hγt : MDiffAt γ t := hγtC.mdifferentiableAt one_ne_zero
    have hVt : MDiffAt V (γ t) := hV (γ t)
    have hcomp : MDiffAt (V ∘ γ) t := hVt.comp t hγt
    have hchain := mvfderiv_comp_apply t hVt hγt (1 : TangentSpace 𝓘(ℝ) t)
    rw [mvfderiv_real_apply_one, hdV] at hchain
    have hd := hcomp.differentiableAt.hasDerivAt
    exact hd.congr_deriv hchain
  have hint : IntervalIntegrable g volume 0 1 := by
    exact arcIntegrand_intervalIntegrable (form := form) γ
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    zero_le_one hcont hderiv hint
  rw [arcIntegral]
  change (∫ t in (0 : ℝ)..1, g t) = V y - V x
  rw [hftc]
  simp [Function.comp_apply, γ.source, γ.target]

theorem pathIntegral_exact (form : C1OneForm (E := E) (M := M))
    (V : M → ℝ) (hV : MDiff V)
    (hdV : ∀ x, mvfderiv 𝓘(ℝ, E) V x = form x)
    {x y : M} (γ : PiecewiseSmoothPath E M x y) :
    pathIntegral form γ = V y - V x := by
  induction γ with
  | refl x => simp
  | atom γ => exact arcIntegral_exact form V hV hdV γ
  | trans γ δ ihγ ihδ =>
      rw [pathIntegral_trans, ihγ, ihδ]
      ring
  | symm γ ih =>
      rw [pathIntegral_symm, ih]
      ring

theorem exact_closedPeriods (form : C1OneForm (E := E) (M := M))
    (hexact : IsExactForm form) : ClosedPeriods form := by
  rcases hexact with ⟨V, hV, hdV⟩
  intro x γ
  rw [pathIntegral_exact form V hV hdV γ]
  ring

theorem p_ali_01 [ConnectedSpace M] (form : C1OneForm (E := E) (M := M)) :
    IsExactForm form ↔ ClosedPeriods form := by
  constructor
  · exact exact_closedPeriods form
  · exact closedPeriods_exact form

end
end UEOT.V3.AlignmentGlobalExactness
