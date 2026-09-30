import UEOT.V3.Compression.StructuralDefectClosure
import UEOT.V3.CoreOperationalAssembly
import UEOT.V3.InformationZeroTV

/-!
# Second-order compression stress test: approximate control quotient -> exact limit

This module is an out-of-sample transfer test for the structural-defect bridge.
It does not alter any frozen Core v3 P-ID or counted compression generator.

The target is deliberately simple and auditable: keep the micro model, quotient
map, and candidate macro model fixed while a family of certified reward and
transition defects shrinks to zero.  The limit is then an exact control quotient,
so the existing P-QUO-01 theorem supplies exact value and policy lifting.

The mathematical point is not that a constant nonnegative quantity bounded by
a sequence tending to zero must vanish; that step is elementary.  The useful
cross-module statement is that Core v3's approximate control interface closes
onto its exact control interface under vanishing certified defects.
-/

namespace UEOT.V3.Compression.StructuralDefectControlLimit

open Filter Topology
open UEOT.V3.FiniteDiscountedControl

universe uX uM uA

/-- Zero finite-PMF total variation forces equality of the PMFs themselves.
This is a thin discrete wrapper around the registered measure-level zero-TV
theorem. -/
theorem pmf_eq_of_tvDist_eq_zero
    {S : Type*} (p q : PMF S)
    (hzero : FiniteProbabilityRow.tvDist p q = 0) :
    p = q := by
  letI : MeasurableSpace S := ⊤
  letI : MeasurableSingletonClass S := by infer_instance
  apply PMF.toMeasure_injective
  apply UEOT.V3.InformationZeroTV.measure_eq_of_tvDist_eq_zero
  simpa [FiniteProbabilityRow.tvDist] using hzero

/-- Finite-PMF total variation is nonnegative, with the discrete measurable
structure kept internal to the wrapper. -/
theorem finite_tvDist_nonneg
    {S : Type*} (p q : PMF S) :
    0 ≤ FiniteProbabilityRow.tvDist p q := by
  letI : MeasurableSpace S := ⊤
  change 0 ≤ UEOT.V3.TotalVariation.tvDist p.toMeasure q.toMeasure
  exact UEOT.V3.TotalVariation.tvDist_nonneg _ _

/-- Triangle inequality for the finite-PMF TV wrapper, keeping the discrete
measurable structure internal. -/
theorem finite_tvDist_triangle
    {S : Type*} (p q r : PMF S) :
    FiniteProbabilityRow.tvDist p r ≤
      FiniteProbabilityRow.tvDist p q +
        FiniteProbabilityRow.tvDist q r := by
  letI : MeasurableSpace S := ⊤
  change
    UEOT.V3.TotalVariation.tvDist p.toMeasure r.toMeasure ≤
      UEOT.V3.TotalVariation.tvDist p.toMeasure q.toMeasure +
        UEOT.V3.TotalVariation.tvDist q.toMeasure r.toMeasure
  exact UEOT.V3.TransportDefect.tvDist_triangle _ _ _

/-- A fixed finite control representation whose certified reward and transition
defects are bounded by envelopes converging to zero is already an exact control
quotient.

This theorem is outside the frozen 106 P-ID source list.  It is an assembly
bridge between the approximate quotient interface and the exact quotient
interface; it does not replace either source theorem family. -/
noncomputable def exactControlQuotient_of_vanishing_defects
    {X : Type uX} [Fintype X]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (f : X → M) (hf : Function.Surjective f)
    (micro : Model X (fun x => Abar (f x)))
    (macroModel : Model M Abar)
    (hdiscount : micro.discount = macroModel.discount)
    (εr εp : ℕ → ℝ)
    (hεr : Tendsto εr atTop (𝓝 0))
    (hεp : Tendsto εp atTop (𝓝 0))
    (hreward : ∀ n x (a : Abar (f x)),
      |micro.reward x a - macroModel.reward (f x) a| ≤ εr n)
    (htransition : ∀ n x (a : Abar (f x)),
      FiniteProbabilityRow.tvDist
        (pushforwardTransitionPMF f micro x a)
        (macroModel.transitionPMF (f x) a) ≤ εp n) :
    ExactControlQuotient X M Abar := by
  classical
  refine
    { f := f
      surjective := hf
      micro := micro
      macroModel := macroModel
      discount_eq := hdiscount
      reward_closed := ?_
      transition_closed := ?_ }
  · intro x a
    let d : ℝ := |micro.reward x a - macroModel.reward (f x) a|
    have hd0 : Tendsto (fun _ : ℕ => d) atTop (𝓝 0) := by
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hεr
        (Eventually.of_forall fun _ => abs_nonneg _)
        (Eventually.of_forall fun n => hreward n x a)
    have hd : d = 0 :=
      tendsto_nhds_unique tendsto_const_nhds hd0
    exact sub_eq_zero.mp (abs_eq_zero.mp hd)
  · intro x a y
    let p : PMF M := pushforwardTransitionPMF f micro x a
    let q : PMF M := macroModel.transitionPMF (f x) a
    let d : ℝ := FiniteProbabilityRow.tvDist p q
    have hd_nonneg : 0 ≤ d := by
      exact finite_tvDist_nonneg p q
    have hd0 : Tendsto (fun _ : ℕ => d) atTop (𝓝 0) := by
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hεp
        (Eventually.of_forall fun _ => hd_nonneg)
        (Eventually.of_forall fun n => htransition n x a)
    have hd : d = 0 :=
      tendsto_nhds_unique tendsto_const_nhds hd0
    have hpq : p = q :=
      pmf_eq_of_tvDist_eq_zero p q hd
    have hpoint := congrArg (fun r : PMF M => (r y).toReal) hpq
    simpa [p, q] using hpoint

/-- The previous exactification immediately transfers all frozen P-QUO-01
consequences: exact value pullback, exact optimal action-value agreement, and
macro-greedy policy lifting against the full causal policy class. -/
theorem p_quo_01_of_vanishing_defects
    {X : Type uX} [Fintype X]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (f : X → M) (hf : Function.Surjective f)
    (micro : Model X (fun x => Abar (f x)))
    (macroModel : Model M Abar)
    (hdiscount : micro.discount = macroModel.discount)
    (εr εp : ℕ → ℝ)
    (hεr : Tendsto εr atTop (𝓝 0))
    (hεp : Tendsto εp atTop (𝓝 0))
    (hreward : ∀ n x (a : Abar (f x)),
      |micro.reward x a - macroModel.reward (f x) a| ≤ εr n)
    (htransition : ∀ n x (a : Abar (f x)),
      FiniteProbabilityRow.tvDist
        (pushforwardTransitionPMF f micro x a)
        (macroModel.transitionPMF (f x) a) ≤ εp n) :
    let Q := exactControlQuotient_of_vanishing_defects
      f hf micro macroModel hdiscount εr εp hεr hεp hreward htransition
    (∀ x : X, Q.micro.optimalValue x =
        Q.macroModel.optimalValue (Q.f x)) ∧
    (∀ (x : X) (a : Abar (Q.f x)),
      Q.micro.qValue Q.micro.optimalValue x a =
        Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a) ∧
    (∀ {t : ℕ} (x : X),
      CausalPolicy.infiniteValue
        (selectorPolicy (Q.liftSelector Q.macroModel.greedyAction))
        Q.micro (t := t) x = Q.micro.optimalValue x) ∧
    (∀ (π : CausalPolicy X (fun x => Abar (Q.f x)))
        {t : ℕ} (h : π.Memory t),
      CausalPolicy.infiniteValue π Q.micro h ≤
        Q.micro.optimalValue (π.current h)) := by
  dsimp only
  exact (exactControlQuotient_of_vanishing_defects
    f hf micro macroModel hdiscount εr εp hεr hεp
    hreward htransition).p_quo_01

/-- P-CORE-01-facing adapter.

If a sequence of `FixedSourceApproximation` certificates all refers to the
same frozen micro source, quotient map, and macro target while its declared
reward/transition radii tend to zero, the fixed source/target pair is an exact
control quotient.

This is the direct assembly stress test requested by the second-order mission:
it consumes the source-identity wrapper used by P-CORE-01 rather than inventing
a parallel approximation interface. -/
noncomputable def exactControlQuotient_of_fixedSourceApproximation
    {X : Type uX} [Fintype X]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (f : X → M) (hf : Function.Surjective f)
    (micro : Model X (fun x => Abar (f x)))
    (macroModel : Model M Abar)
    (εr εp : ℕ → ℝ)
    (Q : ∀ n,
      UEOT.V3.CoreOperationalAssembly.FixedSourceApproximation
        f micro (εr n) (εp n))
    (hmacro : ∀ n, (Q n).macroModel = macroModel)
    (hεr : Tendsto εr atTop (𝓝 0))
    (hεp : Tendsto εp atTop (𝓝 0)) :
    ExactControlQuotient X M Abar := by
  have hdiscount : micro.discount = macroModel.discount := by
    have h := (Q 0).discount_eq
    rw [hmacro 0] at h
    exact h
  apply exactControlQuotient_of_vanishing_defects
    f hf micro macroModel hdiscount εr εp hεr hεp
  · intro n x a
    have h := (Q n).reward_approx x a
    rw [hmacro n] at h
    exact h
  · intro n x a
    have h := (Q n).transition_tv_approx x a
    rw [hmacro n] at h
    exact h

/-- Exact P-QUO-01 consequences for a P-CORE-01 fixed-source approximation
family whose certification radii vanish. -/
theorem p_quo_01_of_fixedSourceApproximation
    {X : Type uX} [Fintype X]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (f : X → M) (hf : Function.Surjective f)
    (micro : Model X (fun x => Abar (f x)))
    (macroModel : Model M Abar)
    (εr εp : ℕ → ℝ)
    (Q : ∀ n,
      UEOT.V3.CoreOperationalAssembly.FixedSourceApproximation
        f micro (εr n) (εp n))
    (hmacro : ∀ n, (Q n).macroModel = macroModel)
    (hεr : Tendsto εr atTop (𝓝 0))
    (hεp : Tendsto εp atTop (𝓝 0)) :
    let E := exactControlQuotient_of_fixedSourceApproximation
      f hf micro macroModel εr εp Q hmacro hεr hεp
    (∀ x : X, E.micro.optimalValue x =
        E.macroModel.optimalValue (E.f x)) ∧
    (∀ (x : X) (a : Abar (E.f x)),
      E.micro.qValue E.micro.optimalValue x a =
        E.macroModel.qValue E.macroModel.optimalValue (E.f x) a) ∧
    (∀ {t : ℕ} (x : X),
      CausalPolicy.infiniteValue
        (selectorPolicy (E.liftSelector E.macroModel.greedyAction))
        E.micro (t := t) x = E.micro.optimalValue x) ∧
    (∀ (π : CausalPolicy X (fun x => Abar (E.f x)))
        {t : ℕ} (h : π.Memory t),
      CausalPolicy.infiniteValue π E.micro h ≤
        E.micro.optimalValue (π.current h)) := by
  dsimp only
  exact (exactControlQuotient_of_fixedSourceApproximation
    f hf micro macroModel εr εp Q hmacro hεr hεp).p_quo_01

/-- Convergent estimated macro models exactify in the limit.

Each stage supplies the same fixed micro source and quotient map through
P-CORE-01's `FixedSourceApproximation`, but the estimated macro model may vary
with `n`.  If the source-to-estimate defects vanish and the estimated macro
models themselves approach one fixed target macro model in reward and
transition-TV coordinates, then the target macro model forms an exact control
quotient with the fixed source.

This is the stronger S5 assembly-transfer theorem: it models a genuine
estimation sequence rather than repeating one fixed approximate target. -/
noncomputable def exactControlQuotient_of_convergent_fixedSourceApproximation
    {X : Type uX} [Fintype X]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (f : X → M) (hf : Function.Surjective f)
    (micro : Model X (fun x => Abar (f x)))
    (macroLimit : Model M Abar)
    (hdiscountLimit : micro.discount = macroLimit.discount)
    (εr εp ρr ρp : ℕ → ℝ)
    (Q : ∀ n,
      UEOT.V3.CoreOperationalAssembly.FixedSourceApproximation
        f micro (εr n) (εp n))
    (hεr : Tendsto εr atTop (𝓝 0))
    (hεp : Tendsto εp atTop (𝓝 0))
    (hρr : Tendsto ρr atTop (𝓝 0))
    (hρp : Tendsto ρp atTop (𝓝 0))
    (hrewardLimit : ∀ n m (a : Abar m),
      |(Q n).macroModel.reward m a - macroLimit.reward m a| ≤ ρr n)
    (htransitionLimit : ∀ n m (a : Abar m),
      FiniteProbabilityRow.tvDist
        ((Q n).macroModel.transitionPMF m a)
        (macroLimit.transitionPMF m a) ≤ ρp n) :
    ExactControlQuotient X M Abar := by
  have hsumReward :
      Tendsto (fun n => εr n + ρr n) atTop (𝓝 0) := by
    simpa using hεr.add hρr
  have hsumTransition :
      Tendsto (fun n => εp n + ρp n) atTop (𝓝 0) := by
    simpa using hεp.add hρp
  apply exactControlQuotient_of_vanishing_defects
    f hf micro macroLimit hdiscountLimit
    (fun n => εr n + ρr n) (fun n => εp n + ρp n)
    hsumReward hsumTransition
  · intro n x a
    have hsrc := (Q n).reward_approx x a
    have hlim := hrewardLimit n (f x) a
    have htri :
        |micro.reward x a - macroLimit.reward (f x) a| ≤
          |micro.reward x a - (Q n).macroModel.reward (f x) a| +
            |(Q n).macroModel.reward (f x) a -
              macroLimit.reward (f x) a| := by
      have h := abs_add_le
        (micro.reward x a - (Q n).macroModel.reward (f x) a)
        ((Q n).macroModel.reward (f x) a -
          macroLimit.reward (f x) a)
      simpa [sub_add_sub_cancel] using h
    exact htri.trans (add_le_add hsrc hlim)
  · intro n x a
    let p : PMF M := pushforwardTransitionPMF f micro x a
    let q : PMF M := (Q n).macroModel.transitionPMF (f x) a
    let r : PMF M := macroLimit.transitionPMF (f x) a
    have htri := finite_tvDist_triangle p q r
    have hsrc := (Q n).transition_tv_approx x a
    have hlim := htransitionLimit n (f x) a
    exact htri.trans (add_le_add hsrc hlim)

/-- Frozen exact-control consequences at the limit of a convergent
P-CORE-01 fixed-source approximation sequence. -/
theorem p_quo_01_of_convergent_fixedSourceApproximation
    {X : Type uX} [Fintype X]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (f : X → M) (hf : Function.Surjective f)
    (micro : Model X (fun x => Abar (f x)))
    (macroLimit : Model M Abar)
    (hdiscountLimit : micro.discount = macroLimit.discount)
    (εr εp ρr ρp : ℕ → ℝ)
    (Q : ∀ n,
      UEOT.V3.CoreOperationalAssembly.FixedSourceApproximation
        f micro (εr n) (εp n))
    (hεr : Tendsto εr atTop (𝓝 0))
    (hεp : Tendsto εp atTop (𝓝 0))
    (hρr : Tendsto ρr atTop (𝓝 0))
    (hρp : Tendsto ρp atTop (𝓝 0))
    (hrewardLimit : ∀ n m (a : Abar m),
      |(Q n).macroModel.reward m a - macroLimit.reward m a| ≤ ρr n)
    (htransitionLimit : ∀ n m (a : Abar m),
      FiniteProbabilityRow.tvDist
        ((Q n).macroModel.transitionPMF m a)
        (macroLimit.transitionPMF m a) ≤ ρp n) :
    let E := exactControlQuotient_of_convergent_fixedSourceApproximation
      f hf micro macroLimit hdiscountLimit εr εp ρr ρp Q
      hεr hεp hρr hρp hrewardLimit htransitionLimit
    (∀ x : X, E.micro.optimalValue x =
        E.macroModel.optimalValue (E.f x)) ∧
    (∀ (x : X) (a : Abar (E.f x)),
      E.micro.qValue E.micro.optimalValue x a =
        E.macroModel.qValue E.macroModel.optimalValue (E.f x) a) ∧
    (∀ {t : ℕ} (x : X),
      CausalPolicy.infiniteValue
        (selectorPolicy (E.liftSelector E.macroModel.greedyAction))
        E.micro (t := t) x = E.micro.optimalValue x) ∧
    (∀ (π : CausalPolicy X (fun x => Abar (E.f x)))
        {t : ℕ} (h : π.Memory t),
      CausalPolicy.infiniteValue π E.micro h ≤
        E.micro.optimalValue (π.current h)) := by
  dsimp only
  exact (exactControlQuotient_of_convergent_fixedSourceApproximation
    f hf micro macroLimit hdiscountLimit εr εp ρr ρp Q
    hεr hεp hρr hρp hrewardLimit htransitionLimit).p_quo_01

end UEOT.V3.Compression.StructuralDefectControlLimit
