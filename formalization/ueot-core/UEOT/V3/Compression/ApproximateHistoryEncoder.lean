import UEOT.V3.Compression.ApproximateGoaTracking

/-!
# Approximate history encoder -> approximate control quotient

This module closes the main remaining certificate gap in the finite
approximate Agency -> near-GOD -> near-GOA chain.

Instead of assuming a macro control model together with reward/transition error
radii, start from one finite micro/history model and a surjective encoder

`C : H -> S`.

If reward values and pushed-forward next-state laws have uniformly small
diameter inside every encoder fibre, a canonical representative construction
produces a macro model on `S`.  The resulting object is an
`ApproxControlQuotient`, so the existing P-QUO-02 and near-GOA machinery can be
used without inserting independent approximation premises.
-/

namespace UEOT.V3.Compression.ApproximateHistoryEncoder

open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.ApproximateGoaTracking

universe uH uS uA

noncomputable local instance stateDecidableEq (S : Type uS) : DecidableEq S :=
  Classical.decEq S

/-- Canonical finite-PMF TV is nonnegative, with its discrete measurable
structure kept internal to the wrapper. -/
theorem finitePMFTV_nonneg {S : Type uS} (p q : PMF S) :
    0 ≤ FiniteProbabilityRow.tvDist p q := by
  letI : MeasurableSpace S := ⊤
  change 0 ≤ UEOT.V3.TotalVariation.tvDist p.toMeasure q.toMeasure
  exact UEOT.V3.TotalVariation.tvDist_nonneg _ _

/-- One chosen history representative for every encoded state. -/
noncomputable def representative
    {H : Type uH} {S : Type uS}
    (C : H → S) (hC : Function.Surjective C) : S → H :=
  fun s => Classical.choose (hC s)

theorem encoder_representative
    {H : Type uH} {S : Type uS}
    (C : H → S) (hC : Function.Surjective C) (s : S) :
    C (representative C hC s) = s :=
  Classical.choose_spec (hC s)

/-- Macro model obtained by reading reward and encoded transition law from one
chosen representative of each encoder fibre.

The action carrier is uniform in this first finite theorem.  State-dependent
action admissibility needs an additional fibre-compatibility layer and is not
silently assumed. -/
noncomputable def representativeMacroModel
    {H : Type uH} [Fintype H]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : H → S) (hC : Function.Surjective C)
    (micro : Model H (fun _ => Act)) :
    Model S (fun _ => Act) where
  transition := fun s a y =>
    fiberMass C (micro.transition (representative C hC s) a) y
  reward := fun s a => micro.reward (representative C hC s) a
  rewardBound := micro.rewardBound
  discount := micro.discount
  transition_nonneg := by
    intro s a y
    exact fiberMass_nonneg C
      (micro.transition (representative C hC s) a)
      (micro.transition_nonneg (representative C hC s) a) y
  transition_sum_one := by
    intro s a
    rw [sum_fiberMass, micro.transition_sum_one]
  reward_abs_le := by
    intro s a
    exact micro.reward_abs_le (representative C hC s) a
  discount_pos := micro.discount_pos
  discount_lt_one := micro.discount_lt_one

@[simp] theorem representativeMacroModel_reward
    {H : Type uH} [Fintype H]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : H → S) (hC : Function.Surjective C)
    (micro : Model H (fun _ => Act))
    (s : S) (a : Act) :
    (representativeMacroModel C hC micro).reward s a =
      micro.reward (representative C hC s) a := rfl

/-- The macro transition PMF is exactly the encoded micro row of the chosen
representative. -/
theorem representativeMacroModel_transitionPMF
    {H : Type uH} [Fintype H]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : H → S) (hC : Function.Surjective C)
    (micro : Model H (fun _ => Act))
    (s : S) (a : Act) :
    (representativeMacroModel C hC micro).transitionPMF s a =
      pushforwardTransitionPMF C micro (representative C hC s) a := by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ y) (PMF.apply_ne_top _ y)).mp
  simp [representativeMacroModel, pushforwardTransitionPMF_apply_toReal]

/-- Uniform within-fibre reward and transition-law diameters make the encoder
an approximate control quotient.

No independent macro approximation hypothesis is present: the macro model is
constructed from the same micro source and the same encoder. -/
noncomputable def approximateQuotientOfFiberDefects
    {H : Type uH} [Fintype H] [Nonempty H]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : H → S) (hC : Function.Surjective C)
    (micro : Model H (fun _ => Act))
    (εr εp : ℝ)
    (hrewardFiber : ∀ h h' a,
      C h = C h' →
        |micro.reward h a - micro.reward h' a| ≤ εr)
    (htransitionFiber : ∀ h h' a,
      C h = C h' →
        FiniteProbabilityRow.tvDist
          (pushforwardTransitionPMF C micro h a)
          (pushforwardTransitionPMF C micro h' a) ≤ εp) :
    ApproxControlQuotient H S (fun _ => Act) where
  f := C
  surjective := hC
  micro := micro
  macroModel := representativeMacroModel C hC micro
  discount_eq := rfl
  epsilonReward := εr
  epsilonTransition := εp
  epsilonReward_nonneg := by
    let h : H := Classical.choice inferInstance
    let a : Act := Classical.choice inferInstance
    have hbound := hrewardFiber h h a rfl
    exact (abs_nonneg (micro.reward h a - micro.reward h a)).trans hbound
  epsilonTransition_nonneg := by
    let h : H := Classical.choice inferInstance
    let a : Act := Classical.choice inferInstance
    let p := pushforwardTransitionPMF C micro h a
    have hbound := htransitionFiber h h a rfl
    exact (finitePMFTV_nonneg p p).trans hbound
  reward_approx := by
    intro h a
    change
      |micro.reward h a -
          micro.reward (representative C hC (C h)) a| ≤ εr
    apply hrewardFiber
    exact (encoder_representative C hC (C h)).symm
  transition_tv_approx := by
    intro h a
    rw [representativeMacroModel_transitionPMF]
    apply htransitionFiber
    exact (encoder_representative C hC (C h)).symm

/-- The constructed quotient's local approximation fields are definitionally
the supplied encoder-fibre radii. -/
@[simp] theorem approximateQuotientOfFiberDefects_epsilonReward
    {H : Type uH} [Fintype H] [Nonempty H]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : H → S) (hC : Function.Surjective C)
    (micro : Model H (fun _ => Act))
    (εr εp : ℝ)
    (hrewardFiber : ∀ h h' a,
      C h = C h' → |micro.reward h a - micro.reward h' a| ≤ εr)
    (htransitionFiber : ∀ h h' a,
      C h = C h' →
        FiniteProbabilityRow.tvDist
          (pushforwardTransitionPMF C micro h a)
          (pushforwardTransitionPMF C micro h' a) ≤ εp) :
    (approximateQuotientOfFiberDefects
      C hC micro εr εp hrewardFiber htransitionFiber).epsilonReward = εr := rfl

/-! ## End-to-end specialization -/

/-- Fibre-level representation defects generate a concrete approximate quotient
and therefore the full baseline near-GOD / time-varying near-GOA certificate.

This is the strongest current finite encoder theorem: reward and transition
approximation radii originate from within-encoder-fibre variation rather than
being postulated for an independently supplied macro model. -/
theorem fiberDefects_to_nearGod_nearGoa
    {H : Type uH} [Fintype H] [Nonempty H]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : H → S) (hC : Function.Surjective C)
    (micro : Model H (fun _ => Act))
    (εr εp : ℝ)
    (hrewardFiber : ∀ h h' a,
      C h = C h' →
        |micro.reward h a - micro.reward h' a| ≤ εr)
    (htransitionFiber : ∀ h h' a,
      C h = C h' →
        FiniteProbabilityRow.tvDist
          (pushforwardTransitionPMF C micro h a)
          (pushforwardTransitionPMF C micro h' a) ≤ εp)
    (halpha :
      let Q := approximateQuotientOfFiberDefects
        C hC micro εr εp hrewardFiber htransitionFiber
      dobrushinAlpha
        (policyMatrix Q.micro (approximateGodPolicy Q))
        (policyMatrix_rowStochastic Q.micro (approximateGodPolicy Q)) < 1)
    (Mseq : ℕ → Model H (fun _ => Act))
    (mu : ℕ → stdSimplex ℝ H)
    (hmu :
      let Q := approximateQuotientOfFiberDefects
        C hC micro εr εp hrewardFiber htransitionFiber
      ∀ n,
        mu (n + 1) =
          step
            (policyMatrix (Mseq n) (approximateGodPolicy Q))
            (policyMatrix_rowStochastic (Mseq n) (approximateGodPolicy Q))
            (mu n))
    (δ : ℕ → ℝ)
    (hrow :
      let Q := approximateQuotientOfFiberDefects
        C hC micro εr εp hrewardFiber htransitionFiber
      ∀ n x,
        crossRowTV
          (policyMatrix Q.micro (approximateGodPolicy Q))
          (policyMatrix_rowStochastic Q.micro (approximateGodPolicy Q))
          (policyMatrix (Mseq n) (approximateGodPolicy Q))
          (policyMatrix_rowStochastic (Mseq n) (approximateGodPolicy Q)) x ≤ δ n) :
    let Q := approximateQuotientOfFiberDefects
      C hC micro εr εp hrewardFiber htransitionFiber
    (∀ {t : ℕ} (h : H),
      0 ≤ Q.micro.optimalValue h -
        CausalPolicy.infiniteValue
          (selectorPolicy (Q.liftSelector Q.macroModel.greedyAction))
          Q.micro (t := t) h ∧
      Q.micro.optimalValue h -
        CausalPolicy.infiniteValue
          (selectorPolicy (Q.liftSelector Q.macroModel.greedyAction))
          Q.micro (t := t) h ≤ 2 * Q.D) ∧
    ∃ mustar : stdSimplex ℝ H,
      step
          (policyMatrix Q.micro (approximateGodPolicy Q))
          (policyMatrix_rowStochastic Q.micro (approximateGodPolicy Q))
          mustar = mustar ∧
      (∀ nu : stdSimplex ℝ H,
        step
            (policyMatrix Q.micro (approximateGodPolicy Q))
            (policyMatrix_rowStochastic Q.micro (approximateGodPolicy Q)) nu = nu →
          nu = mustar) ∧
      ∀ n,
        lawTV mustar (mu n) ≤
          dobrushinAlpha
              (policyMatrix Q.micro (approximateGodPolicy Q))
              (policyMatrix_rowStochastic Q.micro (approximateGodPolicy Q)) ^ n *
            lawTV mustar (mu 0) +
          ∑ k ∈ Finset.range n,
            δ k *
              dobrushinAlpha
                (policyMatrix Q.micro (approximateGodPolicy Q))
                (policyMatrix_rowStochastic Q.micro (approximateGodPolicy Q)) ^
                  (n - (k + 1)) := by
  dsimp only
  let Q := approximateQuotientOfFiberDefects
    C hC micro εr εp hrewardFiber htransitionFiber
  have hmain := approximate_god_and_timeVarying_near_goa
    Q (by simpa [Q] using halpha) Mseq mu
    (by simpa [Q] using hmu) δ
    (by simpa [Q] using hrow)
  simpa [Q] using hmain

end UEOT.V3.Compression.ApproximateHistoryEncoder
