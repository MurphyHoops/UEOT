import UEOT.V3.Compression.ValueSpanClosure

/-!
# Primitive reward -> automatic optimal-value span closure

The previous moving-GOA closure accepted a uniform bound on the macro optimal
value spans as an external premise.  For quotients of one common finite micro
model this bound is not primitive: the macro reward is already controlled by
the fixed micro reward envelope plus the quotient's reward defect.

This module proves the Bellman bound needed to make that dependence explicit.
-/

namespace UEOT.V3.Compression.PrimitiveRewardSpanClosure

open Filter Topology Function
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.ValueSpanClosure

universe uX uS uA

noncomputable section

/-- A finite discounted model whose actual rewards are bounded by `R` has its
optimal value uniformly bounded by `R / (1 - beta)`.  This uses the frozen
Bellman residual certificate at the zero function and does not rely on the
model's declared `rewardBound` field. -/
theorem Model.abs_optimalValue_le_of_reward_abs_le
    {S : Type uS} [Fintype S] [Nonempty S]
    {Act : S → Type uA} [∀ s, Fintype (Act s)] [∀ s, Nonempty (Act s)]
    (M : Model S Act)
    (R : ℝ) (hR0 : 0 ≤ R)
    (hReward : ∀ s a, |M.reward s a| ≤ R)
    (s : S) :
    |M.optimalValue s| ≤ R / (1 - M.discount) := by
  let z : S → ℝ := fun _ => 0
  have hbellPoint : ∀ x, |M.bellman z x| ≤ R := by
    intro x
    obtain ⟨a, ha_mem, ha⟩ :=
      Finset.exists_mem_eq_sup'
        (s := (Finset.univ : Finset (Act x)))
        Finset.univ_nonempty (fun a => M.qValue z x a)
    change |Finset.univ.sup' Finset.univ_nonempty (fun a : Act x => M.qValue z x a)| ≤ R
    rw [ha]
    simpa [Model.qValue, Model.expect, z] using hReward x a
  have hres : dist z (M.bellman z) ≤ R := by
    apply (dist_pi_le_iff hR0).2
    intro x
    simpa [Real.dist_eq, z, abs_neg] using hbellPoint x
  have hden : 0 ≤ 1 - M.discount := sub_nonneg.mpr M.discount_lt_one.le
  have hdist : dist z M.optimalValue ≤ R / (1 - M.discount) := by
    exact (M.valueError_le_residual z).trans
      (div_le_div_of_nonneg_right hres hden)
  have hs := dist_le_pi_dist z M.optimalValue s
  have habs : |M.optimalValue s| ≤ dist z M.optimalValue := by
    simpa [Real.dist_eq, z, abs_neg] using hs
  exact habs.trans hdist

/-- Pointwise absolute control gives a `2B` bound on finite-state span. -/
theorem span_le_two_mul_of_abs_le
    {S : Type uS} [Fintype S] [Nonempty S]
    (v : S → ℝ) (B : ℝ)
    (habs : ∀ s, |v s| ≤ B) :
    UEOT.V3.TVSpan.span v ≤ 2 * B := by
  have habove : BddAbove (Set.range v) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact (abs_le.mp (habs s)).2
  have hbelow : BddBelow (Set.range v) := by
    refine ⟨-B, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact (abs_le.mp (habs s)).1
  have hnonempty : (Set.range v).Nonempty := Set.range_nonempty v
  have hsup : sSup (Set.range v) ≤ B :=
    csSup_le hnonempty (fun y hy => by
      rcases hy with ⟨s, rfl⟩
      exact (abs_le.mp (habs s)).2)
  have hinf : -B ≤ sInf (Set.range v) :=
    le_csInf hnonempty (fun y hy => by
      rcases hy with ⟨s, rfl⟩
      exact (abs_le.mp (habs s)).1)
  unfold UEOT.V3.TVSpan.span
  linarith

/-- Actual reward control therefore yields an explicit optimal-value span bound. -/
theorem Model.optimalValue_span_le_of_reward_abs_le
    {S : Type uS} [Fintype S] [Nonempty S]
    {Act : S → Type uA} [∀ s, Fintype (Act s)] [∀ s, Nonempty (Act s)]
    (M : Model S Act)
    (R : ℝ) (hR0 : 0 ≤ R)
    (hReward : ∀ s a, |M.reward s a| ≤ R) :
    UEOT.V3.TVSpan.span M.optimalValue ≤
      2 * (R / (1 - M.discount)) := by
  exact span_le_two_mul_of_abs_le M.optimalValue
    (R / (1 - M.discount))
    (fun s => UEOT.V3.Compression.PrimitiveRewardSpanClosure.Model.abs_optimalValue_le_of_reward_abs_le M R hR0 hReward s)

variable {X : Type uX} [Fintype X] [Nonempty X]
variable {S : Type uS} [Fintype S] [Nonempty S]
variable {Act : Type uA} [Fintype Act] [Nonempty Act]

omit [Nonempty X] [Nonempty S] in
/-- A macro reward is bounded by the common micro model's declared reward
radius plus the primitive reward defect of this quotient. -/
theorem macroReward_abs_le_microBound_add_epsilon
    (Qref Qn : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Qref.micro = Qn.micro)
    (s : S) (a : Act) :
    |Qn.macroModel.reward s a| ≤ Qref.micro.rewardBound + Qn.epsilonReward := by
  rcases Qn.surjective s with ⟨x, rfl⟩
  have happrox := Qn.reward_approx x a
  have hmicro0 := Qn.micro.reward_abs_le x a
  have hmicro : |Qn.micro.reward x a| ≤ Qref.micro.rewardBound := by
    simpa [hMicro] using hmicro0
  have htri := abs_sub_le
    (Qn.macroModel.reward (Qn.f x) a)
    (Qn.micro.reward x a) 0
  calc
    |Qn.macroModel.reward (Qn.f x) a|
        = |Qn.macroModel.reward (Qn.f x) a - 0| := by ring_nf
    _ ≤ |Qn.macroModel.reward (Qn.f x) a - Qn.micro.reward x a| +
          |Qn.micro.reward x a - 0| := htri
    _ = |Qn.micro.reward x a - Qn.macroModel.reward (Qn.f x) a| +
          |Qn.micro.reward x a| := by rw [abs_sub_comm]; simp
    _ ≤ Qn.epsilonReward + Qref.micro.rewardBound := add_le_add happrox hmicro
    _ = Qref.micro.rewardBound + Qn.epsilonReward := by ring

/-- The moving macro optimal-value span has an explicit primitive envelope; no
uniform span hypothesis is required at one index. -/
theorem macroOptimalValue_span_le_primitiveEnvelope
    (Qref Qn : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Qref.micro = Qn.micro) :
    UEOT.V3.TVSpan.span Qn.macroModel.optimalValue ≤
      2 * ((Qref.micro.rewardBound + Qn.epsilonReward) /
        (1 - Qref.macroModel.discount)) := by
  let x0 : X := Classical.choice (inferInstance : Nonempty X)
  let a0 : Act := Classical.choice (inferInstance : Nonempty Act)
  have href0 : 0 ≤ Qref.micro.rewardBound :=
    (abs_nonneg (Qref.micro.reward x0 a0)).trans
      (Qref.micro.reward_abs_le x0 a0)
  have hR0 : 0 ≤ Qref.micro.rewardBound + Qn.epsilonReward :=
    add_nonneg href0 Qn.epsilonReward_nonneg
  have hspan := UEOT.V3.Compression.PrimitiveRewardSpanClosure.Model.optimalValue_span_le_of_reward_abs_le
    Qn.macroModel (Qref.micro.rewardBound + Qn.epsilonReward) hR0
    (macroReward_abs_le_microBound_add_epsilon Qref Qn hMicro)
  have hdisc := macroDiscount_eq_ref_of_commonMicro Qref Qn hMicro
  simpa [hdisc] using hspan


/-- Direct primitive envelope for the global P-QUO radius.  The macro value
span is eliminated in favor of the fixed micro reward radius and this
quotient's reward defect. -/
theorem D_le_primitiveEnvelope
    (Qref Qn : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Qref.micro = Qn.micro) :
    Qn.D ≤
      (Qn.epsilonReward +
        Qref.macroModel.discount * Qn.epsilonTransition *
          (2 * ((Qref.micro.rewardBound + Qn.epsilonReward) /
            (1 - Qref.macroModel.discount)))) /
        (1 - Qref.macroModel.discount) := by
  exact D_le_of_span_le Qref Qn hMicro
    (2 * ((Qref.micro.rewardBound + Qn.epsilonReward) /
      (1 - Qref.macroModel.discount)))
    (macroOptimalValue_span_le_primitiveEnvelope Qref Qn hMicro)

/-- Primitive reward/transition defects tending to zero force the P-QUO global
radius to zero for quotients of one common micro model.  The former external
uniform optimal-value-span hypothesis is derived internally and disappears. -/
theorem D_tendsto_zero_of_primitive_defects
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (hMicro : ∀ n, Qref.micro = (Qseq n).micro)
    (hR : Tendsto (fun n => (Qseq n).epsilonReward) atTop (𝓝 0))
    (hP : Tendsto (fun n => (Qseq n).epsilonTransition) atTop (𝓝 0)) :
    Tendsto (fun n => (Qseq n).D) atTop (𝓝 0) := by
  let beta := Qref.macroModel.discount
  let den := 1 - beta
  let Cseq : ℕ → ℝ := fun n =>
    2 * ((Qref.micro.rewardBound + (Qseq n).epsilonReward) / den)
  let upper : ℕ → ℝ := fun n =>
    ((Qseq n).epsilonReward +
      beta * (Qseq n).epsilonTransition * Cseq n) / den
  have hden : den ≠ 0 := by
    dsimp [den, beta]
    linarith [Qref.macroModel.discount_lt_one]
  have hC : Tendsto Cseq atTop
      (𝓝 (2 * (Qref.micro.rewardBound / den))) := by
    have hsum : Tendsto
        (fun n => Qref.micro.rewardBound + (Qseq n).epsilonReward)
        atTop (𝓝 (Qref.micro.rewardBound + 0)) :=
      tendsto_const_nhds.add hR
    have hdiv : Tendsto
        (fun n => (Qref.micro.rewardBound + (Qseq n).epsilonReward) / den)
        atTop (𝓝 ((Qref.micro.rewardBound + 0) / den)) :=
      hsum.div_const den
    have hmul := hdiv.const_mul 2
    simpa [Cseq] using hmul
  have htrans : Tendsto
      (fun n => beta * (Qseq n).epsilonTransition * Cseq n)
      atTop (𝓝 0) := by
    have hpC : Tendsto
        (fun n => (Qseq n).epsilonTransition * Cseq n)
        atTop (𝓝 (0 * (2 * (Qref.micro.rewardBound / den)))) :=
      hP.mul hC
    have hbeta := hpC.const_mul beta
    simpa [mul_assoc] using hbeta
  have hnum : Tendsto
      (fun n => (Qseq n).epsilonReward +
        beta * (Qseq n).epsilonTransition * Cseq n)
      atTop (𝓝 0) := by
    simpa using hR.add htrans
  have hupper0 : Tendsto upper atTop (𝓝 0) := by
    simpa [upper] using hnum.div_const den
  have hlower : ∀ n, 0 ≤ (Qseq n).D := fun n => (Qseq n).D_nonneg
  have hupper : ∀ n, (Qseq n).D ≤ upper n := by
    intro n
    simpa [upper, Cseq, beta, den] using
      D_le_primitiveEnvelope Qref (Qseq n) (hMicro n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper0
    (Filter.Eventually.of_forall hlower)
    (Filter.Eventually.of_forall hupper)


end
end UEOT.V3.Compression.PrimitiveRewardSpanClosure
