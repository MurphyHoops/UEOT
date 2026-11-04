import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionFreeTail

/-!
# Same-menu fixed-request comparison after the one-wallet first success

The comparator has exactly the same idle root/child requests, observations and
costs; it commits its address sequence in advance and may ignore the receipts.
Its best three-tick continuation is proved, not selected by testing only one
candidate. Stop commitments are included by their remaining-root-idle sequence.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionFixedTail

open RegisterJointDecisionSource RegisterJointDecisionConsumer
open RegisterJointDecisionFreeTail
open FiniteJointDecisionSolver FiniteJointDecisionFilteredModel

def fixedSchedule : (js : List Bool) → Table Act Obs js.length
  | [] => .halt
  | j :: js => .node (some (j,none)) (fun _ => fixedSchedule js)

def bitFixedValue (r d : ℚ) : List Bool → (Bool × Bool) → ℚ
  | [], _ => 0
  | j :: js, x =>
      r*((if selected x j then 1 else 0)+d*bitFixedValue r d js x) +
        (1-r)*d*bitFixedValue r d js (bitNext x j false)

theorem fixedSchedule_free : ∀ js, Free (fixedSchedule js) := by
  intro js
  induction js with
  | nil => trivial
  | cons j js ih =>
    refine ⟨?_,fun _ => ih⟩
    simp [cap,effective]

/-- The fixed comparator is executed in the same literal source. No hidden
state is exposed to this table; the projection appears only in its proof. -/
theorem fixedSchedule_source {Theta : Type} (P : Family Theta) :
    ∀ (js : List Bool) (w : World Theta), w.stopped = false → 2 ≤ w.store.length →
      sourceValue (source P) (gain P) P.discount (fixedSchedule js) w =
        bitFixedValue (P.normal w.theta) P.discount js (health P.goal w.store) := by
  intro js
  induction js with
  | nil => intro w hs hlen; rfl
  | cons j js ih =>
    intro w hs hlen
    let a : Act := some (j,none)
    have ha : cap a = 0 := by simp [a,cap,effective]
    have hx (mode : Bool) :
        health P.goal (step P.goal w a (mode,false)).store =
          bitNext (health P.goal w.store) j mode := by
      rw [step_health P.goal w a ha hlen]
      simp [a,effective,hs]
    have ho (mode : Bool) :
        observe P.goal w a (mode,false) = bitObs (health P.goal w.store) j mode := by
      rw [observe_free P.goal w a ha]
      simp [a,effective,hs]
    have ht (mode : Bool) :
        sourceValue (source P) (gain P) P.discount (fixedSchedule js)
          (step P.goal w a (mode,false)) =
        bitFixedValue (P.normal w.theta) P.discount js
          (bitNext (health P.goal w.store) j mode) := by
      rw [ih]
      · rw [hx]
        rfl
      · simp [step,a,hs]
      · rw [step_length]; omega
    change sourceValue (source P) (gain P) P.discount (.node a (fun _ => fixedSchedule js)) w = _
    rw [sourceValue_modes,ht true,ht false,ho true,ho false]
    simp [bitFixedValue,gain,charge,bitObs,bitNext]
    ring

/-- Exhaustion of both addresses for three fixed free requests. The two
nonoptimal patterns have gaps d*r*(1-r)*(1+d*r) and d*(1-d)*r*(1-r). -/
theorem fixed_three_upper (r d : ℚ) (hr : 0 ≤ r ∧ r ≤ 1)
    (hd : 0 ≤ d ∧ d ≤ 1) (j k l : Bool) :
    bitFixedValue r d [j,k,l] (true,true) ≤ r+d*r+d^2*r^2 := by
  have h₀ : 0 ≤ d*r*(1-r)*(1+d*r) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hd.1 hr.1) (sub_nonneg.mpr hr.2))
      (by nlinarith [mul_nonneg hd.1 hr.1])
  have h₁ : 0 ≤ d*(1-d)*r*(1-r) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hd.1 (sub_nonneg.mpr hd.2)) hr.1)
      (sub_nonneg.mpr hr.2)
  cases j <;> cases k <;> cases l <;>
    simp [bitFixedValue,selected,bitNext] <;> nlinarith

theorem alternating_fixed_attains (r d : ℚ) :
    bitFixedValue r d [false,true,false] (true,true) = r+d*r+d^2*r^2 := by
  simp [bitFixedValue,selected,bitNext]
  ring

theorem exact_feedback_improvement (r d : ℚ) :
    twoBound r d 3 - bitFixedValue r d [false,true,false] (true,true) =
      d^2*r^2*(1-r) := by
  rw [(twoBound_small r d).2.2,alternating_fixed_attains]
  ring

/-- Actual source comparison against EVERY committed three-address sequence. -/
theorem actual_fixed_three_upper {Theta : Type} (P : Family Theta) (w : World Theta)
    (hs : w.stopped = false) (hlen : 2 ≤ w.store.length)
    (hx : health P.goal w.store = (true,true)) (j k l : Bool) :
    sourceValue (source P) (gain P) P.discount (fixedSchedule [j,k,l]) w ≤
      P.normal w.theta + P.discount*P.normal w.theta +
        P.discount^2*(P.normal w.theta)^2 := by
  rw [fixedSchedule_source P _ w hs hlen,hx]
  exact fixed_three_upper _ _ (P.normal_bounds w.theta) P.discount_bounds _ _ _

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionFixedTail

