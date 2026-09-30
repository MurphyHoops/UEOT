import UEOT.V3.Compression.MovingEncoderGaugeClosure
import UEOT.V3.FiniteDiscountedExactQuotient

/-!
# Quotient gauge -> exact control-semantic gauge

Representation gauge should not stop at equality of source fibres.  For exact
control quotients of the same micro model, the canonical M-QD quotient
relabeling transports the entire macro control semantics:

* reward;
* transition rows;
* optimal value;
* optimal action value;
* Bellman-optimal action sets.

The final theorem combines this with moving-encoder gauge closure: under one
finite full-support source law, weighted gauge mismatch tending to zero forces
eventual exact control-semantic equivalence, provided the compared exact
quotients share the same micro model.

Canonical `greedyAction` values are not claimed to be literally equal across
relabelings: tied argmaxes may be selected differently.  Instead, a greedy
action chosen on one quotient is proved Bellman-optimal on the relabeled state
of the other quotient.
-/

namespace UEOT.V3.Compression.GaugeSemanticTransfer

open Filter Topology Function
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.QuotientGauge
open UEOT.V3.Compression.WeightedQuotientGauge
open UEOT.V3.Compression.MovingEncoderGaugeClosure

universe uX uS uA

noncomputable section

variable {X : Type uX} [Fintype X] [Nonempty X]
variable {S : Type uS} [Fintype S]
variable {Act : Type uA} [Fintype Act] [Nonempty Act]

/-- Fibre mass is invariant under a bijective relabeling of quotient states. -/
theorem fiberMass_relabel
    (q r : X → S) (e : S ≃ S)
    (he : e ∘ q = r)
    (p : X → ℝ) (s : S) :
    fiberMass q p s = fiberMass r p (e s) := by
  classical
  unfold fiberMass
  apply Finset.sum_congr rfl
  intro x hx
  have hxr : e (q x) = r x := by
    simpa only [Function.comp_apply] using congrFun he x
  by_cases hqs : q x = s
  · have hrs : r x = e s := by simpa [hqs] using hxr.symm
    simp [hqs, hrs]
  · have hrs : r x ≠ e s := by
      intro hrs
      apply hqs
      apply e.injective
      calc
        e (q x) = r x := hxr
        _ = e s := hrs
    simp [hqs, hrs]

/-- Exact semantic content transported by one quotient-state relabeling. -/
def SemanticRelabel
    (Q R : ExactControlQuotient X S (fun _ => Act))
    (e : S ≃ S) : Prop :=
  e ∘ Q.f = R.f ∧
  (∀ s a,
    Q.macroModel.reward s a = R.macroModel.reward (e s) a) ∧
  (∀ s a t,
    Q.macroModel.transition s a t =
      R.macroModel.transition (e s) a (e t)) ∧
  (∀ s,
    Q.macroModel.optimalValue s = R.macroModel.optimalValue (e s)) ∧
  (∀ s a,
    Q.macroModel.qValue Q.macroModel.optimalValue s a =
      R.macroModel.qValue R.macroModel.optimalValue (e s) a) ∧
  (∀ s,
    R.macroModel.qValue R.macroModel.optimalValue (e s)
        (Q.macroModel.greedyAction s) =
      R.macroModel.optimalValue (e s))

/-- Two exact quotients of the same micro model with identical source fibres
have one unique quotient-state relabeling, and that relabeling transports the
full exact control semantics.

Uniqueness is representation-theoretic: any semantic relabeling must in
particular transport `Q.f` to `R.f`, so M-QD quotient gauge uniqueness applies.
-/
theorem existsUnique_semanticRelabel_of_sameFibers
    (Q R : ExactControlQuotient X S (fun _ => Act))
    (hMicro : Q.micro = R.micro)
    (hsame : SameFibers Q.f R.f) :
    ∃! e : S ≃ S, SemanticRelabel Q R e := by
  let e : S ≃ S := quotientEquiv Q.f R.f Q.surjective R.surjective hsame
  have he : e ∘ Q.f = R.f :=
    quotientEquiv_comp Q.f R.f Q.surjective R.surjective hsame
  have hrelabel_reward : ∀ s a,
      Q.macroModel.reward s a = R.macroModel.reward (e s) a := by
    intro s a
    rcases Q.surjective s with ⟨x, rfl⟩
    have hex : e (Q.f x) = R.f x := by
      simpa only [Function.comp_apply] using congrFun he x
    calc
      Q.macroModel.reward (Q.f x) a = Q.micro.reward x a :=
        (Q.reward_closed x a).symm
      _ = R.micro.reward x a := by rw [hMicro]
      _ = R.macroModel.reward (R.f x) a := R.reward_closed x a
      _ = R.macroModel.reward (e (Q.f x)) a := by rw [hex]
  have hrelabel_transition : ∀ s a t,
      Q.macroModel.transition s a t =
        R.macroModel.transition (e s) a (e t) := by
    intro s a t
    rcases Q.surjective s with ⟨x, rfl⟩
    have hex : e (Q.f x) = R.f x := by
      simpa only [Function.comp_apply] using congrFun he x
    calc
      Q.macroModel.transition (Q.f x) a t =
          fiberMass Q.f (Q.micro.transition x a) t :=
        (Q.transition_closed x a t).symm
      _ = fiberMass R.f (Q.micro.transition x a) (e t) :=
        fiberMass_relabel Q.f R.f e he (Q.micro.transition x a) t
      _ = fiberMass R.f (R.micro.transition x a) (e t) := by
        rw [hMicro]
      _ = R.macroModel.transition (R.f x) a (e t) :=
        R.transition_closed x a (e t)
      _ = R.macroModel.transition (e (Q.f x)) a (e t) := by rw [hex]
  have hrelabel_value : ∀ s,
      Q.macroModel.optimalValue s = R.macroModel.optimalValue (e s) := by
    intro s
    rcases Q.surjective s with ⟨x, rfl⟩
    have hex : e (Q.f x) = R.f x := by
      simpa only [Function.comp_apply] using congrFun he x
    calc
      Q.macroModel.optimalValue (Q.f x) = Q.micro.optimalValue x :=
        (Q.optimalValue_apply x).symm
      _ = R.micro.optimalValue x := by rw [hMicro]
      _ = R.macroModel.optimalValue (R.f x) := R.optimalValue_apply x
      _ = R.macroModel.optimalValue (e (Q.f x)) := by rw [hex]
  have hrelabel_qValue : ∀ s a,
      Q.macroModel.qValue Q.macroModel.optimalValue s a =
        R.macroModel.qValue R.macroModel.optimalValue (e s) a := by
    intro s a
    rcases Q.surjective s with ⟨x, rfl⟩
    have hex : e (Q.f x) = R.f x := by
      simpa only [Function.comp_apply] using congrFun he x
    calc
      Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a =
          Q.micro.qValue Q.micro.optimalValue x a :=
        (Q.optimal_qValue_pullback x a).symm
      _ = R.micro.qValue R.micro.optimalValue x a := by rw [hMicro]
      _ = R.macroModel.qValue R.macroModel.optimalValue (R.f x) a :=
        R.optimal_qValue_pullback x a
      _ = R.macroModel.qValue R.macroModel.optimalValue (e (Q.f x)) a := by
        rw [hex]
  have hgreedy : ∀ s,
      R.macroModel.qValue R.macroModel.optimalValue (e s)
          (Q.macroModel.greedyAction s) =
        R.macroModel.optimalValue (e s) := by
    intro s
    calc
      R.macroModel.qValue R.macroModel.optimalValue (e s)
          (Q.macroModel.greedyAction s) =
          Q.macroModel.qValue Q.macroModel.optimalValue s
            (Q.macroModel.greedyAction s) :=
        (hrelabel_qValue s (Q.macroModel.greedyAction s)).symm
      _ = Q.macroModel.optimalValue s := Q.macroModel.greedyAction_spec s
      _ = R.macroModel.optimalValue (e s) := hrelabel_value s
  refine ⟨e, ⟨he, hrelabel_reward, hrelabel_transition,
    hrelabel_value, hrelabel_qValue, hgreedy⟩, ?_⟩
  intro e' he'
  exact quotientEquiv_unique Q.f R.f Q.surjective R.surjective hsame e' he'.1

/-- Moving-encoder representation closure upgrades to eventual exact control
semantic closure when each compared quotient is exact and shares the same
micro model as the reference quotient.

The conclusion is deliberately eventual and gauge-invariant: from some finite
index onward there exists one unique state relabeling transporting the complete
exact quotient semantics. -/
theorem eventually_existsUnique_semanticRelabel_of_weightedGauge_tendsto_zero
    (mu : stdSimplex ℝ X)
    (hfull : ∀ x, 0 < mu x)
    (Qref : ExactControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ExactControlQuotient X S (fun _ => Act))
    (hMicro : ∀ n, (Qseq n).micro = Qref.micro)
    (hconv :
      Tendsto
        (fun n => weightedGaugeMismatch mu (Qseq n).f Qref.f)
        atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      ∃! e : S ≃ S, SemanticRelabel (Qseq n) Qref e := by
  have hsame : ∀ᶠ n in atTop, SameFibers (Qseq n).f Qref.f :=
    eventually_sameFibers_of_weightedGaugeMismatch_tendsto_zero
      mu hfull Qref.f Qref.surjective
      (fun n => (Qseq n).f) (fun n => (Qseq n).surjective) hconv
  filter_upwards [hsame] with n hn
  exact existsUnique_semanticRelabel_of_sameFibers
    (Qseq n) Qref (hMicro n) hn

end


end UEOT.V3.Compression.GaugeSemanticTransfer
