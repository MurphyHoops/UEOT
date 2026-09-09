import UEOT.Core.Prediction

/-! Deterministic controlled specialization of P-DYN-01. -/

namespace UEOT.Dynamics

universe u v w z
variable {X : Type u} {A : Type v} {Y : Type w} {Z : Type z}

def Closed (step : X → A → X) (f : X → Y) : Prop :=
  ∀ x y, f x = f y → ∀ a, f (step x a) = f (step y a)

def Intertwines (step : X → A → X) (coarseStep : Y → A → Y) (f : X → Y) : Prop :=
  ∀ x a, f (step x a) = coarseStep (f x) a

theorem intertwines_closed {step : X → A → X} {coarseStep : Y → A → Y}
    {f : X → Y} (h : Intertwines step coarseStep f) : Closed step f := by
  intro x y e a
  rw [h, h, e]

theorem intertwines_comp {step : X → A → X} {mid : Y → A → Y}
    {last : Z → A → Z} {f : X → Y} {g : Y → Z}
    (hf : Intertwines step mid f) (hg : Intertwines mid last g) :
    Intertwines step last (g ∘ f) := by
  intro x a
  change g (f (step x a)) = last (g (f x)) a
  rw [hf, hg]

def run (step : X → A → X) (x : X) : List A → X
  | [] => x
  | a :: as => run step (step x a) as

theorem run_append (step : X → A → X) (x : X) (as bs : List A) :
    run step x (as ++ bs) = run step (run step x as) bs := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih => exact ih (step x a)

theorem intertwines_run {step : X → A → X} {coarseStep : Y → A → Y}
    {f : X → Y} (h : Intertwines step coarseStep f) (x : X) (as : List A) :
    f (run step x as) = run coarseStep (f x) as := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih =>
    change f (run step (step x a) as) = run coarseStep (coarseStep (f x) a) as
    rw [ih, h]

theorem macro_unique {step : X → A → X} {m₁ m₂ : Y → A → Y}
    {f : X → Y} (surj : Function.Surjective f)
    (h₁ : Intertwines step m₁ f) (h₂ : Intertwines step m₂ f) : m₁ = m₂ := by
  funext y a
  obtain ⟨x, rfl⟩ := surj y
  exact (h₁ x a).symm.trans (h₂ x a)

noncomputable def macroOfClosed (step : X → A → X) (f : X → Y)
    (surj : Function.Surjective f) : Y → A → Y :=
  fun y a => f (step (Classical.choose (surj y)) a)

theorem macroOfClosed_intertwines {step : X → A → X} {f : X → Y}
    (surj : Function.Surjective f) (h : Closed step f) :
    Intertwines step (macroOfClosed step f surj) f := by
  intro x a
  exact h x (Classical.choose (surj (f x))) (Classical.choose_spec (surj (f x))).symm a

theorem closed_iff_exists_macro {step : X → A → X} {f : X → Y}
    (surj : Function.Surjective f) :
    Closed step f ↔ ∃ coarseStep, Intertwines step coarseStep f := by
  constructor
  · intro h
    exact ⟨macroOfClosed step f surj, macroOfClosed_intertwines surj h⟩
  · rintro ⟨coarseStep, h⟩
    exact intertwines_closed h

theorem closed_run {step : X → A → X} {f : X → Y} (h : Closed step f)
    {x y : X} (e : f x = f y) (as : List A) :
    f (run step x as) = f (run step y as) := by
  induction as generalizing x y with
  | nil => exact e
  | cons a as ih => exact ih (h x y e a)

end UEOT.Dynamics
