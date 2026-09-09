import Mathlib.Logic.Function.Basic

/-! Pointwise, set-theoretic foundation of P-PRED-01/02.
No measurability or almost-everywhere conclusion is asserted in this module. -/

namespace UEOT

universe u v w z

def FactorsThrough {X : Type u} {Y : Type v} {Z : Type w}
    (f : X → Y) (g : X → Z) : Prop :=
  ∃ decoder : Z → Y, ∀ x, f x = decoder (g x)

theorem factorsThrough_refl {X : Type u} {Y : Type v} (f : X → Y) :
    FactorsThrough f f := ⟨id, fun _ => rfl⟩

theorem factorsThrough_trans {X : Type u} {Y : Type v} {Z : Type w} {W : Type z}
    {f : X → Y} {g : X → Z} {h : X → W}
    (hfg : FactorsThrough f g) (hgh : FactorsThrough g h) : FactorsThrough f h := by
  obtain ⟨d, hd⟩ := hfg
  obtain ⟨e, he⟩ := hgh
  exact ⟨d ∘ e, fun x => by rw [hd, he]; rfl⟩

theorem factorsThrough_fiber {X : Type u} {Y : Type v} {Z : Type w}
    {f : X → Y} {g : X → Z} (h : FactorsThrough f g)
    {x y : X} (hxy : g x = g y) : f x = f y := by
  obtain ⟨d, hd⟩ := h
  rw [hd, hd, hxy]

namespace Prediction

variable {H : Type u} {I : Type v} {Y : Type w}

def canonical (K : H → I → Y) : H → (I → Y) := K

def equivalent (K : H → I → Y) (h h' : H) : Prop := ∀ i, K h i = K h' i

theorem equivalent_iff_canonical (K : H → I → Y) (h h' : H) :
    equivalent K h h' ↔ canonical K h = canonical K h' :=
  ⟨fun e => funext e, fun e i => congrFun e i⟩

def responseSetoid (K : H → I → Y) : Setoid H where
  r := equivalent K
  iseqv := ⟨fun _ _ => rfl, fun e i => (e i).symm,
    fun e₁ e₂ i => (e₁ i).trans (e₂ i)⟩

theorem coordinate_sufficient (K : H → I → Y) (i : I) :
    FactorsThrough (fun h => K h i) (canonical K) := ⟨fun c => c i, fun _ => rfl⟩

theorem canonical_minimal {S : Type z} (K : H → I → Y) (s : H → S)
    (L : S → I → Y) (hL : ∀ h i, K h i = L (s h) i) :
    FactorsThrough (canonical K) s := ⟨L, fun h => funext (hL h)⟩

theorem canonical_minimal_of_coordinates {S : Type z}
    (K : H → I → Y) (s : H → S)
    (hs : ∀ i, FactorsThrough (fun h => K h i) s) :
    FactorsThrough (canonical K) s := by
  classical
  exact canonical_minimal K s (fun t i => Classical.choose (hs i) t)
    (fun h i => Classical.choose_spec (hs i) h)

theorem restrict_equivalent {J : Type z} (K : H → I → Y) (r : J → I)
    {h h' : H} (e : equivalent K h h') :
    equivalent (fun x j => K x (r j)) h h' := fun j => e (r j)

theorem postprocess_equivalent {Z : Type z} (K : H → I → Y) (f : Y → Z)
    {h h' : H} (e : equivalent K h h') :
    equivalent (fun x i => f (K x i)) h h' := fun i => congrArg f (e i)

def lift {Z : Type z} (K : H → I → Y) (f : H → Z)
    (hf : ∀ h h', equivalent K h h' → f h = f h') :
    Quotient (responseSetoid K) → Z := Quotient.lift f hf

theorem lift_mk {Z : Type z} (K : H → I → Y) (f : H → Z)
    (hf : ∀ h h', equivalent K h h' → f h = f h') (h : H) :
    lift K f hf (Quotient.mk _ h) = f h := rfl

theorem lift_unique {Z : Type z} (K : H → I → Y) (f : H → Z)
    (hf : ∀ h h', equivalent K h h' → f h = f h')
    (g : Quotient (responseSetoid K) → Z)
    (hg : ∀ h, g (Quotient.mk _ h) = f h) : g = lift K f hf := by
  funext q
  induction q using Quotient.inductionOn with
  | h h => exact hg h

end Prediction
end UEOT
