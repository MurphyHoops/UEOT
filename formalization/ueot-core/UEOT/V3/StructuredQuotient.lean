import Mathlib

/-!
# P-INT-02 — canonical internal/environment quotient of a response kernel

For a response family K_i(x,e), define two pointwise equivalence relations:
two internal states are equivalent when every environment/protocol response
agrees, and dually for environment states. The response therefore descends to
the pair of quotient spaces. Any other exact separated representation must
refine these canonical quotients.

The proof is set-theoretic and in fact does not need finiteness; a final wrapper
retains the finite source assumptions literally.
-/

namespace UEOT.V3.StructuredQuotient

universe uX uE uI uR uS uU

variable {X : Type uX} {E : Type uE} {I : Type uI} {R : Type uR}

def internalSetoid (K : I → X → E → R) : Setoid X where
  r x x' := ∀ e i, K i x e = K i x' e
  iseqv := by
    constructor
    · intro x e i
      rfl
    · intro x x' h e i
      exact (h e i).symm
    · intro x y z hxy hyz e i
      exact (hxy e i).trans (hyz e i)

def environmentSetoid (K : I → X → E → R) : Setoid E where
  r e e' := ∀ x i, K i x e = K i x e'
  iseqv := by
    constructor
    · intro e x i
      rfl
    · intro e e' h x i
      exact (h x i).symm
    · intro e d e' hed hde x i
      exact (hed x i).trans (hde x i)

abbrev InternalClass (K : I → X → E → R) := Quotient (internalSetoid K)
abbrev EnvironmentClass (K : I → X → E → R) := Quotient (environmentSetoid K)

def internalClass (K : I → X → E → R) (x : X) : InternalClass K :=
  Quotient.mk (internalSetoid K) x

def environmentClass (K : I → X → E → R) (e : E) : EnvironmentClass K :=
  Quotient.mk (environmentSetoid K) e

/-- The response descends to the pair of canonical quotient classes. -/
def quotientResponse (K : I → X → E → R) (i : I) :
    InternalClass K → EnvironmentClass K → R :=
  Quotient.lift
    (fun x =>
      Quotient.lift
        (fun e => K i x e)
        (by
          intro e e' he
          exact he x i))
    (by
      intro x x' hx
      funext ec
      refine Quotient.inductionOn ec ?_
      intro e
      exact hx e i)

@[simp] theorem quotientResponse_mk
    (K : I → X → E → R) (i : I) (x : X) (e : E) :
    quotientResponse K i (internalClass K x) (environmentClass K e) =
      K i x e := by
  simp [quotientResponse, internalClass, environmentClass]

/-- Exact source factorization through the canonical internal/environment
quotients. -/
theorem canonical_factorization
    (K : I → X → E → R) :
    ∀ i x e,
      K i x e =
        quotientResponse K i (internalClass K x) (environmentClass K e) := by
  intro i x e
  exact (quotientResponse_mk K i x e).symm

/-- Any exact separated representation identifies only internally equivalent
microscopic states. Hence it refines the canonical internal quotient. -/
theorem internal_refinement
    {S : Type uS} {U : Type uU}
    (K : I → X → E → R)
    (f : X → S) (g : E → U) (Q : I → S → U → R)
    (hfac : ∀ i x e, K i x e = Q i (f x) (g e)) :
    ∀ {x x'}, f x = f x' → (internalSetoid K).r x x' := by
  intro x x' hxx e i
  rw [hfac i x e, hfac i x' e, hxx]

/-- Dually, any exact separated representation refines the canonical
environment quotient. -/
theorem environment_refinement
    {S : Type uS} {U : Type uU}
    (K : I → X → E → R)
    (f : X → S) (g : E → U) (Q : I → S → U → R)
    (hfac : ∀ i x e, K i x e = Q i (f x) (g e)) :
    ∀ {e e'}, g e = g e' → (environmentSetoid K).r e e' := by
  intro e e' hee x i
  rw [hfac i x e, hfac i x e', hee]

/-- Literal finite-source wrapper for P-INT-02. -/
theorem p_int_02
    [Fintype X] [Fintype E] [Fintype I]
    (K : I → X → E → R) :
    (∀ i x e,
      K i x e =
        quotientResponse K i (internalClass K x) (environmentClass K e)) ∧
    (∀ {S : Type uS} {U : Type uU}
      (f : X → S) (g : E → U) (Q : I → S → U → R),
      (∀ i x e, K i x e = Q i (f x) (g e)) →
      (∀ {x x'}, f x = f x' → (internalSetoid K).r x x') ∧
      (∀ {e e'}, g e = g e' → (environmentSetoid K).r e e')) := by
  refine ⟨canonical_factorization K, ?_⟩
  intro S U f g Q hfac
  exact ⟨internal_refinement K f g Q hfac,
    environment_refinement K f g Q hfac⟩

end UEOT.V3.StructuredQuotient
