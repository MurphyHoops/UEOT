import UEOTQM.QuantumPurification
import UEOTQM.ClassicalSector
import UEOTQM.CorePurificationBoundary
import UEOTQM.RealLocalTomography

/-!
# Actual finite operational models and separate candidate principles

The presentation contains operations, while its elementary laws are proved in a
separate package. Purification and local tomography are independent predicates,
never constructor fields. The three adapters use the entire classical simplex,
the entire real positive trace-one subspace, and the entire complex density
space, respectively. The product carrier is literally a Cartesian product.
-/

namespace UEOTQM.OperationalSystems

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

noncomputable section

/-- A concrete finite carrier; empty carriers are allowed. -/
structure FiniteSystem where
  Carrier : Type
  finite : Fintype Carrier
  decidableEq : DecidableEq Carrier

attribute [instance] FiniteSystem.finite FiniteSystem.decidableEq

instance finiteSystemCoeSort : CoeSort FiniteSystem Type := ⟨FiniteSystem.Carrier⟩

def FiniteSystem.of (ι : Type) [Fintype ι] [DecidableEq ι] : FiniteSystem :=
  ⟨ι, inferInstance, inferInstance⟩

def FiniteSystem.product (A B : FiniteSystem) : FiniteSystem :=
  FiniteSystem.of (A × B)

universe p

/-- Actual operations only. The process universe can contain a bundled finite
Kraus index. No purification, tomography, or uniqueness law is an input. -/
structure Presentation where
  State : FiniteSystem → Type
  Effect : FiniteSystem → Type
  probability : {A : FiniteSystem} → Effect A → State A → ℝ
  mix : {A : FiniteSystem} → (t : ℝ) → 0 ≤ t → t ≤ 1 → State A → State A → State A
  productState : {A B : FiniteSystem} → State A → State B → State (A.product B)
  productEffect : {A B : FiniteSystem} → Effect A → Effect B → Effect (A.product B)
  Process : FiniteSystem → FiniteSystem → Type p
  act : {A B : FiniteSystem} → Process A B → State A → State B
  identity : (A : FiniteSystem) → Process A A
  compose : {A B C : FiniteSystem} → Process B C → Process A B → Process A C
  discardProcess : (A B : FiniteSystem) → Process (A.product B) A

def Presentation.discardRight (M : Presentation.{p}) {A B : FiniteSystem}
    (ρ : M.State (A.product B)) : M.State A := M.act (M.discardProcess A B) ρ

/-- Elementary operational laws, to be proved for each concrete presentation. -/
structure Laws (M : Presentation.{p}) : Prop where
  probability_bounds : ∀ {A} (E : M.Effect A) (ρ : M.State A),
    0 ≤ M.probability E ρ ∧ M.probability E ρ ≤ 1
  probability_mix : ∀ {A} (E : M.Effect A) t ht0 ht1 (ρ σ : M.State A),
    M.probability E (M.mix t ht0 ht1 ρ σ) =
      t * M.probability E ρ + (1 - t) * M.probability E σ
  product_probability : ∀ {A B} (E : M.Effect A) (F : M.Effect B)
      (ρ : M.State A) (σ : M.State B),
    M.probability (M.productEffect E F) (M.productState ρ σ) =
      M.probability E ρ * M.probability F σ
  discard_product : ∀ {A B} (ρ : M.State A) (σ : M.State B),
    M.discardRight (M.productState ρ σ) = ρ
  act_mix : ∀ {A B} (C : M.Process A B) t ht0 ht1 (ρ σ : M.State A),
    M.act C (M.mix t ht0 ht1 ρ σ) = M.mix t ht0 ht1 (M.act C ρ) (M.act C σ)
  identity_act : ∀ {A} (ρ : M.State A), M.act (M.identity A) ρ = ρ
  compose_act : ∀ {A B C} (D : M.Process B C) (E : M.Process A B) (ρ : M.State A),
    M.act (M.compose D E) ρ = M.act D (M.act E ρ)

/-- Convex extremality quantifies over every normalized state in the model. -/
def IsPure (M : Presentation.{p}) {A : FiniteSystem} (ρ : M.State A) : Prop :=
  ∀ (σ τ : M.State A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1),
    ρ = M.mix t ht0.le ht1.le σ τ → σ = ρ ∧ τ = ρ

def Purifies (M : Presentation.{p}) {A B : FiniteSystem}
    (Ψ : M.State (A.product B)) (ρ : M.State A) : Prop :=
  IsPure M Ψ ∧ M.discardRight Ψ = ρ

/-- A candidate principle, separate from presentation and basic laws. -/
def PurificationExistence (M : Presentation.{p}) : Prop :=
  ∀ (A : FiniteSystem) (ρ : M.State A),
    ∃ (B : FiniteSystem) (Ψ : M.State (A.product B)), Purifies M Ψ ρ

/-- A second independent candidate principle: all local product tests separate. -/
def LocalTomography (M : Presentation.{p}) : Prop :=
  ∀ (A B : FiniteSystem) (ρ σ : M.State (A.product B)),
    (∀ (E : M.Effect A) (F : M.Effect B),
      M.probability (M.productEffect E F) ρ =
        M.probability (M.productEffect E F) σ) → ρ = σ

namespace ClassicalModel

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

def product (p : Classical.State X) (q : Classical.State Y) : Classical.State (X × Y) where
  weight xy := p.weight xy.1 * q.weight xy.2
  nonneg xy := mul_nonneg (p.nonneg xy.1) (q.nonneg xy.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, q.sum_one, mul_one, p.sum_one]

def productEffect (e : Classical.Effect X) (f : Classical.Effect Y) :
    Classical.Effect (X × Y) where
  response xy := e.response xy.1 * f.response xy.2
  nonneg xy := mul_nonneg (e.nonneg xy.1) (f.nonneg xy.2)
  le_one xy := by
    calc
      e.response xy.1 * f.response xy.2 ≤ 1 * f.response xy.2 :=
        mul_le_mul_of_nonneg_right (e.le_one xy.1) (f.nonneg xy.2)
      _ ≤ 1 := by simpa using f.le_one xy.2

/-- Every stochastic kernel is an actual classical process. -/
def act (K : X → Classical.State Y) (p : Classical.State X) : Classical.State Y where
  weight y := ∑ x, p.weight x * (K x).weight y
  nonneg y := Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) ((K x).nonneg y)
  sum_one := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, Mixture.Weights.sum_one, mul_one]

theorem probability_mix (e : Classical.Effect X) t ht0 ht1 (p q : Classical.State X) :
    Classical.evaluate (Classical.mix t ht0 ht1 p q) e =
      t * Classical.evaluate p e + (1 - t) * Classical.evaluate q e := by
  simp only [Classical.evaluate, Classical.mix_weight, add_mul,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]

theorem product_probability (e : Classical.Effect X) (f : Classical.Effect Y)
    (p : Classical.State X) (q : Classical.State Y) :
    Classical.evaluate (product p q) (productEffect e f) =
      Classical.evaluate p e * Classical.evaluate q f := by
  simp only [Classical.evaluate, product, productEffect, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem marginal_product (p : Classical.State X) (q : Classical.State Y) :
    Classical.marginalLeft (product p q) = p := by
  apply Classical.state_ext
  intro x
  change (∑ y, p.weight x * q.weight y) = p.weight x
  rw [← Finset.mul_sum, q.sum_one, mul_one]

theorem act_discard (p : Classical.State (X × Y)) :
    act (fun xy => Classical.dirac xy.1) p = Classical.marginalLeft p := by
  classical
  apply Classical.state_ext
  intro x
  simp only [act, Classical.dirac_weight, Classical.marginalLeft_weight]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp

theorem act_mix (K : X → Classical.State Y) t ht0 ht1 (p q : Classical.State X) :
    act K (Classical.mix t ht0 ht1 p q) =
      Classical.mix t ht0 ht1 (act K p) (act K q) := by
  apply Classical.state_ext
  intro y
  simp only [act, Classical.mix_weight, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]

theorem act_identity (p : Classical.State X) : act Classical.dirac p = p := by
  classical
  apply Classical.state_ext
  intro x
  simp [act, Classical.dirac_weight]

theorem act_comp (L : Y → Classical.State Z) (K : X → Classical.State Y)
    (p : Classical.State X) : act (fun x => act L (K x)) p = act L (act K p) := by
  apply Classical.state_ext
  intro z
  simp only [act, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

end ClassicalModel

/-- Full finite classical state spaces, with all stochastic kernels. -/
def classicalModel : Presentation.{0} where
  State A := Classical.State A
  Effect A := Classical.Effect A
  probability E ρ := Classical.evaluate ρ E
  mix := Classical.mix
  productState := ClassicalModel.product
  productEffect := ClassicalModel.productEffect
  Process A B := A → Classical.State B
  act := ClassicalModel.act
  identity _ := Classical.dirac
  compose D E x := ClassicalModel.act D (E x)
  discardProcess _ _ xy := Classical.dirac xy.1

theorem classical_laws : Laws classicalModel where
  probability_bounds E ρ := ⟨Classical.evaluate_nonneg ρ E, Classical.evaluate_le_one ρ E⟩
  probability_mix := ClassicalModel.probability_mix
  product_probability := ClassicalModel.product_probability
  discard_product ρ σ := (ClassicalModel.act_discard _).trans
    (ClassicalModel.marginal_product ρ σ)
  act_mix := ClassicalModel.act_mix
  identity_act := ClassicalModel.act_identity
  compose_act := ClassicalModel.act_comp

theorem classical_pure_iff {A : FiniteSystem} (ρ : Classical.State A) :
    IsPure classicalModel ρ ↔ Classical.IsPure ρ := by
  constructor
  · intro h σ τ t ht0 ht1 heq
    exact h σ τ t ht0 ht1 (Classical.state_ext heq)
  · intro h σ τ t ht0 ht1 heq
    apply h σ τ t ht0 ht1
    intro x
    exact congrArg (fun p : Classical.State A => p.weight x) heq

theorem classical_discard_eq {A B : FiniteSystem} (ρ : Classical.State (A × B)) :
    classicalModel.discardRight (A := A) (B := B) ρ = Classical.marginalLeft ρ :=
  ClassicalModel.act_discard ρ

theorem classical_not_purification : ¬ PurificationExistence classicalModel := by
  intro h
  let A := FiniteSystem.of (Fin 2)
  obtain ⟨B, Ψ, hp, hm⟩ := h A
    (Classical.halfMix (Classical.dirac (0 : Fin 2)) (Classical.dirac (1 : Fin 2)))
  apply Classical.no_pure_extension_halfMix (B := B) (x := (0 : Fin 2))
    (y := 1) (by decide)
  refine ⟨Ψ, (classical_pure_iff Ψ).mp hp, ?_⟩
  exact (classical_discard_eq Ψ).symm.trans hm

/-- This is the previously proved actual Core terminal quotient carrier. -/
def coreSystem : FiniteSystem := by
  classical
  exact FiniteSystem.of CorePurificationBoundary.Terminal

/-- The state here is the actual first terminal-quotient path marginal from the
Core boundary module, with its finite-interface scope unchanged. -/
theorem core_first_marginal_no_purifies (B : FiniteSystem) :
    ¬ ∃ Ψ : classicalModel.State (coreSystem.product B),
      Purifies classicalModel Ψ CorePurificationBoundary.firstQuotientState := by
  rintro ⟨Ψ, hp, hm⟩
  apply CorePurificationBoundary.firstQuotientState_no_pure_extension B
  exact ⟨Ψ, (classical_pure_iff Ψ).mp hp, (classical_discard_eq Ψ).symm.trans hm⟩

/-- Finite Kraus data with actual typed input and output; arbitrary positive maps
are not admitted as quantum processes. -/
structure QuantumProcess (A B : FiniteSystem) where
  environment : FiniteSystem
  channel : RectangularChannel A B environment

namespace QuantumModel

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem trace_product_im_zero {E X : Operator ι} (hE : E.PosSemidef)
    (hX : X.PosSemidef) : (E * X).trace.im = 0 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hE.nonneg
  rw [hB]
  change (Bᴴ * B * X).trace.im = 0
  rw [← Matrix.trace_mul_cycle B X Bᴴ]
  exact trace_im_eq_zero (hX.mul_mul_conjTranspose_same B)

theorem product_probability (E : Effect ι) (F : Effect α)
    (ρ : Density ι) (σ : Density α) :
    (RealLocalTomography.productEffect E F).probability (QuantumPurification.product ρ σ) =
      E.probability ρ * F.probability σ := by
  change ((E.matrix ⊗ₖ F.matrix) * (ρ.matrix ⊗ₖ σ.matrix)).trace.re =
    (E.matrix * ρ.matrix).trace.re * (F.matrix * σ.matrix).trace.re
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, Complex.mul_re,
    trace_product_im_zero E.positive ρ.positive,
    trace_product_im_zero F.positive σ.positive, zero_mul, sub_zero]

end QuantumModel

/-- Full finite complex densities, full quantum effects, and finite Kraus maps. -/
def complexModel : Presentation.{1} where
  State A := Density A
  Effect A := UEOTQM.Effect A
  probability E ρ := E.probability ρ
  mix := QuantumPurification.mix
  productState := QuantumPurification.product
  productEffect := RealLocalTomography.productEffect
  Process := QuantumProcess
  act C := C.channel.state
  identity A := ⟨FiniteSystem.of Unit, RectangularChannel.identity A⟩
  compose D E := ⟨D.environment.product E.environment, D.channel.comp E.channel⟩
  discardProcess A B := ⟨B, RectangularChannel.discardRight A B⟩

theorem complex_laws : Laws complexModel where
  probability_bounds E ρ := ⟨E.probability_nonneg ρ, E.probability_le_one ρ⟩
  probability_mix := QuantumPurification.probability_mix
  product_probability := QuantumModel.product_probability
  discard_product := QuantumPurification.discard_product
  act_mix C := QuantumPurification.state_mix C.channel
  identity_act := RectangularChannel.identity_state
  compose_act D E := RectangularChannel.comp_state D.channel E.channel

theorem complex_pure_iff {A : FiniteSystem} (ρ : Density A) :
    IsPure complexModel ρ ↔ QuantumPurification.IsPure ρ := by
  constructor
  · intro h σ τ t ht0 ht1 heq
    exact h σ τ t ht0 ht1 (Density.ext heq)
  · intro h σ τ t ht0 ht1 heq
    exact h σ τ t ht0 ht1 (congrArg Density.matrix heq)

/-- The candidate existence principle is a theorem of this concrete complex
model, with the whole density space and the actual partial trace. -/
theorem complex_purification : PurificationExistence complexModel := by
  intro A ρ
  refine ⟨A, QuantumPurification.purification ρ, ?_, ?_⟩
  · exact (complex_pure_iff _).mpr (QuantumPurification.purification_isPure ρ)
  · exact QuantumPurification.purification_marginal ρ

namespace RealModel

/-- Entrywise reality also applies to rectangular Kraus matrices. -/
def IsRealMatrix {ι α : Type*} (X : Matrix ι α ℂ) : Prop := ∀ i j, (X i j).im = 0

theorem real_add {ι α : Type*} {X Y : Matrix ι α ℂ}
    (hX : IsRealMatrix X) (hY : IsRealMatrix Y) : IsRealMatrix (X + Y) := by
  intro i j
  simp [Matrix.add_apply, hX i j, hY i j]

theorem real_smul {ι α : Type*} (r : ℝ) {X : Matrix ι α ℂ}
    (hX : IsRealMatrix X) : IsRealMatrix (r • X) := by
  intro i j
  simp [Matrix.smul_apply, hX i j]

theorem real_mul {ι α β : Type*} [Fintype α] {X : Matrix ι α ℂ} {Y : Matrix α β ℂ}
    (hX : IsRealMatrix X) (hY : IsRealMatrix Y) : IsRealMatrix (X * Y) := by
  unfold IsRealMatrix at hX hY ⊢
  intro i j
  simp [Matrix.mul_apply, Complex.mul_im, hX, hY]

theorem real_conjTranspose {ι α : Type*} {X : Matrix ι α ℂ}
    (hX : IsRealMatrix X) : IsRealMatrix Xᴴ := by
  intro i j
  simp [Matrix.conjTranspose_apply, hX j i]

theorem real_kronecker {ι α : Type*} {X : Operator ι} {Y : Operator α}
    (hX : IsRealMatrix X) (hY : IsRealMatrix Y) : IsRealMatrix (X ⊗ₖ Y) := by
  intro i j
  simp [Complex.mul_im, hX i.1 j.1, hY i.2 j.2]

abbrev State (A : FiniteSystem) := {ρ : Density A // RealLocalTomography.IsReal ρ.matrix}
abbrev Effect (A : FiniteSystem) := {E : UEOTQM.Effect A // RealLocalTomography.IsReal E.matrix}

def mix {A : FiniteSystem} (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ρ σ : State A) : State A :=
  ⟨QuantumPurification.mix t ht0 ht1 ρ.1 σ.1,
    real_add (real_smul t ρ.2) (real_smul (1 - t) σ.2)⟩

def product {A B : FiniteSystem} (ρ : State A) (σ : State B) : State (A.product B) :=
  ⟨QuantumPurification.product ρ.1 σ.1, real_kronecker ρ.2 σ.2⟩

def productEffect {A B : FiniteSystem} (E : Effect A) (F : Effect B) : Effect (A.product B) :=
  ⟨RealLocalTomography.productEffect E.1 F.1, real_kronecker E.2 F.2⟩

/-- These are finite real Kraus processes, not arbitrary affine positive maps. -/
structure Process (A B : FiniteSystem) where
  environment : FiniteSystem
  channel : RectangularChannel A B environment
  real_kraus : ∀ k, IsRealMatrix (channel.kraus k)

theorem operator_real {A B : FiniteSystem} (C : Process A B) {X : Operator A}
    (hX : IsRealMatrix X) : IsRealMatrix (C.channel.operator X) := by
  intro i j
  simp only [RectangularChannel.operator, Matrix.sum_apply]
  have h : ∀ k, ((C.channel.kraus k * X * (C.channel.kraus k)ᴴ) i j).im = 0 :=
    fun k => real_mul (real_mul (C.real_kraus k) hX)
      (real_conjTranspose (C.real_kraus k)) i j
  simp [h]

def act {A B : FiniteSystem} (C : Process A B) (ρ : State A) : State B :=
  ⟨C.channel.state ρ.1, operator_real C ρ.2⟩

def identity (A : FiniteSystem) : Process A A where
  environment := FiniteSystem.of Unit
  channel := RectangularChannel.identity A
  real_kraus _ i j := by
    classical
    change ((1 : Operator A) i j).im = 0
    simp only [Matrix.one_apply]
    split_ifs <;> simp

def compose {A B C : FiniteSystem} (D : Process B C) (E : Process A B) : Process A C where
  environment := D.environment.product E.environment
  channel := D.channel.comp E.channel
  real_kraus k := real_mul (D.real_kraus k.1) (E.real_kraus k.2)

def discardProcess (A B : FiniteSystem) : Process (A.product B) A where
  environment := B
  channel := RectangularChannel.discardRight A B
  real_kraus b i j := by
    classical
    simp only [RectangularChannel.discardRight, RectangularChannel.discardRightKraus]
    split_ifs <;> simp

end RealModel

/-- Full real PSD trace-one states and effects inside the complex matrix encoding. -/
def realModel : Presentation.{1} where
  State := RealModel.State
  Effect := RealModel.Effect
  probability E ρ := E.1.probability ρ.1
  mix := RealModel.mix
  productState := RealModel.product
  productEffect := RealModel.productEffect
  Process := RealModel.Process
  act := RealModel.act
  identity := RealModel.identity
  compose := RealModel.compose
  discardProcess := RealModel.discardProcess

theorem real_laws : Laws realModel where
  probability_bounds E ρ := ⟨E.1.probability_nonneg ρ.1, E.1.probability_le_one ρ.1⟩
  probability_mix E t ht0 ht1 ρ σ := QuantumPurification.probability_mix E.1 t ht0 ht1 ρ.1 σ.1
  product_probability E F ρ σ := QuantumModel.product_probability E.1 F.1 ρ.1 σ.1
  discard_product ρ σ := Subtype.ext (QuantumPurification.discard_product ρ.1 σ.1)
  act_mix C t ht0 ht1 ρ σ := Subtype.ext (QuantumPurification.state_mix C.channel t ht0 ht1 ρ.1 σ.1)
  identity_act ρ := Subtype.ext (RectangularChannel.identity_state ρ.1)
  compose_act D E ρ := Subtype.ext (RectangularChannel.comp_state D.channel E.channel ρ.1)

/-- The existing real counterexample violates local tomography in the common
interface. This theorem makes no claim that real quantum purification fails. -/
theorem real_not_localTomography : ¬ LocalTomography realModel := by
  intro h
  let A := FiniteSystem.of (Fin 2)
  let ρ : RealModel.State (A.product A) :=
    ⟨RealLocalTomography.rhoPlus, RealLocalTomography.rhoPlus_isReal⟩
  let σ : RealModel.State (A.product A) :=
    ⟨RealLocalTomography.rhoMinus, RealLocalTomography.rhoMinus_isReal⟩
  have heq := h A A ρ σ (fun E F =>
    RealLocalTomography.all_real_product_probabilities_equal E.1 F.1 E.2 F.2)
  exact RealLocalTomography.rhoPlus_ne_rhoMinus (congrArg Subtype.val heq)

end
end UEOTQM.OperationalSystems
