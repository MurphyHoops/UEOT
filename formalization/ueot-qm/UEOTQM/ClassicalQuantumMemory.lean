import UEOTQM.RectangularChannels
import UEOTQM.Adaptive
import UEOTQM.RecordProbability

/-!
# Actual classical records with quantum memory

A record is an orthogonal output label carried by a rectangular Kraus channel.
All joint blocks, marginals, event effects and error bounds refer to the actual
matrices. No posterior is assigned at a zero-probability branch. The protocol
extension uses the existing complete finite adaptive tree and its actual leaves.
-/

namespace UEOTQM.ClassicalQuantumMemory

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

variable {ι ο O κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype O] [DecidableEq O] [Fintype κ]

/-- Embed a genuine Kraus output into one orthogonal classical-label block. -/
def taggedKraus (o : O) (K : Matrix ο ι ℂ) : Matrix (O × ο) ι ℂ :=
  fun p i => if p.1 = o then K p.2 i else 0

theorem taggedKraus_gram (o : O) (K : Matrix ο ι ℂ) :
    (taggedKraus o K)ᴴ * taggedKraus o K = Kᴴ * K := by
  classical
  ext i j
  simp [taggedKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]

theorem taggedKraus_conjugation (o p q : O) (K : Matrix ο ι ℂ)
    (X : Operator ι) (i j : ο) :
    (taggedKraus q K * X * (taggedKraus q K)ᴴ) (o, i) (p, j) =
      if o = q then if p = q then (K * X * Kᴴ) i j else 0 else 0 := by
  classical
  by_cases ho : o = q <;> by_cases hp : p = q <;>
    simp [taggedKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, ho, hp]

/-- The full complex block-diagonal matrix, before any positivity restriction. -/
def block (B : O → Operator ι) : Operator (O × ι) :=
  fun p q => if p.1 = q.1 then B p.1 p.2 q.2 else 0

@[simp] theorem block_apply_same (B : O → Operator ι) (o : O) (i j : ι) :
    block B (o, i) (o, j) = B o i j := by simp [block]

@[simp] theorem block_apply_ne (B : O → Operator ι) {o p : O} (h : o ≠ p)
    (i j : ι) : block B (o, i) (p, j) = 0 := by simp [block, h]

theorem trace_block (B : O → Operator ι) : (block B).trace = ∑ o, (B o).trace := by
  simp [Matrix.trace, block, Fintype.sum_prod_type]

/-- The complete instrument becomes one rectangular channel whose output keeps
both the classical outcome and the quantum memory. -/
def channel (I : Instrument ι O κ) : RectangularChannel ι (O × ι) (O × κ) where
  kraus q := taggedKraus q.1 (I.kraus q.1 q.2)
  complete := by
    simp only [taggedKraus_gram, Fintype.sum_prod_type]
    exact I.complete

/-- Every complex matrix entry is identified; this is stronger than agreement
of branch traces or agreement on a finite collection of density inputs. -/
theorem channel_operator_apply (I : Instrument ι O κ) (X : Operator ι)
    (o p : O) (i j : ι) :
    (channel I).operator X (o, i) (p, j) =
      if o = p then I.branch o X i j else 0 := by
  classical
  simp only [RectangularChannel.operator, channel, Fintype.sum_prod_type,
    Matrix.sum_apply, taggedKraus_conjugation]
  rw [Finset.sum_eq_single o]
  · by_cases hop : o = p
    · subst p
      simp [Instrument.branch, krausMap, Matrix.sum_apply]
    · simp [hop, Ne.symm hop]
  · intro q _ hqo
    simp [Ne.symm hqo]
  · simp

/-- On every complex joint input, the actual identity amplification retains
exactly the original branch block, including off-diagonal auxiliary entries. -/
theorem channel_amplify_operator_apply {ν : Type*} [Fintype ν] [DecidableEq ν]
    (I : Instrument ι O κ) (X : Operator (ι × ν))
    (o p : O) (i j : ι) (a b : ν) :
    ((channel I).amplify ν).operator X ((o, i), a) ((p, j), b) =
      if o = p then I.branch o (fun x y => X (x, a) (y, b)) i j else 0 := by
  rw [RectangularChannel.amplify_operator_apply]
  exact channel_operator_apply I (Matrix.of fun x y => X (x, a) (y, b)) o p i j

theorem channel_operator_eq_block (I : Instrument ι O κ) (X : Operator ι) :
    (channel I).operator X = block (fun o => I.branch o X) := by
  ext ⟨o, i⟩ ⟨p, j⟩
  exact channel_operator_apply I X o p i j

/-- The normalized joint classical-quantum output is derived from completeness. -/
def state (I : Instrument ι O κ) (ρ : Density ι) : Density (O × ι) :=
  (channel I).state ρ

@[simp] theorem state_matrix (I : Instrument ι O κ) (ρ : Density ι) :
    (state I ρ).matrix = block (fun o => I.branch o ρ.matrix) :=
  channel_operator_eq_block I ρ.matrix

/-- Forgetting the label is the actual partial trace and gives the old channel. -/
theorem discard_record_operator (I : Instrument ι O κ) (X : Operator ι) :
    (RectangularChannel.discardLeft ι O).operator ((channel I).operator X) =
      I.channel X := by
  ext i j
  rw [RectangularChannel.discardLeft_operator_apply]
  simp [channel_operator_apply, Instrument.channel, Matrix.sum_apply]

theorem discard_record_state (I : Instrument ι O κ) (ρ : Density ι) :
    (RectangularChannel.discardLeft ι O).state (state I ρ) = I.channelState ρ := by
  apply Density.ext
  exact discard_record_operator I ρ.matrix

/-- Forgetting quantum memory gives the actual diagonal classical density. -/
theorem discard_memory_operator (I : Instrument ι O κ) (X : Operator ι) :
    (RectangularChannel.discardRight O ι).operator ((channel I).operator X) =
      Matrix.diagonal (fun o => (I.branch o X).trace) := by
  ext o p
  rw [RectangularChannel.discardRight_operator_apply]
  by_cases hop : o = p
  · subst p
    simp [channel_operator_apply, Matrix.trace]
  · simp [channel_operator_apply, hop, Matrix.diagonal_apply]

/-- At a density input the classical marginal consists of the original real
probabilities embedded in the complex diagonal matrix. -/
theorem discard_memory_state_matrix (I : Instrument ι O κ) (ρ : Density ι) :
    ((RectangularChannel.discardRight O ι).state (state I ρ)).matrix =
      Matrix.diagonal (fun o => (I.probability ρ o : ℂ)) := by
  change (RectangularChannel.discardRight O ι).operator ((channel I).operator ρ.matrix) = _
  rw [discard_memory_operator]
  congr 1
  funext o
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using
      trace_im_eq_zero (I.branch_posSemidef o ρ.positive)

/-- The mass of each diagonal joint block is the original outcome probability. -/
theorem state_block_mass (I : Instrument ι O κ) (ρ : Density ι) (o : O) :
    mass (fun i j => (state I ρ).matrix (o, i) (o, j)) = I.probability ρ o := by
  simp [state_matrix, Instrument.probability]

theorem positive_block_posterior (I : Instrument ι O κ) (ρ : Density ι) (o : O)
    (hp : 0 < I.probability ρ o) :
    (I.posterior ρ o hp).matrix = (I.probability ρ o)⁻¹ •
      (fun i j => (state I ρ).matrix (o, i) (o, j)) := by
  have hblock : (fun i j => (state I ρ).matrix (o, i) (o, j)) = I.branch o ρ.matrix := by
    ext i j
    simp [state_matrix]
  rw [hblock, Instrument.posterior_matrix]
  ext i j
  rfl

/-- Zero probability means a zero joint block; there is no forced posterior. -/
theorem zero_probability_iff_zero_block (I : Instrument ι O κ) (ρ : Density ι) (o : O) :
    I.probability ρ o = 0 ↔ (fun i j => (state I ρ).matrix (o, i) (o, j)) = 0 := by
  have hblock : (fun i j => (state I ρ).matrix (o, i) (o, j)) = I.branch o ρ.matrix := by
    ext i j
    simp [state_matrix]
  rw [hblock]
  exact I.zero_probability_iff_zero_branch ρ o

/-- A real classical event is represented by its block-diagonal quantum effect. -/
def eventEffect (ι : Type*) [Fintype ι] [DecidableEq ι] (s : Finset O) :
    Effect (O × ι) where
  matrix := Matrix.diagonal (fun p => if p.1 ∈ s then (1 : ℂ) else 0)
  positive := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro p
    split_ifs <;> norm_num
  complement_positive := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro p
    split_ifs <;> norm_num

@[simp] theorem eventEffect_matrix (s : Finset O) :
    (eventEffect ι s).matrix = Matrix.diagonal
      (fun p : O × ι => if p.1 ∈ s then (1 : ℂ) else 0) := rfl

theorem eventEffect_pairing_block (s : Finset O) (B : O → Operator ι) :
    pairing (eventEffect ι s).matrix (block B) = ∑ o ∈ s, mass (B o) := by
  classical
  simp [eventEffect, pairing, mass, Matrix.trace, Matrix.diagonal_mul,
    block, Fintype.sum_prod_type]

def weights (I : Instrument ι O κ) (ρ : Density ι) : Mixture.Weights O where
  weight := I.probability ρ
  nonneg := I.probability_nonneg ρ
  sum_one := I.sum_probability ρ

@[simp] theorem weights_weight (I : Instrument ι O κ) (ρ : Density ι) (o : O) :
    (weights I ρ).weight o = I.probability ρ o := rfl

theorem event_probability (I : Instrument ι O κ) (ρ : Density ι) (s : Finset O) :
    (eventEffect ι s).probability (state I ρ) =
      RecordProbability.eventProbability (weights I ρ) s := by
  change pairing (eventEffect ι s).matrix (state I ρ).matrix = _
  rw [state_matrix, eventEffect_pairing_block]
  rfl

/-- Sharp record-law TV follows from all actual block-diagonal event effects. -/
theorem record_tv_le_joint_distance {κ' : Type*} [Fintype κ']
    (I : Instrument ι O κ) (J : Instrument ι O κ') (ρ σ : Density ι) :
    Mixture.tv (weights I ρ) (weights J σ) ≤ effectDistance (state I ρ) (state J σ) := by
  apply (RecordProbability.tv_le_iff_events _ _ _).mpr
  intro s
  rw [← event_probability, ← event_probability]
  exact (eventEffect ι s).probability_sub_le_effectDistance _ _

/-- The tagged defect is the actual supremum over every input density. -/
def defect {κ' : Type*} [Fintype κ'] (I : Instrument ι O κ)
    (J : Instrument ι O κ') : ℝ := (channel I).defect (channel J)

theorem perturbation_bound {κ' : Type*} [Fintype κ']
    (I : Instrument ι O κ) (J : Instrument ι O κ') (ρ σ : Density ι) :
    effectDistance (state I ρ) (state J σ) ≤ effectDistance ρ σ + defect I J :=
  (channel I).perturbation_bound (channel J) ρ σ

theorem record_tv_perturbation_bound {κ' : Type*} [Fintype κ']
    (I : Instrument ι O κ) (J : Instrument ι O κ') (ρ σ : Density ι) :
    Mixture.tv (weights I ρ) (weights J σ) ≤ effectDistance ρ σ + defect I J :=
  (record_tv_le_joint_distance I J ρ σ).trans (perturbation_bound I J ρ σ)


namespace ProtocolMemory

open Adaptive

variable {A : Type*}

universe uA uO uK

/-- Pin the harmless universe of the stopping leaf; the leaves are exactly those
of the existing protocol, with no new label representation. -/
abbrev Leaf {A : Type uA} {O : Type uO} (π : Protocol A O) : Type uO :=
  Protocol.Leaf.{uA, uO, 0} π

attribute [local instance] Classical.propDecidable

/-- The Kraus choices along one actual leaf of the same complete finite tree.
Leaves may have different depths; no fixed-depth surrogate is introduced. -/
def KrausPath (κ : Type uK) : (π : Protocol A O) → Leaf π → Type uK
  | .stop, _ => PUnit
  | .node _ next, l => κ × KrausPath κ (next l.1) l.2

instance krausPathFintype (π : Protocol A O) :
    ∀ l : Leaf π, Fintype (KrausPath κ π l) := by
  induction π with
  | stop =>
    intro l
    exact inferInstanceAs (Fintype PUnit)
  | node a next ih =>
    rintro ⟨o, l⟩
    letI := ih o l
    exact inferInstanceAs (Fintype (κ × KrausPath κ (next o) l))

/-- Chronological operator multiplication: the later operator is on the left. -/
def pathKraus (I : A → Instrument ι O κ) :
    (π : Protocol A O) → (l : Leaf π) → KrausPath κ π l → Operator ι
  | .stop, _, _ => 1
  | .node a next, l, q => pathKraus I (next l.1) l.2 q.2 * (I a).kraus l.1 q.1

/-- Complete finite adaptive branching gives actual input-space completeness. -/
theorem path_complete (I : A → Instrument ι O κ) (π : Protocol A O) :
    (∑ l : Leaf π, ∑ q : KrausPath κ π l,
      (pathKraus I π l q)ᴴ * pathKraus I π l q) = 1 := by
  induction π with
  | stop =>
    letI : Unique (Leaf (.stop : Protocol A O)) := inferInstanceAs (Unique PUnit)
    letI : ∀ l : Leaf (.stop : Protocol A O), Unique (KrausPath κ .stop l) :=
      fun _ => inferInstanceAs (Unique PUnit)
    simp only [Fintype.sum_unique, pathKraus, Matrix.conjTranspose_one,
      Matrix.one_mul]
  | node a next ih =>
    change (∑ l : (o : O) × Leaf (next o),
      ∑ q : κ × KrausPath κ (next l.1) l.2,
        (pathKraus I (next l.1) l.2 q.2 * (I a).kraus l.1 q.1)ᴴ *
          (pathKraus I (next l.1) l.2 q.2 * (I a).kraus l.1 q.1)) = 1
    rw [Fintype.sum_sigma]
    simp only [Fintype.sum_prod_type, Matrix.conjTranspose_mul]
    calc
      (∑ o, ∑ l : Leaf (next o), ∑ k, ∑ q : KrausPath κ (next o) l,
          ((I a).kraus o k)ᴴ * (pathKraus I (next o) l q)ᴴ *
            (pathKraus I (next o) l q * (I a).kraus o k)) =
          ∑ o, ∑ k, ((I a).kraus o k)ᴴ *
            (∑ l : Leaf (next o), ∑ q : KrausPath κ (next o) l,
              (pathKraus I (next o) l q)ᴴ * pathKraus I (next o) l q) *
            (I a).kraus o k := by
        apply Finset.sum_congr rfl
        intro o _
        rw [Finset.sum_comm]
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = 1 := by
        simp only [ih, Matrix.mul_one]
        exact (I a).complete

/-- Every leaf block is exactly the previously defined unnormalized record
operator, for every complex input matrix. -/
theorem path_branch_eq_recordOperator (I : A → Instrument ι O κ)
    (π : Protocol A O) (X : Operator ι) (l : Leaf π) :
    krausMap (pathKraus I π l) X = recordOperator I (π.word l) X := by
  induction π generalizing X with
  | stop =>
    letI : Unique (KrausPath κ .stop l) := inferInstanceAs (Unique PUnit)
    simp only [krausMap, Fintype.sum_unique, pathKraus, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one, recordOperator, Protocol.word]
  | node a next ih =>
    rcases l with ⟨o, l⟩
    change (∑ q : κ × KrausPath κ (next o) l,
      (pathKraus I (next o) l q.2 * (I a).kraus o q.1) * X *
        (pathKraus I (next o) l q.2 * (I a).kraus o q.1)ᴴ) =
      recordOperator I ((next o).word l) ((I a).branch o X)
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc
      (∑ q : KrausPath κ (next o) l, ∑ k,
        (pathKraus I (next o) l q * (I a).kraus o k) * X *
          (pathKraus I (next o) l q * (I a).kraus o k)ᴴ) =
          krausMap (pathKraus I (next o) l) ((I a).branch o X) := by
        simp only [krausMap, Instrument.branch, Matrix.conjTranspose_mul,
          Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = _ := ih o ((I a).branch o X) l

/-- The actual rectangular output retains the complete leaf label and memory. -/
def channel (I : A → Instrument ι O κ) (π : Protocol A O) :
    RectangularChannel ι (Leaf π × ι) ((l : Leaf π) × KrausPath κ π l) where
  kraus q := taggedKraus q.1 (pathKraus I π q.1 q.2)
  complete := by
    simp only [taggedKraus_gram, Fintype.sum_sigma]
    exact path_complete I π

theorem channel_operator_apply (I : A → Instrument ι O κ) (π : Protocol A O)
    (X : Operator ι) (l m : Leaf π) (i j : ι) :
    (channel I π).operator X (l, i) (m, j) =
      if l = m then recordOperator I (π.word l) X i j else 0 := by
  classical
  simp only [RectangularChannel.operator, channel, Fintype.sum_sigma,
    Matrix.sum_apply, taggedKraus_conjugation]
  rw [Finset.sum_eq_single l]
  · by_cases hlm : l = m
    · subst m
      simpa [krausMap, Matrix.sum_apply] using
        congrArg (fun M : Operator ι => M i j) (path_branch_eq_recordOperator I π X l)
    · simp [hlm, Ne.symm hlm]
  · intro q _ hql
    simp [Ne.symm hql]
  · simp

/-- Arbitrary auxiliary coherences are passed through the same actual leaf
record operator; this is the explicit finite-ancilla block identity. -/
theorem channel_amplify_operator_apply {ν : Type*} [Fintype ν] [DecidableEq ν]
    (I : A → Instrument ι O κ) (π : Protocol A O) (X : Operator (ι × ν))
    (l m : Leaf π) (i j : ι) (a b : ν) :
    ((channel I π).amplify ν).operator X ((l, i), a) ((m, j), b) =
      if l = m then recordOperator I (π.word l)
        (fun x y => X (x, a) (y, b)) i j else 0 := by
  rw [RectangularChannel.amplify_operator_apply]
  exact channel_operator_apply I π (Matrix.of fun x y => X (x, a) (y, b)) l m i j

theorem channel_operator_eq_block (I : A → Instrument ι O κ) (π : Protocol A O)
    (X : Operator ι) : (channel I π).operator X =
      block (fun l => recordOperator I (π.word l) X) := by
  ext ⟨l, i⟩ ⟨m, j⟩
  exact channel_operator_apply I π X l m i j

def state (I : A → Instrument ι O κ) (π : Protocol A O) (ρ : Density ι) :
    Density (Leaf π × ι) := (channel I π).state ρ

@[simp] theorem state_matrix (I : A → Instrument ι O κ)
    (π : Protocol A O) (ρ : Density ι) :
    (state I π ρ).matrix = block (fun l => recordOperator I (π.word l) ρ.matrix) :=
  channel_operator_eq_block I π ρ.matrix

/-- Erasing the final leaf label sums the actual unnormalized leaf operators. -/
theorem discard_record_operator (I : A → Instrument ι O κ) (π : Protocol A O)
    (X : Operator ι) :
    (RectangularChannel.discardLeft ι (Leaf π)).operator ((channel I π).operator X) =
      ∑ l : Leaf π, recordOperator I (π.word l) X := by
  ext i j
  rw [RectangularChannel.discardLeft_operator_apply]
  simp [channel_operator_apply, Matrix.sum_apply]

/-- The other marginal is the diagonal matrix of the full complex leaf traces. -/
theorem discard_memory_operator (I : A → Instrument ι O κ) (π : Protocol A O)
    (X : Operator ι) :
    (RectangularChannel.discardRight (Leaf π) ι).operator ((channel I π).operator X) =
      Matrix.diagonal (fun l => (recordOperator I (π.word l) X).trace) := by
  ext l m
  rw [RectangularChannel.discardRight_operator_apply]
  by_cases hlm : l = m
  · subst m
    simp [channel_operator_apply, Matrix.trace]
  · simp [channel_operator_apply, hlm, Matrix.diagonal_apply]

/-- The actual record marginal is the existing complete leaf law. -/
theorem discard_memory_state_matrix (I : A → Instrument ι O κ)
    (π : Protocol A O) (ρ : Density ι) :
    ((RectangularChannel.discardRight (Leaf π) ι).state (state I π ρ)).matrix =
      Matrix.diagonal (fun l => (Adaptive.leafProbability I π ρ l : ℂ)) := by
  change (RectangularChannel.discardRight (Leaf π) ι).operator
    ((channel I π).operator ρ.matrix) = _
  rw [discard_memory_operator]
  congr 1
  funext l
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using
      trace_im_eq_zero (recordOperator_posSemidef I (π.word l) ρ.positive)

theorem state_block_mass (I : A → Instrument ι O κ) (π : Protocol A O)
    (ρ : Density ι) (l : Leaf π) :
    mass (fun i j => (state I π ρ).matrix (l, i) (l, j)) =
      Adaptive.leafProbability I π ρ l := by
  simp [state_matrix, Adaptive.leafProbability, Adaptive.leafWeight]

/-- The original zero-leaf probability is exactly a zero joint memory block. -/
theorem zero_probability_iff_zero_block (I : A → Instrument ι O κ)
    (π : Protocol A O) (ρ : Density ι) (l : Leaf π) :
    Adaptive.leafProbability I π ρ l = 0 ↔
      (fun i j => (state I π ρ).matrix (l, i) (l, j)) = 0 := by
  have hblock : (fun i j => (state I π ρ).matrix (l, i) (l, j)) =
      recordOperator I (π.word l) ρ.matrix := by
    ext i j
    simp [state_matrix]
  rw [hblock]
  exact mass_eq_zero_iff (recordOperator_posSemidef I (π.word l) ρ.positive)

def weights (I : A → Instrument ι O κ) (π : Protocol A O) (ρ : Density ι) :
    Mixture.Weights (Leaf π) where
  weight := Adaptive.leafProbability I π ρ
  nonneg := Adaptive.leafProbability_nonneg I π ρ
  sum_one := Adaptive.sum_leafProbability I π ρ

@[simp] theorem weights_weight (I : A → Instrument ι O κ)
    (π : Protocol A O) (ρ : Density ι) (l : Leaf π) :
    (weights I π ρ).weight l = Adaptive.leafProbability I π ρ l := rfl

theorem event_probability (I : A → Instrument ι O κ) (π : Protocol A O)
    (ρ : Density ι) (s : Finset (Leaf π)) :
    (eventEffect ι s).probability (state I π ρ) =
      RecordProbability.eventProbability (weights I π ρ) s := by
  change pairing (eventEffect ι s).matrix (state I π ρ).matrix = _
  rw [state_matrix, eventEffect_pairing_block]
  rfl

theorem record_tv_le_joint_distance {κ' : Type*} [Fintype κ']
    (I : A → Instrument ι O κ) (J : A → Instrument ι O κ')
    (π : Protocol A O) (ρ σ : Density ι) :
    Mixture.tv (weights I π ρ) (weights J π σ) ≤
      effectDistance (state I π ρ) (state J π σ) := by
  apply (RecordProbability.tv_le_iff_events _ _ _).mpr
  intro s
  rw [← event_probability, ← event_probability]
  exact (eventEffect ι s).probability_sub_le_effectDistance _ _

/-- This is a whole-protocol actual supremum, not a sum of local step budgets.
Fixed-depth error accumulation is a distinct further theorem. -/
def defect {κ' : Type*} [Fintype κ'] (I : A → Instrument ι O κ)
    (J : A → Instrument ι O κ') (π : Protocol A O) : ℝ :=
  (channel I π).defect (channel J π)

theorem perturbation_bound {κ' : Type*} [Fintype κ']
    (I : A → Instrument ι O κ) (J : A → Instrument ι O κ')
    (π : Protocol A O) (ρ σ : Density ι) :
    effectDistance (state I π ρ) (state J π σ) ≤
      effectDistance ρ σ + defect I J π :=
  (channel I π).perturbation_bound (channel J π) ρ σ

theorem record_tv_perturbation_bound {κ' : Type*} [Fintype κ']
    (I : A → Instrument ι O κ) (J : A → Instrument ι O κ')
    (π : Protocol A O) (ρ σ : Density ι) :
    Mixture.tv (weights I π ρ) (weights J π σ) ≤
      effectDistance ρ σ + defect I J π :=
  (record_tv_le_joint_distance I J π ρ σ).trans (perturbation_bound I J π ρ σ)

end ProtocolMemory

end

end UEOTQM.ClassicalQuantumMemory
