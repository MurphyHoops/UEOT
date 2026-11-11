import UEOTQM.QuantumActionCounterexamples

/-!
# A positive allowed-action witness linked to the original source instrument

The source success terms are Z/2 and X/2; its failure branch contains two
hidden I/2 Kraus terms.  The target uses the same visible success labels and
the fair Z/X instrument.  Two allowed deterministic-label unitary actions,
mixed with weights 1/2, reproduce that target on every operator.
-/

namespace UEOTQM.QuantumActionPauliWitness

open Matrix QuantumActionRealizability
open scoped BigOperators ComplexOrder

noncomputable section

def pauliZ : Operator Bool :=
  fun i j => if i = j then (if i then -1 else 1) else 0

def pauliX : Operator Bool :=
  fun i j => if i = j then 0 else 1

theorem pauliZ_gram : pauliZᴴ * pauliZ = 1 := by
  ext i j
  cases i <;> cases j <;>
    norm_num [pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_bool, Matrix.one_apply]

theorem pauliX_gram : pauliXᴴ * pauliX = 1 := by
  ext i j
  cases i <;> cases j <;>
    norm_num [pauliX, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_bool, Matrix.one_apply]

def labelUnitary (U : Operator Bool) (hU : Uᴴ * U = 1) (label : Bool) :
    Instrument Bool Bool Unit where
  kraus o _ := if o = label then U else 0
  complete := by cases label <;> simp [Fintype.sum_bool, hU]

@[simp] theorem labelUnitary_branch (U : Operator Bool) (hU : Uᴴ * U = 1)
    (label o : Bool) (X : Operator Bool) :
    (labelUnitary U hU label).branch o X =
      if o = label then U * X * Uᴴ else 0 := by
  by_cases h : o = label <;> simp [Instrument.branch, krausMap, labelUnitary, h]

def allowed (a : Bool) : Instrument Bool Bool Unit :=
  if a then labelUnitary pauliX pauliX_gram true
  else labelUnitary pauliZ pauliZ_gram false

def targetWeighted : WeightedInstrument Bool Bool Unit where
  weight _ _ := 1 / 2
  kraus o _ := if o then pauliX else pauliZ
  weight_nonneg _ _ := by norm_num
  complete := by
    norm_num [Fintype.sum_bool, pauliX_gram, pauliZ_gram, ← add_smul]

def target : Instrument Bool Bool Unit := targetWeighted.toInstrument

@[simp] theorem target_branch (o : Bool) (X : Operator Bool) :
    target.branch o X = (1 / 2 : ℝ) •
      ((if o then pauliX else pauliZ) * X * (if o then pauliX else pauliZ)ᴴ) := by
  simp [target, WeightedInstrument.toInstrument_branch, WeightedInstrument.branch,
    weightedKrausMap, targetWeighted]

/-- Actual positive certificate with common weights, valid on all inputs. -/
theorem fair_allowed_realizes_target (o : Bool) (X : Operator Bool) :
    (Mixture.instrument fairWeights allowed).branch o X = target.branch o X := by
  cases o <;>
    simp [Mixture.instrument_branch, fairWeights, allowed, Fintype.sum_bool]

/-- The same certificate expressed in the Choi real-module coordinates. -/
theorem target_choi_positive_certificate :
    (∑ a, fairWeights.weight a • instrumentChoiAfter (allowed a) LinearMap.id) =
      instrumentChoiAfter target LinearMap.id := by
  rw [← mixture_instrumentChoiAfter]
  exact (instrumentChoiAfter_eq_iff _ (branchLinear target) _).mpr
    (fun o X => fair_allowed_realizes_target o X)

/-- `none` is the single visible failure label; its two Kraus refinements stay
hidden.  Zero-weight padding gives every visible branch the same index type. -/
def sourceWeighted : WeightedInstrument Bool (Option Bool) Bool where
  weight o k := match o with
    | none => 1 / 4
    | some _ => if k then 0 else 1 / 4
  kraus o _ := match o with
    | none => 1
    | some false => pauliZ
    | some true => pauliX
  weight_nonneg o k := by
    cases o with
    | none => norm_num
    | some b => cases k <;> norm_num
  complete := by
    norm_num [Fintype.sum_option, Fintype.sum_bool, pauliX_gram, pauliZ_gram,
      ← add_smul]

def source : Instrument Bool (Option Bool) (Bool) := sourceWeighted.toInstrument

/-- Local same-source bridge: success branches have half the target weight.
Iterating three accepted steps therefore gives the original success mass 1/8. -/
theorem source_success_eq_half_target (o : Bool) (X : Operator Bool) :
    source.branch (some o) X = (1 / 2 : ℝ) • target.branch o X := by
  cases o <;>
    norm_num [source, WeightedInstrument.toInstrument_branch, WeightedInstrument.branch,
      weightedKrausMap, sourceWeighted, Fintype.sum_bool, target_branch, smul_smul]

theorem source_failure_branch (X : Operator Bool) :
    source.branch none X = (1 / 2 : ℝ) • X := by
  simp only [source, WeightedInstrument.toInstrument_branch, WeightedInstrument.branch,
    weightedKrausMap, sourceWeighted, Fintype.sum_bool, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]
  rw [← add_smul]
  norm_num

end

end UEOTQM.QuantumActionPauliWitness
