import UEOT.V3.FiniteStablePartitionQuotientNormalization

/-!
# P-ALG-01 — finite-horizon controlled output laws

For a controlled-stable finite partition refining the initial output/reward
partition, every finite-horizon output functional is constant on equivalence
classes.  In particular, for every finite action sequence and every output
word of the matching length, the exact output-word probability descends to the
quotient.
-/

namespace UEOT.V3.FiniteStablePartition

open Finset

universe uX uA uR uO

variable {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
variable [Fintype X] [Fintype A]

/-- Explicit finite equivalence class represented by `z`, local to the
finite-horizon quotient argument. -/
noncomputable def quotientBlockFinset (S : Setoid X) (z : X) : Finset X := by
  classical
  exact Finset.univ.filter (fun y => S.r y z)

@[simp] theorem mem_quotientBlockFinset (S : Setoid X) (z y : X) :
    y ∈ quotientBlockFinset S z ↔ S.r y z := by
  classical
  simp [quotientBlockFinset]

/-- Source block mass is the ordinary sum over the represented quotient class. -/
theorem blockMass_eq_sum_quotientBlockFinset
    (M : Model X A R O) (S : Setoid X) (a : A) (x z : X) :
    blockMass M S a x z =
      ∑ y ∈ quotientBlockFinset S z, M.transition a x y := by
  classical
  unfold blockMass quotientBlockFinset
  rw [Finset.sum_filter]

/-- Every quotient-class block has a representative.  Membership of the chosen
representative is used only internally, so no `DecidableEq X` artifact leaks
into this theorem statement. -/
theorem exists_rep_of_mem_quotientClassBlocks
    (S : Setoid X) {t : Finset X} (ht : t ∈ quotientClassBlocks S) :
    ∃ z : X, quotientBlockFinset S z = t := by
  classical
  have ht' : t ∈ (Finpartition.ofSetoid S).parts := by
    simpa [quotientClassBlocks] using ht
  obtain ⟨z, hz⟩ := (Finpartition.ofSetoid S).nonempty_of_mem_parts ht'
  have hpart : (Finpartition.ofSetoid S).part z = t :=
    (Finpartition.ofSetoid S).part_eq_of_mem ht' hz
  refine ⟨z, ?_⟩
  rw [← hpart]
  ext y
  rw [mem_quotientBlockFinset, Finpartition.mem_part_ofSetoid_iff_rel]
  exact ⟨fun hyz => S.symm hyz, fun hzy => S.symm hzy⟩

/-- Stable block masses imply equality of one-step expectations for every
function constant on quotient classes. -/
theorem stable_weighted_sum_eq
    (M : Model X A R O) (S : Setoid X) (hStable : Stable M S)
    (a : A) (f : X → ℝ)
    (hf : ∀ ⦃u v : X⦄, S.r u v → f u = f v)
    {x x' : X} (hxx : S.r x x') :
    (∑ y : X, M.transition a x y * f y) =
      ∑ y : X, M.transition a x' y * f y := by
  classical
  have hx_decomp :
      (∑ y : X, M.transition a x y * f y) =
        ∑ t ∈ quotientClassBlocks S,
          ∑ y ∈ t, M.transition a x y * f y :=
    (sum_over_quotientClassBlocks S
      (fun y => M.transition a x y * f y)).symm
  have hx'_decomp :
      (∑ y : X, M.transition a x' y * f y) =
        ∑ t ∈ quotientClassBlocks S,
          ∑ y ∈ t, M.transition a x' y * f y :=
    (sum_over_quotientClassBlocks S
      (fun y => M.transition a x' y * f y)).symm
  rw [hx_decomp, hx'_decomp]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨z, hblock⟩ := exists_rep_of_mem_quotientClassBlocks S ht
  have hxmass :
      (∑ y ∈ t, M.transition a x y) = blockMass M S a x z := by
    rw [← hblock]
    exact (blockMass_eq_sum_quotientBlockFinset M S a x z).symm
  have hx'mass :
      (∑ y ∈ t, M.transition a x' y) = blockMass M S a x' z := by
    rw [← hblock]
    exact (blockMass_eq_sum_quotientBlockFinset M S a x' z).symm
  calc
    (∑ y ∈ t, M.transition a x y * f y)
        = ∑ y ∈ t, M.transition a x y * f z := by
            apply Finset.sum_congr rfl
            intro y hy
            have hyblock : y ∈ quotientBlockFinset S z := by
              rw [hblock]
              exact hy
            have hyz : S.r y z := (mem_quotientBlockFinset S z y).1 hyblock
            rw [hf hyz]
    _ = (∑ y ∈ t, M.transition a x y) * f z := by
          rw [Finset.sum_mul]
    _ = blockMass M S a x z * f z := by rw [hxmass]
    _ = blockMass M S a x' z * f z := by rw [hStable hxx a z]
    _ = (∑ y ∈ t, M.transition a x' y) * f z := by rw [hx'mass]
    _ = ∑ y ∈ t, M.transition a x' y * f z := by
          rw [Finset.sum_mul]
    _ = ∑ y ∈ t, M.transition a x' y * f y := by
          apply Finset.sum_congr rfl
          intro y hy
          have hyblock : y ∈ quotientBlockFinset S z := by
            rw [hblock]
            exact hy
          have hyz : S.r y z := (mem_quotientBlockFinset S z y).1 hyblock
          rw [hf hyz]

/-- Backward finite-horizon output functional.  With a test `g_k : O → ℝ`
at each time, this is the exact controlled expectation of the product of those
tests along the output trajectory.  Extra/missing tests are handled by the
base clauses; the source-facing output-word law below enforces matching length. -/
noncomputable def finiteHorizonOutputFunctional
    (M : Model X A R O) : List A → List (O → ℝ) → X → ℝ
  | [], [] => fun _ => 1
  | [], g :: _ => fun x => g (M.output x)
  | _ :: _, [] => fun _ => 1
  | a :: actions, g :: tests => fun x =>
      g (M.output x) *
        ∑ y : X, M.transition a x y *
          finiteHorizonOutputFunctional M actions tests y

/-- Every finite-horizon output functional is constant on a stable class that
refines the initial output/reward partition. -/
theorem finiteHorizonOutputFunctional_eq_of_rel
    (M : Model X A R O) (S : Setoid X)
    (hSinit : Refines S (initialSetoid M)) (hStable : Stable M S) :
    ∀ (actions : List A) (tests : List (O → ℝ)) {x x' : X},
      S.r x x' →
      finiteHorizonOutputFunctional M actions tests x =
        finiteHorizonOutputFunctional M actions tests x' := by
  intro actions
  induction actions with
  | nil =>
      intro tests x x' hxx
      cases tests with
      | nil => rfl
      | cons g gs =>
          simp only [finiteHorizonOutputFunctional]
          rw [(hSinit hxx).1]
  | cons a actions ih =>
      intro tests x x' hxx
      cases tests with
      | nil => rfl
      | cons g gs =>
          simp only [finiteHorizonOutputFunctional]
          have hout : M.output x = M.output x' := (hSinit hxx).1
          have hsum := stable_weighted_sum_eq M S hStable a
            (fun y => finiteHorizonOutputFunctional M actions gs y)
            (fun {_ _} huv => ih gs huv) hxx
          rw [hout, hsum]

/-- Point indicator used to extract exact output-word cylinder probabilities. -/
noncomputable def outputPointIndicator (o : O) : O → ℝ := by
  classical
  exact fun u => if u = o then 1 else 0

/-- Exact finite-horizon probability of an output word under a fixed action
sequence, represented as the product-indicator expectation.  Length mismatch
is assigned probability zero. -/
noncomputable def finiteHorizonOutputWordMass
    (M : Model X A R O) (actions : List A) (word : List O) (x : X) : ℝ :=
  if word.length = actions.length + 1 then
    finiteHorizonOutputFunctional M actions
      (word.map outputPointIndicator) x
  else 0

/-- All controlled finite-horizon output-word probabilities are identical for
states in the same stable quotient class. -/
theorem finiteHorizonOutputWordMass_eq_of_rel
    (M : Model X A R O) (S : Setoid X)
    (hSinit : Refines S (initialSetoid M)) (hStable : Stable M S)
    (actions : List A) (word : List O) {x x' : X} (hxx : S.r x x') :
    finiteHorizonOutputWordMass M actions word x =
      finiteHorizonOutputWordMass M actions word x' := by
  classical
  unfold finiteHorizonOutputWordMass
  split_ifs
  · exact finiteHorizonOutputFunctional_eq_of_rel M S hSinit hStable
      actions (word.map outputPointIndicator) hxx
  · rfl

/-- Therefore every finite-horizon output-word law descends canonically to the
stable quotient. -/
noncomputable def quotientFiniteHorizonOutputWordMass
    (M : Model X A R O) (S : Setoid X)
    (hSinit : Refines S (initialSetoid M)) (hStable : Stable M S)
    (actions : List A) (word : List O) : Quotient S → ℝ :=
  fun q => Quotient.liftOn q
    (finiteHorizonOutputWordMass M actions word)
    (by
      intro x x' hxx
      exact finiteHorizonOutputWordMass_eq_of_rel M S hSinit hStable
        actions word hxx)

@[simp] theorem quotientFiniteHorizonOutputWordMass_mk
    (M : Model X A R O) (S : Setoid X)
    (hSinit : Refines S (initialSetoid M)) (hStable : Stable M S)
    (actions : List A) (word : List O) (x : X) :
    quotientFiniteHorizonOutputWordMass M S hSinit hStable actions word ⟦x⟧ =
      finiteHorizonOutputWordMass M actions word x := rfl

end UEOT.V3.FiniteStablePartition
