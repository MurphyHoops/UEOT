import UEOT
namespace UEOTCarrierFrontierIndependent
open UEOT
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open FiniteResponseCarrierFrontier
-- The engine really works without Fintype atoms; ambient Nat has no powerset enumeration.
example : enumerate ([{0,1},{1,2}] : List (Finset ℕ)) = {{1},{0,2}} := by decide
example : enumerate ([∅] : List (Finset ℕ))=∅ := by decide
example : enumerate ([] : List (Finset ℕ))={∅} := rfl
-- Equal actual observations with different targets are a real obstruction.
def blindObs (_ : Bool) (_ : Bool) : Bool := false
def identityTarget (x : Bool) := x
theorem blind_insufficient (S : Finset Bool) : ¬ Access.Sufficient blindObs identityTarget S := by
  intro h
  have he := h false true (fun _ _ => rfl)
  exact Bool.false_ne_true he

theorem blind_carriers : carrierList [false,true] blindObs identityTarget=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro S hS
  exact blind_insufficient S ((carrierList_iff_original [false,true]
    (fun v => by cases v <;> simp) blindObs identityTarget S).mp hS).1
-- Already-insufficient access has the EMPTY minimal cut; do not presume
-- full-state sufficiency or replace the original blocker conventions.
example : cutList [false,true] blindObs identityTarget=[∅] := by
  rw [cutList,blind_carriers]
  rfl
example : ¬ Access.Sufficient blindObs identityTarget (Finset.univ : Finset Bool) := by
  intro h
  have he := h false true (fun _ _ => rfl)
  exact Bool.false_ne_true he
open FiniteReplicaCarrierErasureSource
-- This actual complete table has all source rows, and every returned decoder
-- consumes exactly its realized access range.
example (m : ℕ) (S : Finset (Atom m)) (hS : S ∈ actualCarriers m) (x : Row m) :=
  returned_decoder m S hS x
example (m : ℕ) (D : Finset (Atom m)) := returned_cut_original m D
example (m : ℕ) (D : Finset (Atom m)) := physical_frame D
example (m : ℕ) (D : Finset (Atom m)) := actual_cut_family m D
example (m : ℕ) (x : Row m) := source_positive m x
example (C k : ℕ) := no_table_polynomial_output_bound C k
example : (actualCarriers 3).length=8 := by simpa using actual_output_length 3
example : (actualCuts 3).length=3 := actual_cut_length 3
example : (actualCarriers 0).length=1 ∧ actualCuts 0=[] := zero_dimension
#print axioms enumerate_mem_iff
#print axioms carriers_iff_original
#print axioms decode_returned
#print axioms cutList_iff_original
#print axioms physical_frame
#print axioms returned_cut_original
#print axioms no_table_polynomial_output_bound
end UEOTCarrierFrontierIndependent
