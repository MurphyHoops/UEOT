import UEOTQM.ExactCertificate

/-!
Generated exact numerical instance. Original labels and source bindings are
in the companion manifest. This source has no external verification oracle:
`checked` must be accepted by Lean's kernel before its consequences are used.
-/

namespace UEOTQM.Generated.Certificate_f15e85048ff2d0cde352ece7ee50d18e18f51f48ee95c7dc57b2db19ecd0ecc6

open UEOTQM
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev Hilbert := Fin 2
abbrev Action := Fin 1
abbrev Outcome := Fin 2
abbrev KrausIndex := Fin 1
abbrev Coordinate := Fin 2

def weights : Action → Outcome → KrausIndex → ℚ :=
  ![![![(1 : ℚ)], ![(1 : ℚ)]]]

def krausData : Action → Outcome → KrausIndex → Exact.OperatorData Hilbert :=
  ![![![⟨!![(1 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)], !![(0 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)]⟩], ![⟨!![(0 : ℚ), (0 : ℚ); (0 : ℚ), (1 : ℚ)], !![(0 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)]⟩]]]

def basisData : Coordinate → Exact.OperatorData Hilbert :=
  ![⟨!![(1 : ℚ), (0 : ℚ); (0 : ℚ), (1 : ℚ)], !![(0 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)]⟩, ⟨!![(1 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)], !![(0 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)]⟩]

def words : Coordinate → List (Action × Outcome) :=
  ![[], [((⟨0, by decide⟩ : Action), (⟨0, by decide⟩ : Outcome))]]

def coefficients : Action → Outcome → Coordinate → Coordinate → ℚ :=
  ![![![![(1 : ℚ), (1 : ℚ)], ![(0 : ℚ), (1 : ℚ)]], ![![(1 : ℚ), (-1 : ℚ)], ![(0 : ℚ), (0 : ℚ)]]]]

def data : ExactCertificate.Data 2 1 2 1 2 where
  weight := weights
  kraus := krausData
  basis := basisData
  word := words
  unitIndex := (⟨0, by decide⟩ : Coordinate)
  coeff := fun e => coefficients e.1 e.2

theorem rejected : ExactCertificate.check data = false := by decide +kernel

#print axioms rejected

end UEOTQM.Generated.Certificate_f15e85048ff2d0cde352ece7ee50d18e18f51f48ee95c7dc57b2db19ecd0ecc6
