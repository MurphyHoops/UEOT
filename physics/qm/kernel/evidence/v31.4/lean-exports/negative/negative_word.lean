import UEOTQM.ExactCertificate

/-!
Generated exact numerical instance. Original labels and source bindings are
in the companion manifest. This source has no external verification oracle:
`checked` must be accepted by Lean's kernel before its consequences are used.
-/

namespace UEOTQM.Generated.Certificate_6d0317ee7bb3888dc9b92431e5263f4f62802a6237dedeb2831a2a57201061f8

open UEOTQM
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev Hilbert := Fin 2
abbrev Action := Fin 2
abbrev Outcome := Fin 2
abbrev KrausIndex := Fin 1
abbrev Coordinate := Fin 3

def weights : Action → Outcome → KrausIndex → ℚ :=
  ![![![((1 : ℚ) / 2)], ![(0 : ℚ)]], ![![(1 : ℚ)], ![(1 : ℚ)]]]

def krausData : Action → Outcome → KrausIndex → Exact.OperatorData Hilbert :=
  ![![![⟨!![(1 : ℚ), (1 : ℚ); (1 : ℚ), (-1 : ℚ)], !![(0 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)]⟩], ![⟨!![(0 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)], !![(0 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)]⟩]], ![![⟨!![(1 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)], !![(0 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)]⟩], ![⟨!![(0 : ℚ), (0 : ℚ); (0 : ℚ), (1 : ℚ)], !![(0 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)]⟩]]]

def basisData : Coordinate → Exact.OperatorData Hilbert :=
  ![⟨!![(1 : ℚ), (0 : ℚ); (0 : ℚ), (1 : ℚ)], !![(0 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)]⟩, ⟨!![(1 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)], !![(0 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)]⟩, ⟨!![((1 : ℚ) / 2), ((1 : ℚ) / 2); ((1 : ℚ) / 2), ((1 : ℚ) / 2)], !![(0 : ℚ), (0 : ℚ); (0 : ℚ), (0 : ℚ)]⟩]

def words : Coordinate → List (Action × Outcome) :=
  ![[], [((⟨1, by decide⟩ : Action), (⟨0, by decide⟩ : Outcome))], [((⟨1, by decide⟩ : Action), (⟨0, by decide⟩ : Outcome)), ((⟨0, by decide⟩ : Action), (⟨0, by decide⟩ : Outcome))]]

def coefficients : Action → Outcome → Coordinate → Coordinate → ℚ :=
  ![![![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (1 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)]], ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)]]], ![![![(0 : ℚ), (1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)], ![(0 : ℚ), ((1 : ℚ) / 2), (0 : ℚ)]], ![![(1 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![((1 : ℚ) / 2), ((-1 : ℚ) / 2), (0 : ℚ)]]]]

def data : ExactCertificate.Data 2 2 2 1 3 where
  weight := weights
  kraus := krausData
  basis := basisData
  word := words
  unitIndex := (⟨0, by decide⟩ : Coordinate)
  coeff := fun e => coefficients e.1 e.2

theorem checked : ExactCertificate.check data = true := by decide +kernel

noncomputable def instruments := ExactCertificate.instrumentFamily data checked
noncomputable def presentation := ExactCertificate.presentation data checked

theorem all_word_response_iff (ρ σ : Density Hilbert) :
    presentation.coordinates ρ = presentation.coordinates σ ↔
      response instruments ρ = response instruments σ :=
  presentation.coordinates_eq_iff_response_eq ρ σ

theorem finite_tree_coordinates (π : Adaptive.Protocol Action Outcome)
    (ρ : Density Hilbert) (l : π.Leaf) :
    Adaptive.leafProbability instruments π ρ l =
      presentation.recordCoordinates (π.word l) (presentation.coordinates ρ)
        presentation.unitIndex :=
  Adaptive.leafProbability_eq_recordCoordinates_unit instruments presentation π ρ l

theorem all_finite_tree_laws (π : Adaptive.Protocol Action Outcome)
    (ρ σ : Density Hilbert)
    (h : presentation.coordinates ρ = presentation.coordinates σ) :
    Adaptive.leafProbability instruments π ρ =
      Adaptive.leafProbability instruments π σ :=
  Adaptive.leafProbability_eq_of_coordinates_eq instruments presentation h π

theorem complete_tree_normalization (π : Adaptive.Protocol Action Outcome)
    (ρ : Density Hilbert) :
    (∑ l : π.Leaf, Adaptive.leafProbability instruments π ρ l) = 1 :=
  Adaptive.sum_leafProbability instruments π ρ

theorem closed_coordinate_update (x : Set.range presentation.coordinates)
    (e : Action × Outcome) :
    Option.map Subtype.val (presentation.closedCoordinateUpdate x e) =
      presentation.coordinateUpdate x.val e :=
  presentation.closedCoordinateUpdate_map_val x e

#print axioms checked
#print axioms presentation
#print axioms all_word_response_iff
#print axioms finite_tree_coordinates
#print axioms all_finite_tree_laws
#print axioms complete_tree_normalization
#print axioms closed_coordinate_update

end UEOTQM.Generated.Certificate_6d0317ee7bb3888dc9b92431e5263f4f62802a6237dedeb2831a2a57201061f8
