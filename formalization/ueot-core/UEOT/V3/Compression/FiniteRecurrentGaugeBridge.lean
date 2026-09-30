import UEOT.V3.Compression.RecurrentClassGaugeInvariance
import UEOT.V3.FiniteRecurrentDecompositionStability

/-!
# Finite recurrent-decomposition gauge bridge

This module connects the generic recurrent gauge layer back to the frozen
P-GOA-03 `FiniteRecurrentDecomposition` source structure.

The bridge is deliberately one-sided at first: a certified source decomposition
already determines recurrent carriers, class-supported invariant laws, and an
absorption-weighted recurrent-mixture Cesaro limit.  Under arbitrary exact state
gauge, these physical objects transport to the target kernel even if the target
has not been repackaged using the same transient/recurrent coordinate split.

This avoids treating the bookkeeping labels `T`, `R`, or `C` as physical gauge
invariants.
-/

namespace UEOT.V3.Compression.FiniteRecurrentGaugeBridge

open Filter Topology
open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.FiniteCesaroInvariant
open UEOT.V3.FiniteRecurrentDecompositionStability
open UEOT.V3.Compression.GoaGaugeInvariance
open UEOT.V3.Compression.RecurrentClassGaugeInvariance
open UEOT.V3.Compression.CesaroOccupationGaugeInvariance
open UEOT.V3.Compression.InvariantSetGaugeInvariance

universe uT uR uC

noncomputable section

variable {T : Type uT} [Fintype T] [DecidableEq T]
variable {R : Type uR} [Fintype R] [DecidableEq R]
variable {C : Type uC} [Fintype C] [DecidableEq C]
variable {K : RecurrentPartition R C}

/-- The physical state carrier of one recurrent class in a frozen
`FiniteRecurrentDecomposition`. -/
def classCarrier (K : RecurrentPartition R C) (c : C) :
    Set (FullState T R) :=
  {x | match x with
    | Sum.inl _ => False
    | Sum.inr r => K.classOf r = c}

@[simp] theorem mem_classCarrier_inl
    (K : RecurrentPartition R C) (c : C) (i : T) :
    Sum.inl i ∉ classCarrier (T := T) K c := by
  simp [classCarrier]

@[simp] theorem mem_classCarrier_inr
    (K : RecurrentPartition R C) (c : C) (r : R) :
    Sum.inr r ∈ classCarrier (T := T) K c ↔ K.classOf r = c := by
  rfl

/-- Every recurrent class stored by the frozen P-GOA-03 decomposition is a
closed communicating carrier in the generic gauge sense. -/
theorem decomposition_class_is_recurrentCarrier
    (M : FiniteRecurrentDecomposition (T := T) K) (c : C) :
    RecurrentCarrier M.P (classCarrier (T := T) K c) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases K.class_nonempty c with ⟨r, hr⟩
    exact ⟨Sum.inr r, hr⟩
  · intro x hx y hy
    rcases x with i | r
    · exact (mem_classCarrier_inl (T := T) K c i hx).elim
    · rcases y with j | s
      · exact (mem_classCarrier_inl (T := T) K c j hy).elim
      · have hr : K.classOf r = c := hx
        have hs : K.classOf s = c := hy
        constructor
        · rcases M.class_communicates c r s hr hs with ⟨n, hnpos, hn⟩
          exact ⟨n, hn⟩
        · rcases M.class_communicates c s r hs hr with ⟨n, hnpos, hn⟩
          exact ⟨n, hn⟩
  · intro x hx y hxy
    rcases x with i | r
    · exact (mem_classCarrier_inl (T := T) K c i hx).elim
    · have hr : K.classOf r = c := hx
      rcases y with j | s
      · have hz := M.recurrent_to_transient_zero r j
        linarith
      · by_cases hs : K.classOf s = c
        · exact hs
        · have hne : K.classOf r ≠ K.classOf s := by
            rw [hr]
            exact Ne.symm hs
          have hz := M.recurrent_cross_zero r s hne
          linarith

/-- The stored class law is supported exactly inside its recurrent carrier. -/
theorem classLaw_supportedOn_classCarrier
    (M : FiniteRecurrentDecomposition (T := T) K) (c : C) :
    SupportedOn (M.classLaw c) (classCarrier (T := T) K c) := by
  intro x hx
  rcases x with i | r
  · exact M.classLaw_transient_zero c i
  · have hne : K.classOf r ≠ c := by
      intro hrc
      exact hx hrc
    exact M.classLaw_other_zero c r hne

/-- The stored class law belongs to the generic invariant-law set. -/
theorem classLaw_mem_invariantLawSet
    (M : FiniteRecurrentDecomposition (T := T) K) (c : C) :
    M.classLaw c ∈ invariantLawSet M.P M.stochastic := by
  apply Subtype.ext
  exact M.classLaw_invariant c

/-- The frozen class law is therefore an invariant law carried by the frozen
recurrent class in the generic structural gauge language. -/
theorem classLaw_mem_carrierInvariantLawSet
    (M : FiniteRecurrentDecomposition (T := T) K) (c : C) :
    M.classLaw c ∈
      carrierInvariantLawSet M.P M.stochastic (classCarrier (T := T) K c) := by
  exact ⟨classLaw_mem_invariantLawSet M c, classLaw_supportedOn_classCarrier M c⟩

/-- Relabeling commutes exactly with a finite mixture when only the state
coordinate is gauged and class weights are unchanged. -/
theorem recurrentMixture_relabel
    {S : Type*} [Fintype S] [Nonempty S]
    (e : S ≃ S) (w : stdSimplex ℝ C) (pi : C → stdSimplex ℝ S) :
    relabelSimplex e (recurrentMixture w pi) =
      recurrentMixture w (fun c => relabelSimplex e (pi c)) := by
  apply Subtype.ext
  funext y
  rcases e.surjective y with ⟨s, rfl⟩
  change
    (relabelSimplex e (recurrentMixture w pi)).1 (e s) =
      (recurrentMixture w (fun c => relabelSimplex e (pi c))).1 (e s)
  calc
    (relabelSimplex e (recurrentMixture w pi)).1 (e s) =
        (recurrentMixture w pi).1 s :=
      relabelSimplex_apply_e e (recurrentMixture w pi) s
    _ = ∑ c, w.1 c * (pi c).1 s := by
      rw [recurrentMixture_apply]
    _ = ∑ c, w.1 c * (relabelSimplex e (pi c)).1 (e s) := by
      apply Finset.sum_congr rfl
      intro c hc
      change w.1 c * (pi c).1 s =
        w.1 c * (relabelSimplex e (pi c)).1 (e s)
      congr 1
      change (pi c).1 s = (pi c).1 (e.symm (e s))
      simp
    _ = (recurrentMixture w (fun c => relabelSimplex e (pi c))).1 (e s) := by
      rw [recurrentMixture_apply]

/-- One frozen P-GOA-03 recurrent class transports to a target recurrent
carrier together with its carried invariant law under arbitrary exact state
gauge. -/
theorem decomposition_class_transport
    (M : FiniteRecurrentDecomposition (T := T) K)
    (Ptarget : Matrix (FullState T R) (FullState T R) ℝ)
    (hPtarget : Ptarget ∈ Matrix.rowStochastic ℝ (FullState T R))
    (e : FullState T R ≃ FullState T R)
    (hconj : ∀ s t, M.P s t = Ptarget (e s) (e t))
    (c : C) :
    RecurrentCarrier Ptarget (e '' classCarrier (T := T) K c) ∧
      relabelSimplex e (M.classLaw c) ∈
        carrierInvariantLawSet Ptarget hPtarget
          (e '' classCarrier (T := T) K c) := by
  let r0 : R := Classical.choose (K.class_nonempty c)
  letI : Nonempty (FullState T R) := ⟨Sum.inr r0⟩
  constructor
  · exact (recurrentCarrier_image_iff M.P Ptarget e hconj
      (classCarrier (T := T) K c)).2
      (decomposition_class_is_recurrentCarrier M c)
  · have hset := carrierInvariantLawSet_relabel_eq
      M.P Ptarget M.stochastic hPtarget e hconj (classCarrier (T := T) K c)
    rw [hset]
    exact ⟨M.classLaw c, classLaw_mem_carrierInvariantLawSet M c, rfl⟩

end

end UEOT.V3.Compression.FiniteRecurrentGaugeBridge
