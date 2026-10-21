import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape

/-!
Exact complete-history path TV through a finite observation image and an explicit escape state. The actual microscopic kernel and the entire state-action occupancy law use the original policy. Absorbing reference paths match full live histories; no coordinatewise reference path equality is assumed.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck

open MeasureTheory UEOT.V3.TotalVariation UEOT.V3.PathError
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck
open scoped BigOperators Classical

noncomputable section

universe u

/-- Composition acts on the entire history, including every recorded action. -/
theorem riskHistoryMap_comp_general
    {X Y Z R S V : Type u}
    (f : X → Y) (g : R → S) (f' : Y → Z) (g' : S → V) :
    ∀ n (h : CausalHistory X R n),
      riskHistoryMap f' g' n (riskHistoryMap f g n h) =
        riskHistoryMap (f' ∘ f) (g' ∘ g) n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
      intro h
      change (riskHistoryMap f' g' n (riskHistoryMap f g n h.1), g' (g h.2)) =
        (riskHistoryMap (f' ∘ f) (g' ∘ g) n h.1, (g' ∘ g) h.2)
      rw [ih h.1]
      rfl

/-- Injecting both kinds of records injects every complete finite history. -/
theorem riskHistoryMap_injective_general
    {X Y R S : Type u} (f : X → Y) (g : R → S)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∀ n, Function.Injective (riskHistoryMap f g n) := by
  intro n
  induction n with
  | zero => exact hf
  | succ n ih =>
      intro h k heq
      change (riskHistoryMap f g n h.1, g h.2) =
        (riskHistoryMap f g n k.1, g k.2) at heq
      apply Prod.ext
      · exact ih (congrArg Prod.fst heq)
      · exact hg (congrArg Prod.snd heq)

abbrev observationHistoryMap
    {X Y A : Type u} (q : X → Y) (n : ℕ) :
    CausalHistory X (A × X) n → CausalHistory Y (A × Y) n :=
  riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n

theorem observationHistoryMap_comp
    {X Y Z A : Type u} (f : X → Y) (g : Y → Z)
    (n : ℕ) (h : CausalHistory X (A × X) n) :
    observationHistoryMap g n (observationHistoryMap f n h) =
      observationHistoryMap (g ∘ f) n h :=
  riskHistoryMap_comp_general f (fun ax : A × X => (ax.1, f ax.2))
    g (fun ay : A × Y => (ay.1, g ay.2)) n h

theorem observationHistoryMap_injective
    {X Y A : Type u} (i : X → Y) (hi : Function.Injective i) (n : ℕ) :
    Function.Injective (observationHistoryMap (A := A) i n) := by
  refine riskHistoryMap_injective_general i
    (fun ax : A × X => (ax.1, i ax.2)) hi ?_ n
  intro a b heq
  change (a.1, i a.2) = (b.1, i b.2) at heq
  apply Prod.ext
  · exact congrArg (fun z : A × Y => z.1) heq
  · exact hi (congrArg (fun z : A × Y => z.2) heq)

theorem map_observationHistoryMap_comp
    {X Y Z A : Type u} (f : X → Y) (g : Y → Z)
    (n : ℕ) (p : PMF (CausalHistory X (A × X) n)) :
    (p.map (observationHistoryMap f n)).map (observationHistoryMap g n) =
      p.map (observationHistoryMap (g ∘ f) n) := by
  rw [PMF.map_comp]
  congr 1
  funext h
  exact observationHistoryMap_comp f g n h

/-- The fallback makes decoding total. Its value cannot affect a live history. -/
def escapeDecode {I Y : Type u} (i : I → Y) (fallback : Y) : Option I → Y
  | none => fallback
  | some s => i s

/-- Original reference mass outside the finite carrier becomes an absorbing
escape state. Live-to-live atoms retain their original unconditional mass. -/
def escapeReferenceKernel
    {I Y A : Type u} (i : I → Y) (Q : ℕ → Y → A → PMF Y) :
    ℕ → Option I → A → PMF (Option I)
  | _, none, _ => PMF.pure none
  | n, some s, a => (Q n (i s) a).map (atomEncode i)

/-- The complete original policy supplies actions at every encoded history. -/
def escapePolicy
    {I Y A : Type u} (i : I → Y) (fallback : Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) :
    ∀ n, CausalHistory (Option I) (A × Option I) n → PMF A :=
  fun n h => π n (observationHistoryMap (escapeDecode i fallback) n h)

theorem escapePolicy_live_history
    {I Y A : Type u} (i : I → Y) (fallback : Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (n : ℕ) (h : CausalHistory I (A × I) n) :
    escapePolicy i fallback π n (observationHistoryMap some n h) =
      π n (observationHistoryMap i n h) := by
  unfold escapePolicy
  rw [observationHistoryMap_comp]
  rfl

theorem escapePolicy_actual_history
    {X I Y A : Type u} (qI : X → I) (i : I → Y) (fallback : Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (n : ℕ) (h : CausalHistory X (A × X) n) :
    escapePolicy i fallback π n
        (observationHistoryMap (fun x => some (qI x)) n h) =
      π n (observationHistoryMap (i ∘ qI) n h) := by
  unfold escapePolicy
  rw [observationHistoryMap_comp]
  rfl

/-- Coding the observation does not change any actual microscopic kernel. -/
theorem escape_micro_control_kernel
    {X I Y A : Type u} (qI : X → I) (i : I → Y) (fallback : Y)
    (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) :
    riskMicroControlKernel (fun x => some (qI x)) P (escapePolicy i fallback π) =
      riskMicroControlKernel (i ∘ qI) P π := by
  funext n h
  change pmfExtend
      (escapePolicy i fallback π n
        (observationHistoryMap (fun x => some (qI x)) n h))
      (P n (riskLastState n h)) =
    pmfExtend (π n (observationHistoryMap (i ∘ qI) n h))
      (P n (riskLastState n h))
  rw [escapePolicy_actual_history]

/-- The entire actual state/action PMF is identical, not just its bad mass. -/
theorem escape_deployment_row_law
    {X I Y A : Type u} (p₀ : PMF X) (qI : X → I)
    (i : I → Y) (fallback : Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) (n : ℕ) :
    coverageDeploymentRowLaw p₀ (fun x => some (qI x)) P
        (escapePolicy i fallback π) n =
      coverageDeploymentRowLaw p₀ (i ∘ qI) P π n := by
  have hp : (fun h : CausalHistory X (A × X) n =>
      escapePolicy i fallback π n
        (observationHistoryMap (fun x => some (qI x)) n h)) =
      (fun h => π n (observationHistoryMap (i ∘ qI) n h)) :=
    funext (escapePolicy_actual_history qI i fallback π n)
  unfold coverageDeploymentRowLaw
  rw [escape_micro_control_kernel, hp]

/-- Initial live atoms are compared as genuine PMF masses. -/
theorem escape_initial_live_mass
    {X I Y : Type u} (p₀ : PMF X) (qI : X → I)
    (i : I → Y) (hi : Function.Injective i) (s : I) :
    (p₀.map (i ∘ qI)) (i s) =
      (p₀.map (fun x => some (qI x))) (some s) := by
  have hm : (p₀.map (i ∘ qI)).map (atomEncode i) =
      p₀.map (fun x => some (qI x)) := by
    rw [PMF.map_comp]
    congr 1
    funext x
    exact atomEncode_atom i hi (qI x)
  rw [← hm, atomEncode_map_some i hi]

/-- The conditional action/observation atom on a live history is exact.
This calculation uses the arbitrary-alphabet extension formula. -/
theorem escape_macro_live_mass
    {I Y A : Type u} (i : I → Y) (hi : Function.Injective i)
    (fallback : Y) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (n : ℕ) (h : CausalHistory I (A × I) n) (a : A) (s : I) :
    riskMacroControlKernel Q π n (observationHistoryMap i n h) (a, i s) =
      riskMacroControlKernel (escapeReferenceKernel i Q) (escapePolicy i fallback π)
        n (observationHistoryMap some n h) (a, some s) := by
  unfold riskMacroControlKernel
  rw [pmfExtend_apply_general, pmfExtend_apply_general,
    escapePolicy_live_history, risk_last_project, risk_last_project]
  change (π n (observationHistoryMap i n h)) a *
      (Q n (i (riskLastState n h)) a) (i s) =
    (π n (observationHistoryMap i n h)) a *
      ((Q n (i (riskLastState n h)) a).map (atomEncode i)) (some s)
  rw [atomEncode_map_some i hi]

/-- Every complete live reference history keeps its unconditional probability.
An escape at any earlier time excludes a history from this statement. -/
theorem escape_reference_live_history_mass
    {X I Y A : Type u} (p₀ : PMF X) (qI : X → I)
    (i : I → Y) (hi : Function.Injective i) (fallback : Y)
    (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (n : ℕ) (h : CausalHistory I (A × I) n) :
    causalLaw (p₀.map (i ∘ qI)) (riskMacroControlKernel Q π) n
        (observationHistoryMap i n h) =
      causalLaw (p₀.map (fun x => some (qI x)))
        (riskMacroControlKernel (escapeReferenceKernel i Q) (escapePolicy i fallback π))
        n (observationHistoryMap some n h) := by
  exact causalLaw_live_history_mass
    i (fun az : A × I => (az.1, i az.2))
    some (fun az : A × I => (az.1, some az.2))
    (p₀.map (i ∘ qI)) (p₀.map (fun x => some (qI x)))
    (riskMacroControlKernel Q π)
    (riskMacroControlKernel (escapeReferenceKernel i Q) (escapePolicy i fallback π))
    (escape_initial_live_mass p₀ qI i hi)
    (fun n h z => escape_macro_live_mass i hi fallback Q π n h z.1 z.2) n h

/-- Exact path-TV comparison via two encoders into the same Option of full
live histories. The ambient observation type Y may be infinite. -/
theorem escape_path_tv
    {X I Y A : Type u} [Fintype I] [Fintype A]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (p₀ : PMF X) (qI : X → I) (i : I → Y) (hi : Function.Injective i)
    (fallback : Y) (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) (n : ℕ) :
    tvDist ((causalLaw p₀ (riskMicroControlKernel (i ∘ qI) P π) n).map
        (observationHistoryMap (i ∘ qI) n)).toMeasure
      (causalLaw (p₀.map (i ∘ qI)) (riskMacroControlKernel Q π) n).toMeasure =
    tvDist ((causalLaw p₀
        (riskMicroControlKernel (fun x => some (qI x)) P (escapePolicy i fallback π)) n).map
        (observationHistoryMap (fun x => some (qI x)) n)).toMeasure
      (causalLaw (p₀.map (fun x => some (qI x)))
        (riskMacroControlKernel (escapeReferenceKernel i Q) (escapePolicy i fallback π)) n).toMeasure := by
  letI : MeasurableSpace (Option (CausalHistory I (A × I) n)) := ⊤
  rw [escape_micro_control_kernel]
  let r : PMF (CausalHistory I (A × I) n) :=
    (causalLaw p₀ (riskMicroControlKernel (i ∘ qI) P π) n).map
      (observationHistoryMap qI n)
  have ht := tvDist_eq_of_live_reference_masses
    (observationHistoryMap (A := A) i n) (observationHistoryMap_injective i hi n)
    (observationHistoryMap (A := A) some n)
      (observationHistoryMap_injective some (fun _ _ h => Option.some.inj h) n)
    r (causalLaw (p₀.map (i ∘ qI)) (riskMacroControlKernel Q π) n)
    (causalLaw (p₀.map (fun x => some (qI x)))
      (riskMacroControlKernel (escapeReferenceKernel i Q) (escapePolicy i fallback π)) n)
    (escape_reference_live_history_mass p₀ qI i hi fallback Q π n)
  dsimp only [r] at ht
  rw [map_observationHistoryMap_comp, map_observationHistoryMap_comp] at ht
  exact ht

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck
