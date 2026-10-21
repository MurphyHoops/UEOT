import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverage

/-!
# Exact TV through a finite carrier with an escape value

An actual finite encoder keeps all live atoms and sends every other point to
one escape value. If the source measure is supported on the finite carrier,
its TV distance from an arbitrary reference probability measure is preserved
exactly. The reverse inequality follows from measurable event traces and
probability complements; reference escape mass is retained without conditioning.

The cross-space endpoint uses one finite source PMF and matching live reference
atoms. A general PMF extension formula and live-history induction require no
finite ambient space. Construction of a controlled reference and its policy is
separate from these reusable comparison lemmas.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck

open MeasureTheory UEOT.V3.TotalVariation UEOT.V3.PathError
open scoped BigOperators Classical

noncomputable section

universe uI uY uZ u

/-- For probability measures, controlling every signed forward event gap also
controls its reverse: apply the same bound to the measurable complement. -/
theorem tvDist_le_of_event_sub_le
    {Y : Type uY} [MeasurableSpace Y]
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (b : ℝ)
    (hgap : ∀ A : Set Y, MeasurableSet A → μ.real A - ν.real A ≤ b) :
    tvDist μ ν ≤ b := by
  unfold tvDist
  refine csSup_le (tvEventSet_nonempty μ ν) ?_
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  have hpos := hgap A hA
  have hneg := hgap Aᶜ hA.compl
  have hμcompl := probReal_add_probReal_compl (μ := μ) hA
  have hνcompl := probReal_add_probReal_compl (μ := ν) hA
  rw [abs_le]
  constructor <;> linarith

/-- A measurable map loses no source/reference TV when every measurable
source-carrier trace is an exact pullback. The reference need not be supported
on that carrier. The trace condition is a structural property of the encoder. -/
theorem tvDist_map_eq_of_carrier_traces
    {Y : Type uY} {Z : Type uZ}
    [MeasurableSpace Y] [MeasurableSpace Z]
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : Set Y) (hS : MeasurableSet S) (hμS : μ.real Sᶜ = 0)
    (f : Y → Z) (hf : Measurable f)
    (htrace : ∀ A : Set Y, MeasurableSet A →
      ∃ B : Set Z, MeasurableSet B ∧ f ⁻¹' B = A ∩ S) :
    tvDist (μ.map f) (ν.map f) = tvDist μ ν := by
  letI : IsProbabilityMeasure (μ.map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (ν.map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  apply le_antisymm (tvDist_map_le μ ν f hf)
  apply tvDist_le_of_event_sub_le μ ν
  intro A hA
  obtain ⟨B, hB, hpre⟩ := htrace A hA
  have hdiff : μ.real (A \ S) = 0 := by
    apply le_antisymm _ measureReal_nonneg
    calc
      μ.real (A \ S) ≤ μ.real Sᶜ := measureReal_mono (by
        intro y hy
        exact hy.2)
      _ = 0 := hμS
  have hcut : μ.real (A ∩ S) = μ.real A := by
    have h := measureReal_inter_add_sdiff (μ := μ) (s := A) hS
    simpa only [hdiff, add_zero] using h
  have hνcut : ν.real (A ∩ S) ≤ ν.real A :=
    measureReal_mono Set.inter_subset_left
  have hμB : (μ.map f).real B = μ.real (A ∩ S) := by
    simp only [measureReal_def, Measure.map_apply hf hB, hpre]
  have hνB : (ν.map f).real B = ν.real (A ∩ S) := by
    simp only [measureReal_def, Measure.map_apply hf hB, hpre]
  have hencoded := (le_abs_self ((μ.map f).real B - (ν.map f).real B)).trans
    (tvEvent_le (μ.map f) (ν.map f) B hB)
  rw [hμB, hνB, hcut] at hencoded
  linarith

/-- Label the atoms of a finite injected carrier; all other points become
none. No reference mass is discarded, conditioned, or renormalized. -/
def atomEncode
    {I : Type uI} {Y : Type uY} (i : I → Y) (y : Y) : Option I :=
  if h : ∃ s, i s = y then some h.choose else none

theorem atomEncode_eq_some_iff
    {I : Type uI} {Y : Type uY} (i : I → Y) (hi : Function.Injective i)
    (y : Y) (s : I) : atomEncode i y = some s ↔ y = i s := by
  unfold atomEncode
  split_ifs with h
  · constructor
    · intro heq
      have hs : h.choose = s := Option.some.inj heq
      exact h.choose_spec.symm.trans (congrArg i hs)
    · intro heq
      have hs : h.choose = s := hi (h.choose_spec.trans heq)
      exact congrArg some hs
  · constructor
    · intro heq
      cases heq
    · intro heq
      exact False.elim (h ⟨s, heq.symm⟩)

@[simp] theorem atomEncode_atom
    {I : Type uI} {Y : Type uY} (i : I → Y) (hi : Function.Injective i)
    (s : I) : atomEncode i (i s) = some s :=
  (atomEncode_eq_some_iff i hi (i s) s).2 rfl

theorem atomEncode_eq_none_iff
    {I : Type uI} {Y : Type uY} (i : I → Y) (y : Y) :
    atomEncode i y = none ↔ y ∉ Set.range i := by
  unfold atomEncode
  split_ifs with h <;> simp [Set.mem_range, h]

/-- Finite carrier atoms are measurable; every encoder preimage is either
a subset of the finite carrier or the complement of such a subset. -/
theorem atomEncode_measurable
    {I : Type uI} {Y : Type uY} [Fintype I]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace (Option I)] (i : I → Y) :
    Measurable (atomEncode i) := by
  intro B _hB
  by_cases hn : (none : Option I) ∈ B
  · have hsub : (atomEncode i ⁻¹' B)ᶜ ⊆ Set.range i := by
      intro y hy
      by_contra hyi
      have he := (atomEncode_eq_none_iff i y).2 hyi
      exact hy (by simpa only [Set.mem_preimage, he] using hn)
    have hfinite := (Set.finite_range i).subset hsub
    simpa only [compl_compl] using hfinite.measurableSet.compl
  · have hsub : atomEncode i ⁻¹' B ⊆ Set.range i := by
      intro y hy
      by_contra hyi
      have he := (atomEncode_eq_none_iff i y).2 hyi
      exact hn (by simpa only [Set.mem_preimage, he] using hy)
    exact ((Set.finite_range i).subset hsub).measurableSet

/-- The structural trace hypothesis is proved for the actual finite encoder. -/
theorem atomEncode_carrier_trace
    {I : Type uI} {Y : Type uY} [Fintype I]
    [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (i : I → Y) (hi : Function.Injective i) (A : Set Y) :
    ∃ B : Set (Option I), MeasurableSet B ∧
      atomEncode i ⁻¹' B = A ∩ Set.range i := by
  let B : Set (Option I) := {z | match z with
    | none => False
    | some s => i s ∈ A}
  refine ⟨B, Set.to_countable _ |>.measurableSet, ?_⟩
  ext y
  by_cases hy : y ∈ Set.range i
  · obtain ⟨s, rfl⟩ := hy
    simp [B, atomEncode_atom i hi]
  · have he := (atomEncode_eq_none_iff i y).2 hy
    simp [B, he, hy]

/-- Exact finite-carrier TV preservation against an arbitrary reference.
The reference is allowed positive mass outside the finite carrier. -/
theorem tvDist_atomEncode_eq
    {I : Type uI} {Y : Type uY} [Fintype I]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (i : I → Y) (hi : Function.Injective i)
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ (Set.range i)ᶜ = 0) :
    tvDist (μ.map (atomEncode i)) (ν.map (atomEncode i)) = tvDist μ ν := by
  exact tvDist_map_eq_of_carrier_traces μ ν (Set.range i)
    (Set.finite_range i).measurableSet (by simp [measureReal_def, hμ])
    (atomEncode i) (atomEncode_measurable i)
    (fun A _ => atomEncode_carrier_trace i hi A)

/-- Every live atom retains its entire original PMF mass. -/
theorem atomEncode_map_some
    {I : Type uI} {Y : Type uY} (i : I → Y) (hi : Function.Injective i)
    (ν : PMF Y) (s : I) : (ν.map (atomEncode i)) (some s) = ν (i s) := by
  rw [PMF.map_apply]
  refine (tsum_eq_single (i s) ?_).trans ?_
  · intro y hy
    have hne : some s ≠ atomEncode i y := by
      intro heq
      exact hy ((atomEncode_eq_some_iff i hi y s).mp heq.symm)
    exact if_neg hne
  · simp [atomEncode_atom i hi]

/-- The none atom is exactly the original carrier-complement probability. -/
theorem atomEncode_escape_probability
    {I : Type uI} {Y : Type uY} [Fintype I]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (i : I → Y) (ν : Measure Y) :
    (ν.map (atomEncode i)).real {none} = ν.real (Set.range i)ᶜ := by
  have hpre : atomEncode i ⁻¹' ({none} : Set (Option I)) = (Set.range i)ᶜ := by
    ext y
    exact atomEncode_eq_none_iff i y
  simp only [measureReal_def,
    Measure.map_apply (atomEncode_measurable i) (measurableSet_singleton none), hpre]

/-- Probability normalization fixes the last atom after every other finite
atom has been matched. This accounts for all escape mass. -/
theorem pmf_eq_of_eq_except_one
    {I : Type uI} [Fintype I] (p q : PMF I) (escape : I)
    (h : ∀ s, s ≠ escape → p s = q s) : p = q := by
  have hsum : (∑ s, ((p s).toReal - (q s).toReal)) = 0 := by
    rw [Finset.sum_sub_distrib, coverage_sum_toReal, coverage_sum_toReal]
    simp
  have hsingle : (∑ s, ((p s).toReal - (q s).toReal)) =
      (p escape).toReal - (q escape).toReal := by
    apply Finset.sum_eq_single escape
    · intro s _ hs
      rw [h s hs]
      simp
    · intro hs
      exact False.elim (hs (Finset.mem_univ escape))
  rw [hsingle] at hsum
  apply PMF.ext
  intro s
  by_cases hs : s = escape
  · subst s
    apply (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top p escape) (PMF.apply_ne_top q escape)).mp
    linarith
  · exact h s hs

/-- Two reference processes may distribute their non-live mass differently.
Equal live masses force equality after the common finite escape encoding. -/
theorem atomEncode_reference_eq
    {I : Type uI} {Y : Type uY} {Z : Type uZ} [Fintype I]
    (i : I → Y) (hi : Function.Injective i)
    (j : I → Z) (hj : Function.Injective j)
    (ν : PMF Y) (ξ : PMF Z) (hlive : ∀ s, ν (i s) = ξ (j s)) :
    ν.map (atomEncode i) = ξ.map (atomEncode j) := by
  apply pmf_eq_of_eq_except_one _ _ none
  intro z hz
  cases z with
  | none => exact False.elim (hz rfl)
  | some s =>
      rw [atomEncode_map_some i hi, atomEncode_map_some j hj]
      exact hlive s

/-- A source already supplied on its finite live carrier automatically has
zero mass outside the carrier, so the exact TV encoding has no support premise
left for the caller to invent. -/
theorem tvDist_embedded_eq_encoded
    {I : Type uI} {Y : Type uY} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (i : I → Y) (hi : Function.Injective i) (p : PMF I) (ν : PMF Y) :
    tvDist (p.map i).toMeasure ν.toMeasure =
      tvDist (p.map some).toMeasure (ν.map (atomEncode i)).toMeasure := by
  have hiMeas : Measurable i := measurable_of_finite _
  have hcMeas := atomEncode_measurable i
  have hpre : i ⁻¹' (Set.range i)ᶜ = ∅ := by
    ext s
    simp
  have hp : (p.map i).toMeasure (Set.range i)ᶜ = 0 := by
    rw [← PMF.toMeasure_map i p hiMeas,
      Measure.map_apply hiMeas (Set.finite_range i).measurableSet.compl, hpre]
    simp
  have ht := tvDist_atomEncode_eq i hi (p.map i).toMeasure ν.toMeasure hp
  rw [PMF.toMeasure_map (atomEncode i) (p.map i) hcMeas,
    PMF.toMeasure_map (atomEncode i) ν hcMeas] at ht
  have hsource : (p.map i).map (atomEncode i) = p.map some := by
    rw [PMF.map_comp]
    congr 1
    funext s
    exact atomEncode_atom i hi s
  rw [hsource] at ht
  exact ht.symm

/-- Complete cross-space TV transfer from identical live reference masses.
The two original reference PMFs need not be related by a path pushforward. -/
theorem tvDist_eq_of_live_reference_masses
    {I : Type uI} {Y : Type uY} {Z : Type uZ} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (i : I → Y) (hi : Function.Injective i)
    (j : I → Z) (hj : Function.Injective j)
    (p : PMF I) (ν : PMF Y) (ξ : PMF Z)
    (hlive : ∀ s, ν (i s) = ξ (j s)) :
    tvDist (p.map i).toMeasure ν.toMeasure =
      tvDist (p.map j).toMeasure ξ.toMeasure := by
  rw [tvDist_embedded_eq_encoded i hi, tvDist_embedded_eq_encoded j hj,
    atomEncode_reference_eq i hi j hj ν ξ hlive]

/-- The exact extension atom formula does not require a finite history or
record alphabet: both off-diagonal sums vanish by product injectivity. -/
theorem pmfExtend_apply_general
    {H : Type*} {Z : Type*}
    (p : PMF H) (K : H → PMF Z) (h : H) (z : Z) :
    pmfExtend p K (h, z) = p h * K h z := by
  unfold pmfExtend
  rw [PMF.bind_apply]
  refine (tsum_eq_single h ?_).trans ?_
  · intro h' hne
    have hzero : ((K h').map (fun z' => (h', z'))) (h, z) = 0 := by
      rw [PMF.map_apply]
      trans ∑' _ : Z, (0 : ENNReal)
      · apply tsum_congr
        intro z'
        have he : (h, z) ≠ (h', z') := by
          intro heq
          exact hne (congrArg Prod.fst heq).symm
        exact if_neg he
      · simp
    rw [hzero, mul_zero]
  · apply congrArg (fun t : ENNReal => p h * t)
    rw [PMF.map_apply]
    refine (tsum_eq_single z ?_).trans ?_
    · intro z' hne
      have he : (h, z) ≠ (h, z') := by
        intro heq
        exact hne (congrArg Prod.snd heq).symm
      exact if_neg he
    · simp

/-- Point masses of corresponding complete live histories agree if the
actual initial masses and actual conditional extension masses agree there.
This is the PMF path induction used by the explicit absorbing reference. -/
theorem causalLaw_live_history_mass
    {I R Y W Z V : Type u}
    (i : I → Y) (r : R → W) (j : I → Z) (s : R → V)
    (p : PMF Y) (q : PMF Z)
    (K : ∀ n, CausalHistory Y W n → PMF W)
    (L : ∀ n, CausalHistory Z V n → PMF V)
    (hinit : ∀ x, p (i x) = q (j x))
    (hstep : ∀ n (h : CausalHistory I R n) z,
      K n (riskHistoryMap i r n h) (r z) =
        L n (riskHistoryMap j s n h) (s z)) :
    ∀ n (h : CausalHistory I R n),
      causalLaw p K n (riskHistoryMap i r n h) =
        causalLaw q L n (riskHistoryMap j s n h) := by
  intro n
  induction n with
  | zero => exact hinit
  | succ n ih =>
      intro h
      change pmfExtend (causalLaw p K n) (K n)
          (riskHistoryMap i r n h.1, r h.2) =
        pmfExtend (causalLaw q L n) (L n)
          (riskHistoryMap j s n h.1, s h.2)
      rw [pmfExtend_apply_general, pmfExtend_apply_general, ih h.1, hstep n h.1 h.2]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck
