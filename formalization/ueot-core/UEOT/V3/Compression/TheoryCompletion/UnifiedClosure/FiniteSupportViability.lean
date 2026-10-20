import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportCoverage

/-!
# Finite actual-support viability and exact policy existence

The policy-independent support recursion is proved equal to actual
history-conditioned support. Backward viability of every positive initial
observation fiber is equivalent to a full history policy with zero actual
uncertified-row occupancy before the finite horizon. A full fallback is
retained, including at horizon zero; no universal feasibility is asserted.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace SupportViabilityClosure

open MeasureTheory UEOT.V3.PathError
open scoped BigOperators Classical

noncomputable section

universe u

/-- The union of supported source successors sharing the next observation. -/
def successorSupport
    {X Y A : Type u} (q : X → Y) (P : ℕ → X → A → PMF X)
    (n : ℕ) (S : Set X) (a : A) (y : Y) : Set X :=
  {x' | q x' = y ∧ ∃ x ∈ S, x' ∈ (P n x a).support}

/-- Initial source support conditioned on one observed initial record. -/
def initialSupport
    {X Y : Type u} (p₀ : PMF X) (q : X → Y) (y : Y) : Set X :=
  {x | x ∈ p₀.support ∧ q x = y}

/-- Policy-independent support recursion along the recorded observations
and actions. Its identification with a posterior needs positive history mass. -/
def traceSupport
    {X Y A : Type u} (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) :
    ∀ n, CausalHistory Y (A × Y) n → Set X
  | 0, y => initialSupport p₀ q y
  | n + 1, h => successorSupport q P n (traceSupport p₀ q P n h.1) h.2.1 h.2.2

/-- An abbreviation of the existing complete-history projection. -/
abbrev projectHistory
    {X Y A : Type u} (q : X → Y) (n : ℕ) :
    CausalHistory X (A × X) n → CausalHistory Y (A × Y) n :=
  riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n

/-- An abbreviation of the existing actual microscopic causal law. -/
abbrev microLaw
    {X Y A : Type u} (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) (n : ℕ) :
    PMF (CausalHistory X (A × X) n) :=
  causalLaw p₀ (riskMicroControlKernel q P π) n

/-- The actual microscopic causal law pushed through that same projection. -/
abbrev coarseLaw
    {X Y A : Type u} (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) (n : ℕ) :
    PMF (CausalHistory Y (A × Y) n) :=
  (microLaw p₀ q P π n).map (projectHistory q n)

private theorem mem_pmfExtend_support_iff
    {H Z : Type u} [Fintype H] [Fintype Z]
    (p : PMF H) (K : H → PMF Z) (h : H) (z : Z) :
    (h, z) ∈ (pmfExtend p K).support ↔ h ∈ p.support ∧ z ∈ (K h).support := by
  rw [PMF.mem_support_iff, pmfExtend_apply, mul_ne_zero_iff,
    ← PMF.mem_support_iff, ← PMF.mem_support_iff]

/-- Actual microscopic support factors into prior history, its actual
coarse-history policy action, and the fixed source transition support. -/
theorem mem_microLaw_succ_support_iff
    {X Y A : Type u} [Fintype X] [Fintype A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (n : ℕ) (h : CausalHistory X (A × X) n) (a : A) (x : X) :
    (h, (a, x)) ∈ (microLaw p₀ q P π (n + 1)).support ↔
      h ∈ (microLaw p₀ q P π n).support ∧
        a ∈ (π n (projectHistory q n h)).support ∧
          x ∈ (P n (riskLastState n h) a).support := by
  change (h, (a, x)) ∈
      (pmfExtend (microLaw p₀ q P π n) (riskMicroControlKernel q P π n)).support ↔ _
  rw [mem_pmfExtend_support_iff]
  change (_ ∧ (a, x) ∈
    (pmfExtend (π n (projectHistory q n h)) (P n (riskLastState n h))).support) ↔ _
  rw [mem_pmfExtend_support_iff]

/-- Initial observation support is exactly nonempty initial source support
in that observation fiber. No policy or positive-action premise is needed. -/
theorem mem_coarseLaw_zero_support_iff
    {X Y A : Type u}
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) (y : Y) :
    y ∈ (coarseLaw p₀ q P π 0).support ↔ (initialSupport p₀ q y).Nonempty := by
  change y ∈ (p₀.map q).support ↔ ∃ x, x ∈ p₀.support ∧ q x = y
  exact PMF.mem_support_map_iff q p₀ y

private theorem mem_coarseLaw_succ_support_raw_iff
    {X Y A : Type u} [Fintype X] [Fintype A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (n : ℕ) (g : CausalHistory Y (A × Y) n) (a : A) (y : Y) :
    (g, (a, y)) ∈ (coarseLaw p₀ q P π (n + 1)).support ↔
      ∃ h ∈ (microLaw p₀ q P π n).support,
        projectHistory q n h = g ∧ a ∈ (π n g).support ∧
          ∃ x, x ∈ (P n (riskLastState n h) a).support ∧ q x = y := by
  constructor
  · intro hg
    obtain ⟨hnext, hhnext, hproject⟩ :=
      (PMF.mem_support_map_iff (projectHistory q (n + 1))
        (microLaw p₀ q P π (n + 1)) (g, (a, y))).mp hg
    rcases hnext with ⟨h, b, x⟩
    have hp : (projectHistory q n h, (b, q x)) = (g, (a, y)) := hproject
    have hprior : projectHistory q n h = g := congrArg Prod.fst hp
    have haction : b = a := congrArg (fun z => z.2.1) hp
    have hobs : q x = y := congrArg (fun z => z.2.2) hp
    subst b
    have hs := (mem_microLaw_succ_support_iff p₀ q P π n h a x).mp hhnext
    refine ⟨h, hs.1, hprior, ?_, x, hs.2.2, hobs⟩
    simpa only [hprior] using hs.2.1
  · rintro ⟨h, hh, hprior, ha, x, hx, hobs⟩
    apply (PMF.mem_support_map_iff (projectHistory q (n + 1))
      (microLaw p₀ q P π (n + 1)) (g, (a, y))).mpr
    refine ⟨(h, (a, x)), ?_, ?_⟩
    · apply (mem_microLaw_succ_support_iff p₀ q P π n h a x).mpr
      exact ⟨hh, by simpa only [hprior] using ha, hx⟩
    · change (projectHistory q n h, (a, q x)) = (g, (a, y))
      rw [hprior, hobs]

/- This fragment continues inside the open SupportViabilityClosure namespace. -/

/-- At a positive-mass complete observed history, the policy-independent
trace support consists exactly of terminal states of actual supported
microscopic histories in that same observation/action history fiber. -/
theorem mem_traceSupport_iff_realized
    {X Y A : Type u} [Fintype X] [Fintype A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) (n : ℕ) :
    ∀ (g : CausalHistory Y (A × Y) n)
      (_hg : g ∈ (coarseLaw p₀ q P π n).support) (x : X),
      x ∈ traceSupport p₀ q P n g ↔
        ∃ h ∈ (microLaw p₀ q P π n).support,
          projectHistory q n h = g ∧ riskLastState n h = x := by
  induction n with
  | zero =>
      intro g _ x
      change (x ∈ p₀.support ∧ q x = g) ↔
        ∃ h ∈ p₀.support, q h = g ∧ h = x
      constructor
      · intro hx
        exact ⟨x, hx.1, hx.2, rfl⟩
      · rintro ⟨h, hh, hq, rfl⟩
        exact ⟨hh, hq⟩
  | succ n ih =>
      intro g hg x
      rcases g with ⟨g, a, y⟩
      obtain ⟨h₀, hh₀, hf₀, ha, _⟩ :=
        (mem_coarseLaw_succ_support_raw_iff p₀ q P π n g a y).mp hg
      have hgold : g ∈ (coarseLaw p₀ q P π n).support :=
        (PMF.mem_support_map_iff (projectHistory q n) (microLaw p₀ q P π n) g).mpr
          ⟨h₀, hh₀, hf₀⟩
      change (q x = y ∧ ∃ z ∈ traceSupport p₀ q P n g,
          x ∈ (P n z a).support) ↔ _
      constructor
      · rintro ⟨hqx, z, hz, htrans⟩
        obtain ⟨h, hh, hf, hlast⟩ := (ih g hgold z).mp hz
        refine ⟨(h, (a, x)), ?_, ?_, rfl⟩
        · apply (mem_microLaw_succ_support_iff p₀ q P π n h a x).mpr
          exact ⟨hh, by simpa only [hf] using ha,
            by simpa only [hlast] using htrans⟩
        · change (projectHistory q n h, (a, q x)) = (g, (a, y))
          rw [hf, hqx]
      · rintro ⟨hnext, hhnext, hfnext, hlast⟩
        rcases hnext with ⟨h, b, z⟩
        have hp : (projectHistory q n h, (b, q z)) = (g, (a, y)) := hfnext
        have hf : projectHistory q n h = g := congrArg Prod.fst hp
        have hb : b = a := congrArg (fun h => h.2.1) hp
        have hqz : q z = y := congrArg (fun h => h.2.2) hp
        change z = x at hlast
        subst b
        subst z
        have hs := (mem_microLaw_succ_support_iff p₀ q P π n h a x).mp hhnext
        refine ⟨hqz, riskLastState n h, ?_, hs.2.2⟩
        exact (ih g hgold (riskLastState n h)).mpr ⟨h, hs.1, hf, rfl⟩

/-- Exact next-history positivity, with both the actual prior history mass
and the actual policy action mass retained. Potential successors alone do
not assert positive mass under a policy assigning that action zero mass. -/
theorem mem_coarseLaw_succ_support_iff
    {X Y A : Type u} [Fintype X] [Fintype A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (n : ℕ) (g : CausalHistory Y (A × Y) n) (a : A) (y : Y) :
    (g, (a, y)) ∈ (coarseLaw p₀ q P π (n + 1)).support ↔
      g ∈ (coarseLaw p₀ q P π n).support ∧
        a ∈ (π n g).support ∧
          (successorSupport q P n (traceSupport p₀ q P n g) a y).Nonempty := by
  constructor
  · intro hg
    obtain ⟨h, hh, hf, ha, x, hx, hqx⟩ :=
      (mem_coarseLaw_succ_support_raw_iff p₀ q P π n g a y).mp hg
    have hgold : g ∈ (coarseLaw p₀ q P π n).support :=
      (PMF.mem_support_map_iff (projectHistory q n) (microLaw p₀ q P π n) g).mpr
        ⟨h, hh, hf⟩
    refine ⟨hgold, ha, x, hqx, riskLastState n h, ?_, hx⟩
    exact (mem_traceSupport_iff_realized p₀ q P π n g hgold (riskLastState n h)).mpr
      ⟨h, hh, hf, rfl⟩
  · rintro ⟨hg, ha, x, hqx, z, hz, hx⟩
    obtain ⟨h, hh, hf, hlast⟩ :=
      (mem_traceSupport_iff_realized p₀ q P π n g hg z).mp hz
    apply (mem_coarseLaw_succ_support_raw_iff p₀ q P π n g a y).mpr
    exact ⟨h, hh, hf, ha, x, by simpa only [hlast] using hx, hqx⟩

/-- The support recursion is the support of the existing actual
history-fiber posterior, pushed to the terminal microscopic state.
There is intentionally no posterior value or condition at a null history. -/
theorem traceSupport_eq_fiberTerminalPosterior_support
    {X Y A : Type u} [Fintype X] [Fintype A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (n : ℕ) (g : CausalHistory Y (A × Y) n)
    (hg : g ∈ (coarseLaw p₀ q P π n).support) :
    traceSupport p₀ q P n g =
      (PosteriorSupportCoverageCheck.fiberTerminalPosterior
        (microLaw p₀ q P π n) (projectHistory q n) (riskLastState n) g hg).support := by
  ext x
  exact (mem_traceSupport_iff_realized p₀ q P π n g hg x).trans
    (PosteriorSupportCoverageCheck.mem_fiberTerminalPosterior_support_iff
      (microLaw p₀ q P π n) (projectHistory q n) (riskLastState n) g hg x).symm

/-- The actual next-history posterior support is exactly the source
successor union for that recorded action and observation. -/
theorem successorSupport_eq_fiberTerminalPosterior_support
    {X Y A : Type u} [Fintype X] [Fintype A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (n : ℕ) (g : CausalHistory Y (A × Y) n) (a : A) (y : Y)
    (hg : (g, (a, y)) ∈ (coarseLaw p₀ q P π (n + 1)).support) :
    successorSupport q P n (traceSupport p₀ q P n g) a y =
      (PosteriorSupportCoverageCheck.fiberTerminalPosterior
        (microLaw p₀ q P π (n + 1)) (projectHistory q (n + 1))
        (riskLastState (n + 1)) (g, (a, y)) hg).support :=
  traceSupport_eq_fiberTerminalPosterior_support p₀ q P π (n + 1) (g, (a, y)) hg

/-- The actual deployment row support is witnessed by a supported complete
coarse history, one of its positive policy actions, and its exact trace
support. The row-law weights are never replaced by a training distribution. -/
theorem mem_deploymentRowLaw_support_iff
    {X Y A : Type u} [Fintype X] [Fintype A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (n : ℕ) (x : X) (a : A) :
    (x, a) ∈ (coverageDeploymentRowLaw p₀ q P π n).support ↔
      ∃ g ∈ (coarseLaw p₀ q P π n).support,
        a ∈ (π n g).support ∧ x ∈ traceSupport p₀ q P n g := by
  change (x, a) ∈ ((pmfExtend (microLaw p₀ q P π n)
    (fun h => π n (projectHistory q n h))).map
      (fun ha => (riskLastState n ha.1, ha.2))).support ↔ _
  constructor
  · intro hrow
    obtain ⟨⟨h, b⟩, hh, heq⟩ := (PMF.mem_support_map_iff _ _ (x, a)).mp hrow
    have hlast : riskLastState n h = x := congrArg Prod.fst heq
    have hb : b = a := congrArg Prod.snd heq
    subst b
    have hs := (mem_pmfExtend_support_iff (microLaw p₀ q P π n)
      (fun h => π n (projectHistory q n h)) h a).mp hh
    have hg : projectHistory q n h ∈ (coarseLaw p₀ q P π n).support :=
      (PMF.mem_support_map_iff (projectHistory q n) (microLaw p₀ q P π n) _).mpr
        ⟨h, hs.1, rfl⟩
    refine ⟨projectHistory q n h, hg, hs.2, ?_⟩
    exact (mem_traceSupport_iff_realized p₀ q P π n _ hg x).mpr
      ⟨h, hs.1, rfl, hlast⟩
  · rintro ⟨g, hg, ha, hx⟩
    obtain ⟨h, hh, hf, hlast⟩ := (mem_traceSupport_iff_realized p₀ q P π n g hg x).mp hx
    apply (PMF.mem_support_map_iff _ _ (x, a)).mpr
    refine ⟨(h, a), ?_, ?_⟩
    · apply (mem_pmfExtend_support_iff (microLaw p₀ q P π n)
        (fun h => π n (projectHistory q n h)) h a).mpr
      exact ⟨hh, by simpa only [hf] using ha⟩
    · change (riskLastState n h, a) = (x, a)
      rw [hlast]


end
end SupportViabilityClosure
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace SupportViabilityClosure

open MeasureTheory
open scoped BigOperators

/-- Zero uncertified mass is exactly certification of every genuinely
supported state. Finiteness is used only for the existing real event sum. -/
theorem zero_uncertified_mass_iff_support
    {S : Type*} [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (ν : PMF S) (C : S → Prop) :
    ν.toMeasure.real {s | ¬ C s} = 0 ↔ ∀ s ∈ ν.support, C s := by
  classical
  rw [← coverage_uncovered_indicator_expectation ν C]
  constructor
  · intro hsum s hs
    by_contra hC
    have hnonneg : ∀ x ∈ (Finset.univ : Finset S),
        0 ≤ (ν x).toReal * (if C x then (0 : ℝ) else 1) := by
      intro x _
      split_ifs <;> positivity
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum s
      (Finset.mem_univ s)
    simp only [if_neg hC, mul_one] at hz
    rcases (ENNReal.toReal_eq_zero_iff (ν s)).mp hz with hzero | htop
    · exact ((PMF.mem_support_iff ν s).mp hs) hzero
    · exact (PMF.apply_ne_top ν s) htop
  · intro hcert
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s ∈ ν.support
    · simp [hcert s hs]
    · have hz : ν s = 0 := by
        by_contra hn
        exact hs ((PMF.mem_support_iff ν s).mpr hn)
      simp [hz]


end SupportViabilityClosure
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace SupportViabilityClosure

open MeasureTheory UEOT.V3.PathError

universe u

/-- Zero actual uncertified occupancy is equivalent to certifying every
state in every supported coarse-history trace under each positive action
of that same deployed policy. Null histories and zero-probability actions
make no contribution and impose no certification requirements. -/
theorem zero_uncovered_iff_support_certified
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop) (n : ℕ) :
    (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} = 0 ↔
      ∀ g ∈ (coarseLaw p₀ q P π n).support,
        ∀ a ∈ (π n g).support,
          ∀ x ∈ traceSupport p₀ q P n g, certified n x a := by
  rw [zero_uncertified_mass_iff_support]
  constructor
  · intro hcert g hg a ha x hx
    exact hcert (x, a)
      ((mem_deploymentRowLaw_support_iff p₀ q P π n x a).mpr ⟨g, hg, ha, hx⟩)
  · intro hcert xa hxa
    obtain ⟨g, hg, ha, hx⟩ :=
      (mem_deploymentRowLaw_support_iff p₀ q P π n xa.1 xa.2).mp hxa
    exact hcert g hg xa.2 ha xa.1 hx


end SupportViabilityClosure
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace SupportViabilityClosure

universe u

/-- Backward finite viability for a current uncertainty set. There is no
terminal state constraint because the target counts transition-row
certification only before the horizon. -/
def viableWith
    {X Y A : Type u}
    (next : ℕ → Set X → A → Y → Set X)
    (certified : ℕ → X → A → Prop) : ℕ → ℕ → Set X → Prop
  | _, 0, _ => True
  | n, k + 1, S =>
      ∃ a : A,
        (∀ x ∈ S, certified n x a) ∧
          ∀ y : Y, (next n S a y).Nonempty →
            viableWith next certified (n + 1) k (next n S a y)

/-- The first viable step when an absolute finite horizon has not yet been
reached. This only converts remaining-horizon arithmetic. -/
theorem viableWith_step_of_lt
    {X Y A : Type u}
    (next : ℕ → Set X → A → Y → Set X)
    (certified : ℕ → X → A → Prop)
    {n T : ℕ} {S : Set X} (hn : n < T)
    (hV : viableWith next certified n (T - n) S) :
    ∃ a : A,
      (∀ x ∈ S, certified n x a) ∧
        ∀ y : Y, (next n S a y).Nonempty →
          viableWith next certified (n + 1) (T - (n + 1))
            (next n S a y) := by
  have hremaining : T - n = (T - (n + 1)) + 1 := by omega
  rw [hremaining] at hV
  exact hV

end SupportViabilityClosure
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace SupportViabilityClosure

open MeasureTheory UEOT.V3.PathError
open scoped Classical

universe u

noncomputable section

/-- The abstract recursion instantiated by the actual PMF support successor. -/
abbrev Viable
    {X Y A : Type u} (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop) : ℕ → ℕ → Set X → Prop :=
  viableWith (successorSupport q P) certified

/-- A full coarse-history policy synthesized from remaining viability.
The source-support recursion is policy-independent. Nonviable histories
and times after the horizon use the supplied full fallback. Values at null
histories do not affect the actual-law theorem. -/
def viablePolicy
    {X Y A : Type u}
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop) (T : ℕ)
    (πbase : ∀ n, CausalHistory Y (A × Y) n → PMF A) :
    ∀ n, CausalHistory Y (A × Y) n → PMF A :=
  fun n h =>
    if hn : n < T then
      if hV : Viable q P certified n (T - n) (traceSupport p₀ q P n h) then
        PMF.pure (Classical.choose
          (viableWith_step_of_lt (successorSupport q P) certified hn hV))
      else πbase n h
    else πbase n h

/-- Every positive-probability action of the synthesized policy at a viable
history certifies the entire current support and preserves viability of
every nonempty observation-successor support. -/
theorem viablePolicy_support_step
    {X Y A : Type u}
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop) (T : ℕ)
    (πbase : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (n : ℕ) (h : CausalHistory Y (A × Y) n) (a : A)
    (hn : n < T)
    (hV : Viable q P certified n (T - n) (traceSupport p₀ q P n h))
    (ha : a ∈ (viablePolicy p₀ q P certified T πbase n h).support) :
    (∀ x ∈ traceSupport p₀ q P n h, certified n x a) ∧
      ∀ y : Y,
        (successorSupport q P n (traceSupport p₀ q P n h) a y).Nonempty →
          Viable q P certified (n + 1) (T - (n + 1))
            (successorSupport q P n (traceSupport p₀ q P n h) a y) := by
  let hstep := viableWith_step_of_lt (successorSupport q P) certified hn hV
  let chosen : A := Classical.choose hstep
  have hpure : viablePolicy p₀ q P certified T πbase n h = PMF.pure chosen := by
    simp only [viablePolicy, dif_pos hn, dif_pos hV, chosen]
  have haeq : a = chosen := by
    have hnonzero : (viablePolicy p₀ q P certified T πbase n h) a ≠ 0 :=
      (PMF.mem_support_iff _ _).mp ha
    rw [hpure] at hnonzero
    by_contra hne
    apply hnonzero
    simp [PMF.pure_apply]
    exact hne
  rw [haeq]
  exact Classical.choose_spec hstep

/-- The initial backward certificate is preserved along every actually
supported coarse history under this one synthesized policy. -/
theorem viablePolicy_supported_histories_viable
    {X Y A : Type u} [Fintype X] [Fintype A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop) (T : ℕ)
    (πbase : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (hinit : ∀ y : Y, (initialSupport p₀ q y).Nonempty →
      Viable q P certified 0 T (initialSupport p₀ q y)) :
    ∀ n, n ≤ T →
      ∀ h ∈ (coarseLaw p₀ q P (viablePolicy p₀ q P certified T πbase) n).support,
        Viable q P certified n (T - n) (traceSupport p₀ q P n h) := by
  intro n
  induction n with
  | zero =>
      intro _ h hh
      have hbase := hinit h
        ((mem_coarseLaw_zero_support_iff
          p₀ q P (viablePolicy p₀ q P certified T πbase) h).mp hh)
      simpa only [Nat.sub_zero, traceSupport] using hbase
  | succ n ih =>
      intro hn hc hh
      rcases hc with ⟨h, a, y⟩
      have hparts := (mem_coarseLaw_succ_support_iff
        p₀ q P (viablePolicy p₀ q P certified T πbase) n h a y).mp hh
      have hV := ih (by omega) h hparts.1
      have hstep := viablePolicy_support_step
        p₀ q P certified T πbase n h a (by omega) hV hparts.2.1
      change Viable q P certified (n + 1) (T - (n + 1))
        (successorSupport q P n (traceSupport p₀ q P n h) a y)
      exact hstep.2 y hparts.2.2

/-- Initial support viability produces zero actual uncertified-row
occupancy at every transition before the horizon. -/
theorem viablePolicy_zero_uncovered
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop) (T : ℕ)
    (πbase : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (hinit : ∀ y : Y, (initialSupport p₀ q y).Nonempty →
      Viable q P certified 0 T (initialSupport p₀ q y)) :
    ∀ n, n < T →
      (coverageDeploymentRowLaw p₀ q P
        (viablePolicy p₀ q P certified T πbase) n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2} = 0 := by
  intro n hn
  apply (zero_uncovered_iff_support_certified
    p₀ q P (viablePolicy p₀ q P certified T πbase) certified n).mpr
  intro h hh a ha x hx
  have hV := viablePolicy_supported_histories_viable
    p₀ q P certified T πbase hinit n (Nat.le_of_lt hn) h hh
  exact (viablePolicy_support_step
    p₀ q P certified T πbase n h a hn hV ha).1 x hx

/-- Conversely, any randomized full policy with zero actual uncertified
occupancy forces backward viability on every actual supported coarse
history. A positive action is chosen only from that same policy's support. -/
theorem supported_viable_of_zero_uncovered
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop) (T : ℕ)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (hzero : ∀ n, n < T →
      (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} = 0) :
    ∀ k n, n + k ≤ T →
      ∀ h ∈ (coarseLaw p₀ q P π n).support,
        Viable q P certified n k (traceSupport p₀ q P n h) := by
  intro k
  induction k with
  | zero =>
      intro n _ h _
      trivial
  | succ k ih =>
      intro n hnk h hh
      obtain ⟨a, ha⟩ := (π n h).support_nonempty
      have hcert := (zero_uncovered_iff_support_certified
        p₀ q P π certified n).mp (hzero n (by omega)) h hh a ha
      refine ⟨a, hcert, ?_⟩
      intro y hnext
      have hhnext : (h, (a, y)) ∈ (coarseLaw p₀ q P π (n + 1)).support :=
        (mem_coarseLaw_succ_support_iff p₀ q P π n h a y).mpr
          ⟨hh, ha, hnext⟩
      have hV := ih (n + 1) (by omega) (h, (a, y)) hhnext
      exact hV

/-- Exact finite-horizon characterization, with a full fallback policy
explicitly retained. No strong all-covered-prefix Extend premise occurs. -/
theorem initial_viability_iff_exists_zero_uncovered_policy
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop) (T : ℕ)
    (πbase : ∀ n, CausalHistory Y (A × Y) n → PMF A) :
    (∀ y : Y, (initialSupport p₀ q y).Nonempty →
      Viable q P certified 0 T (initialSupport p₀ q y)) ↔
    ∃ π : ∀ n, CausalHistory Y (A × Y) n → PMF A,
      ∀ n, n < T →
        (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2} = 0 := by
  constructor
  · intro hinit
    exact ⟨viablePolicy p₀ q P certified T πbase,
      viablePolicy_zero_uncovered p₀ q P certified T πbase hinit⟩
  · rintro ⟨π, hzero⟩ y hy
    have hh : y ∈ (coarseLaw p₀ q P π 0).support :=
      (mem_coarseLaw_zero_support_iff p₀ q P π y).mpr hy
    have hV := supported_viable_of_zero_uncovered
      p₀ q P certified T π hzero T 0 (by omega) y hh
    exact hV


end
end SupportViabilityClosure
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
