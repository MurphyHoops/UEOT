import Mathlib.Dynamics.OmegaLimit
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Bases
import Mathlib.Topology.Sequences

/-!
# P-PER-01 foundation — omega-limit persistence core

This module formalizes the persistence theorem used by Core 3.  The generic
filter-level lemmas establish nonemptiness, compactness, persistence-domain
containment, and forward invariance.  The final `NNReal` theorem proves the
missing reverse inclusion without introducing negative time or a right inverse:
for a precompact one-sided orbit, every omega-limit point has a shifted
precompact subsequence whose limit is a predecessor inside the same omega-limit.
-/

namespace UEOT.V3.PersistenceOmega

open Set Function Filter Topology
open omegaLimit
open scoped NNReal

universe uT uX

variable {τ : Type uT} {X : Type uX}
variable [TopologicalSpace τ] [AddMonoid τ]
variable [TopologicalSpace X] [T2Space X]

/-- If one tail closure of a trajectory is contained in a compact set, the
omega-limit is compact. -/
theorem isCompact_omegaLimit_of_compact_tail
    (f : Filter τ) (φ : Flow τ X) (x : X)
    {K : Set X} (hK : IsCompact K)
    (habs : ∃ v ∈ f,
      closure (image2 φ v ({x} : Set X)) ⊆ K) :
    IsCompact (ω f φ ({x} : Set X)) := by
  rcases habs with ⟨v, hv, hsub⟩
  exact hK.of_isClosed_subset
    (isClosed_omegaLimit f φ ({x} : Set X))
    ((omegaLimit_subset_closure_image2 f φ ({x} : Set X) hv).trans hsub)

/-- Eventual residence in a closed persistence domain forces the omega-limit
to lie in that domain. -/
theorem omegaLimit_subset_closed_of_eventually_mem
    (f : Filter τ) (φ : Flow τ X) (x : X)
    {V : Set X} (hV : IsClosed V)
    (hstay : ∀ᶠ t in f, φ t x ∈ V) :
    ω f φ ({x} : Set X) ⊆ V := by
  let v : Set τ := {t | φ t x ∈ V}
  have hv : v ∈ f := hstay
  refine (omegaLimit_subset_closure_image2 f φ ({x} : Set X) hv).trans ?_
  apply closure_minimal
  · rintro y ⟨t, ht, z, hz, rfl⟩
    simp only [mem_singleton_iff] at hz
    subst z
    exact ht
  · exact hV

/-- Machine-checked filter-level persistence core behind P-PER-01. -/
theorem omegaLimit_persistence_core
    (f : Filter τ) [NeBot f]
    (φ : Flow τ X) (x : X)
    {V K : Set X}
    (hV : IsClosed V)
    (hstay : ∀ᶠ t in f, φ t x ∈ V)
    (hK : IsCompact K)
    (habs : ∃ v ∈ f,
      closure (image2 φ v ({x} : Set X)) ⊆ K)
    (htrans : ∀ s : τ, Tendsto (s + ·) f f) :
    (ω f φ ({x} : Set X)).Nonempty ∧
      IsCompact (ω f φ ({x} : Set X)) ∧
      ω f φ ({x} : Set X) ⊆ V ∧
      IsInvariant φ (ω f φ ({x} : Set X)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact nonempty_omegaLimit_of_isCompact_absorbing
      f φ ({x} : Set X) hK habs (singleton_nonempty x)
  · exact isCompact_omegaLimit_of_compact_tail f φ x hK habs
  · exact omegaLimit_subset_closed_of_eventually_mem f φ x hV hstay
  · exact Flow.isInvariant_omegaLimit f φ ({x} : Set X) htrans

section NNRealSemiflow

variable [FirstCountableTopology X]

private theorem nnreal_add_left_tendsto_atTop (s : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => s + t) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop b] with t ht
  exact ht.trans (le_add_left le_rfl)

private theorem nnreal_tsub_tendsto_atTop
    {t : ℕ → ℝ≥0} (ht : Tendsto t atTop atTop) (s : ℝ≥0) :
    Tendsto (fun n => t n - s) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  exact (tendsto_atTop.1 ht (b + s)).mono fun _n hn =>
    le_tsub_of_add_le_right hn

/-- Exact invariance of the omega-limit for a genuinely one-sided continuous
semiflow.  The reverse inclusion is obtained by shifting a sequence of times
`tₙ → ∞` by `s`, extracting a convergent subsequence from the precompact
orbit, and passing the semiflow identity through the limit. -/
theorem image_omegaLimit_eq_of_precompact_orbit
    (φ : Flow ℝ≥0 X) (x : X)
    (hpre : IsCompact (closure (range fun t : ℝ≥0 => φ t x)))
    (s : ℝ≥0) :
    φ s '' ω (atTop : Filter ℝ≥0) φ ({x} : Set X) =
      ω (atTop : Filter ℝ≥0) φ ({x} : Set X) := by
  apply Subset.antisymm
  · have htrans : ∀ r : ℝ≥0,
        Tendsto (r + ·) (atTop : Filter ℝ≥0) atTop := fun r =>
      nnreal_add_left_tendsto_atTop r
    exact mapsTo_iff_image_subset.mp
      ((Flow.isInvariant_omegaLimit (atTop : Filter ℝ≥0)
        φ ({x} : Set X) htrans) s)
  · intro y hy
    have hcluster :
        MapClusterPt y (atTop : Filter ℝ≥0) (fun t : ℝ≥0 => φ t x) :=
      (mem_omegaLimit_singleton_iff_mapClusterPt
        (atTop : Filter ℝ≥0) φ x y).1 hy
    obtain ⟨t, hty, htTop⟩ := hcluster.exists_seq_tendsto
    have huTop : Tendsto (fun n => t n - s) atTop (atTop : Filter ℝ≥0) :=
      nnreal_tsub_tendsto_atTop htTop s
    have hmem : ∀ n : ℕ,
        φ (t n - s) x ∈ closure (range fun r : ℝ≥0 => φ r x) := by
      intro n
      exact subset_closure ⟨t n - s, rfl⟩
    obtain ⟨z, hzpre, q, hqmono, hqz⟩ := hpre.isSeqCompact hmem
    have hqTop : Tendsto q atTop atTop := hqmono.tendsto_atTop
    have huqTop : Tendsto (fun n => t (q n) - s) atTop (atTop : Filter ℝ≥0) := by
      simpa [Function.comp_def] using huTop.comp hqTop
    have hzcluster :
        MapClusterPt z (atTop : Filter ℝ≥0) (fun r : ℝ≥0 => φ r x) := by
      apply MapClusterPt.of_comp huqTop
      simpa [Function.comp_def] using hqz.mapClusterPt
    have hzomega : z ∈ ω (atTop : Filter ℝ≥0) φ ({x} : Set X) :=
      (mem_omegaLimit_singleton_iff_mapClusterPt
        (atTop : Filter ℝ≥0) φ x z).2 hzcluster
    have htqTop : Tendsto (fun n => t (q n)) atTop (atTop : Filter ℝ≥0) := by
      simpa [Function.comp_def] using htTop.comp hqTop
    have hge : ∀ᶠ n in atTop, s ≤ t (q n) :=
      tendsto_atTop.1 htqTop s
    have heq :
        (fun n => φ s (φ (t (q n) - s) x)) =ᶠ[atTop]
          (fun n => φ (t (q n)) x) := by
      filter_upwards [hge] with n hn
      rw [← φ.map_add, add_tsub_cancel_of_le hn]
    have hleft : Tendsto (fun n => φ s (φ (t (q n) - s) x))
        atTop (𝓝 (φ s z)) := by
      have hcont : Tendsto (φ s) (𝓝 z) (𝓝 (φ s z)) :=
        (φ.continuous_toFun s).tendsto z
      simpa [Function.comp_def] using hcont.comp hqz
    have hright : Tendsto (fun n => φ (t (q n)) x) atTop (𝓝 y) := by
      simpa [Function.comp_def] using hty.comp hqTop
    have hleftY : Tendsto (fun n => φ s (φ (t (q n) - s) x)) atTop (𝓝 y) :=
      Tendsto.congr' heq.symm hright
    have hsy : φ s z = y := tendsto_nhds_unique hleft hleftY
    exact ⟨z, hzomega, hsy⟩

/-- Source-facing P-PER-01 theorem for nonnegative time: a precompact orbit
that is eventually contained in a closed persistence domain has a nonempty,
compact omega-limit inside that domain, and every nonnegative time map sends
that omega-limit onto itself. -/
theorem p_per_01
    (φ : Flow ℝ≥0 X) (x : X)
    {V : Set X}
    (hV : IsClosed V)
    (hstay : ∀ᶠ t in (atTop : Filter ℝ≥0), φ t x ∈ V)
    (hpre : IsCompact (closure (range fun t : ℝ≥0 => φ t x))) :
    (ω (atTop : Filter ℝ≥0) φ ({x} : Set X)).Nonempty ∧
      IsCompact (ω (atTop : Filter ℝ≥0) φ ({x} : Set X)) ∧
      ω (atTop : Filter ℝ≥0) φ ({x} : Set X) ⊆ V ∧
      ∀ s : ℝ≥0,
        φ s '' ω (atTop : Filter ℝ≥0) φ ({x} : Set X) =
          ω (atTop : Filter ℝ≥0) φ ({x} : Set X) := by
  have htrans : ∀ r : ℝ≥0,
      Tendsto (r + ·) (atTop : Filter ℝ≥0) atTop := fun r =>
    nnreal_add_left_tendsto_atTop r
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0),
      closure (image2 φ v ({x} : Set X)) ⊆
        closure (range fun t : ℝ≥0 => φ t x) := by
    refine ⟨Set.univ, univ_mem, ?_⟩
    apply closure_mono
    rintro y ⟨t, _ht, z, hz, rfl⟩
    simp only [mem_singleton_iff] at hz
    subst z
    exact ⟨t, rfl⟩
  have hcore := omegaLimit_persistence_core
    (atTop : Filter ℝ≥0) φ x hV hstay hpre habs htrans
  exact ⟨hcore.1, hcore.2.1, hcore.2.2.1,
    fun s => image_omegaLimit_eq_of_precompact_orbit φ x hpre s⟩

end NNRealSemiflow

end UEOT.V3.PersistenceOmega
