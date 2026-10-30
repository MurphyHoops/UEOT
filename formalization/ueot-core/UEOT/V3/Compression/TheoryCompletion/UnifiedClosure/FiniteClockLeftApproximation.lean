import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPartitionLeftInputs

/-!
Original commitment: SAME-source full-input QV needs proved actual START approximation, not arbitrary sampling or a different output.
Existing result: original scalar caller-clock proof has pure finite-cell/left-limit facts tied to its source types.
Premise reduced: expose only necessary pure clock facts for arbitrary value space; stochastic past/source permissions remain separate caller obligations.
Model: deterministic finite monotone0/T clocks with COMPUTED mesh→0, repeated clocks/T0, native Ioc left values and no new World/source.
Consumer: old scalar and actual joint-vector START records; this helper transports no coefficients between stochastic filtrations.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteClockLeftApproximation
open Set Filter
open BrownianQuadraticVariation (mesh)
open scoped NNReal Topology
noncomputable section

/-- Actual native finite-cell search, no oracle partition cell is a premise. -/
theorem exists_clock_cell {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (x : ℝ)
    (hx0 : (τ 0 : ℝ)<x) (hxT : x≤(τ (Fin.last n) : ℝ)) :
    ∃ i : Fin n,x∈Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ) := by
  classical
  let q : Fin (n+1)→Prop := fun j=>x≤(τ j : ℝ)
  have hex : ∃ j,q j := ⟨Fin.last n,hxT⟩
  let j:=Fin.find q hex
  have hpos : 0<(j : ℕ) := by
    by_contra hn
    have hj : j=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    have hq : q j := Fin.find_spec hex
    change x≤(τ j : ℝ) at hq
    rw [hj] at hq
    exact (not_le_of_gt hx0) hq
  let i : Fin n:=⟨(j : ℕ)-1,by have := j.is_lt; omega⟩
  have his : i.succ=j := Fin.ext (by simp only [i,Fin.val_succ]; omega)
  have hij : i.castSucc<j := by
    change (i : ℕ)<(j : ℕ)
    simp only [i]
    omega
  refine ⟨i,lt_of_not_ge (Fin.find_min hex hij),?_⟩
  rw [his]
  exact Fin.find_spec hex

/-- Exact positive-real/NNReal endpoint conversion for the original Ioc
convention, valid also when the real argument is negative. -/
theorem toNNReal_mem_Ioc (a b : ℝ≥0) (x : ℝ) :
    Real.toNNReal x∈Ioc a b ↔ x∈Ioc (a : ℝ) (b : ℝ) := by
  have hl : a<Real.toNNReal x ↔ (a : ℝ)<x := by
    simpa only [not_le] using (Real.toNNReal_le_iff_le_coe (r:=x) (p:=a)).not
  simp only [mem_Ioc,hl,Real.toNNReal_le_iff_le_coe]

/-- The original Ioc endpoint convention is left-continuous for an arbitrary
constant value; no temporal smoothing or extra signal regularity is inserted. -/
theorem Ioc_indicator_left {E : Type*} [Zero E] [TopologicalSpace E]
    (c : E) (a b u : ℝ≥0) :
    ContinuousWithinAt ((Ioc a b).indicator (fun _=>c)) (Iic u) u := by
  by_cases hua : u≤a
  · have hz : (Ioc a b).indicator (fun _=>c) u=0 :=
      Set.indicator_of_notMem (fun h=>(not_lt_of_ge hua) h.1) _
    have he : ∀ᶠ v in 𝓝[Iic u] u,(Ioc a b).indicator (fun _=>c) v=0 := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact Set.indicator_of_notMem (fun h=>(not_lt_of_ge (hv.trans hua)) h.1) _
    change Tendsto _ (𝓝[Iic u] u) (𝓝 ((Ioc a b).indicator (fun _=>c) u))
    rw [hz]
    exact (tendsto_congr' he).mpr tendsto_const_nhds
  · have hau : a<u := lt_of_not_ge hua
    by_cases hub : u≤b
    · have hu : (Ioc a b).indicator (fun _=>c) u=c := Set.indicator_of_mem (show u∈Ioc a b from ⟨hau,hub⟩) _
      have he : ∀ᶠ v in 𝓝[Iic u] u,(Ioc a b).indicator (fun _=>c) v=c := by
        filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Ioi_mem_nhds hau)] with v hv hva
        exact Set.indicator_of_mem (show v∈Ioc a b from ⟨hva,hv.trans hub⟩) _
      change Tendsto _ (𝓝[Iic u] u) (𝓝 ((Ioc a b).indicator (fun _=>c) u))
      rw [hu]
      exact (tendsto_congr' he).mpr tendsto_const_nhds
    · have hbu : b<u := lt_of_not_ge hub
      have hz : (Ioc a b).indicator (fun _=>c) u=0 :=
        Set.indicator_of_notMem (fun h=>(not_le_of_gt hbu) h.2) _
      have he : ∀ᶠ v in 𝓝[Iic u] u,(Ioc a b).indicator (fun _=>c) v=0 := by
        filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hbu)] with v hv
        exact Set.indicator_of_notMem (fun h=>(not_le_of_gt hv) h.2) _
      change Tendsto _ (𝓝[Iic u] u) (𝓝 ((Ioc a b).indicator (fun _=>c) u))
      rw [hz]
      exact (tendsto_congr' he).mpr tendsto_const_nhds

/-- Literal left sample in arbitrary additive value space, zero off cells. -/
def leftSample {E : Type*} [AddCommMonoid E] {n : ℕ} (τ : Fin (n+1)→ℝ≥0)
    (F : ℝ≥0→E) (x : ℝ) : E :=
  ∑ i : Fin n,(Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator (fun _=>F (τ i.castSucc)) x

theorem leftSample_eq_cell {E : Type*} [AddCommMonoid E] {n : ℕ}
    (τ : Fin (n+1)→ℝ≥0) (hτ : Monotone τ) (F : ℝ≥0→E) (x : ℝ) (i : Fin n)
    (hi : x∈Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)) : leftSample τ F x=F (τ i.castSucc) := by
  rw [leftSample,Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hi _
  · intro j _ hji
    have hj : x∉Ioc (τ j.castSucc : ℝ) (τ j.succ : ℝ) := by
      intro hj
      rcases lt_or_gt_of_ne hji with h | h
      · have hc : (τ j.succ : ℝ)≤(τ i.castSucc : ℝ) := by
          exact_mod_cast hτ (show j.succ≤ i.castSucc by exact_mod_cast Nat.succ_le_of_lt h)
        exact (not_lt_of_ge (hj.2.trans hc)) hi.1
      · have hc : (τ i.succ : ℝ)≤(τ j.castSucc : ℝ) := by
          exact_mod_cast hτ (show i.succ≤j.castSucc by exact_mod_cast Nat.succ_le_of_lt h)
        exact (not_lt_of_ge (hi.2.trans hc)) hj.1
    exact Set.indicator_of_notMem hj _
  · simp

/-- Pure same-value-space START convergence at an actual positive source time.
No source AE/filtration law is asserted by this deterministic clock lemma. -/
theorem leftSample_tendsto {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (T : ℝ≥0) (N : ℕ→ℕ) (τ : (m : ℕ)→Fin (N m+1)→ℝ≥0)
    (hmono : ∀ m,Monotone (τ m)) (hzero : ∀ m,τ m 0=0) (hend : ∀ m,τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m=>(mesh (τ m) : ℝ)) atTop (𝓝 0))
    (F : ℝ≥0→E) (x : ℝ) (hx0 : 0<x) (hxT : x≤(T : ℝ))
    (hleft : ContinuousWithinAt F (Iic (Real.toNNReal x)) (Real.toNNReal x)) :
    Tendsto (fun m=>leftSample (τ m) F x) atTop (𝓝 (F (Real.toNNReal x))) := by
  have he (m : ℕ) : ∃ i : Fin (N m),x∈Ioc (τ m i.castSucc : ℝ) (τ m i.succ : ℝ) :=
    exists_clock_cell (τ m) x (by simpa only [hzero,NNReal.coe_zero] using hx0) (by simpa only [hend] using hxT)
  choose i hi using he
  have happ : Tendsto (fun m=>τ m (i m).castSucc) atTop (𝓝 (Real.toNNReal x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _=>dist_nonneg) (fun m=>?_) hmesh
    have hgap : (τ m (i m).succ : ℝ)-(τ m (i m).castSucc : ℝ)≤(mesh (τ m) : ℝ) := by
      have hm:=Finset.le_sup (f:=fun j : Fin (N m)=>τ m j.succ-τ m j.castSucc) (Finset.mem_univ (i m))
      have hc:=NNReal.coe_le_coe.mpr hm
      rw [NNReal.coe_sub ((hmono m) (show (i m).castSucc≤(i m).succ by exact_mod_cast Nat.le_succ (i m : ℕ)))] at hc
      exact hc
    rw [NNReal.dist_eq,Real.coe_toNNReal _ hx0.le,abs_of_nonpos (sub_nonpos.mpr (hi m).1.le)]
    linarith [(hi m).2]
  have hw : Tendsto (fun m=>τ m (i m).castSucc) atTop (𝓝[Iic (Real.toNNReal x)] (Real.toNNReal x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨happ,Eventually.of_forall (fun m=>?_)⟩
    change τ m (i m).castSucc≤Real.toNNReal x
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hx0.le]
    exact (hi m).1.le
  exact (tendsto_congr' (Eventually.of_forall (fun m=>leftSample_eq_cell (τ m) (hmono m) F x (i m) (hi m)))).mpr
    (hleft.tendsto.comp hw)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteClockLeftApproximation
