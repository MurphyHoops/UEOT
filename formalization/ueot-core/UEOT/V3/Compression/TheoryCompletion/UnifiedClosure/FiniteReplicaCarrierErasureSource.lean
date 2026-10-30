import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteResponseCarrierFrontier
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.WithBot

/-!
Original commitment: book31.2 requires actual source-derived carriers/cuts and a justified physical-frame consumer, not an oracle hypergraph.
Existing result: table-derived executable frontier is exactly original Access.minimalCarriers and its computed blocker.
Premise reduced: derive replica edges, all minimal outputs, full support and erasure-frame identities from an explicit response source.
Model: NEW finite snapshot/erasure source Option(Fin m) with two atoms per coordinate, no repair/supply/old Register or C5 intervention rights.
Consumer: same-source executable decoder, original blocker erasure theorem, and strict explicit-output exponential boundary; no generic polynomial claim.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteReplicaCarrierErasureSource
open UEOT
open scoped ENNReal
open FiniteResponseCarrierFrontier

abbrev Row (m : ℕ) := Option (Fin m)
abbrev Atom (m : ℕ) := Fin m × Bool

instance rowOrder (m : ℕ) : LinearOrder (Row m) :=
  inferInstanceAs (LinearOrder (WithBot (Fin m)))

def target {m : ℕ} : Row m → Bool | none => false | some _ => true

def obs {m : ℕ} : Row m → Atom m → Bool
  | none, _ => false
  | some i, (j,_) => decide (i=j)

def pair {m : ℕ} (i : Fin m) : Finset (Atom m) := {(i,false),(i,true)}

@[simp] theorem mem_pair {m : ℕ} (i : Fin m) (v : Atom m) : v ∈ pair i ↔ v.1=i := by
  rcases v with ⟨j,b⟩
  cases b <;> simp [pair,Prod.ext_iff,eq_comm]

/-- The hyperedge is derived by comparing actual table entries. -/
theorem actual_difference {m : ℕ} (i : Fin m) : differenceEdge obs none (some i)=pair i := by
  ext v
  simp [differenceEdge,obs,eq_comm]

theorem actual_edge_family (m : ℕ) (E : Finset (Atom m)) :
    E ∈ distinguishingEdges obs target ↔ ∃ i : Fin m, E=pair i := by
  rw [mem_distinguishingEdges]
  constructor
  · rintro ⟨x,y,hxy,he⟩
    cases x with
    | none =>
      cases y with
      | none => exact False.elim (hxy rfl)
      | some i => exact ⟨i,he.symm.trans (actual_difference i)⟩
    | some i =>
      cases y with
      | some j => exact False.elim (hxy rfl)
      | none =>
        refine ⟨i,he.symm.trans ?_⟩
        ext v
        simp [differenceEdge,obs,eq_comm]
  · rintro ⟨i,rfl⟩
    exact ⟨none,some i,by simp [target],actual_difference i⟩

/-- All rows have positive source mass, including the baseline. -/
noncomputable def source (m : ℕ) : PMF (Row m) := PMF.uniformOfFintype _

theorem source_full_support (m : ℕ) (x : Row m) : x ∈ (source m).support :=
  PMF.mem_support_uniformOfFintype x

theorem source_positive (m : ℕ) (x : Row m) : 0 < source m x :=
  pos_iff_ne_zero.mpr ((source m).mem_support_iff x |>.mp (source_full_support m x))

theorem source_mass (m : ℕ) (x : Row m) : source m x=((m+1 : ℕ) : ℝ≥0∞)⁻¹ := by
  simp [source,PMF.uniformOfFintype_apply,Fintype.card_option]

theorem table_dimensions (m : ℕ) : Fintype.card (Row m)=m+1 ∧ Fintype.card (Atom m)=2*m := by
  simp [Fintype.card_option,Fintype.card_prod,Nat.mul_comm]

/-- Exact distinguishing access condition, DERIVED from the actual table. -/
theorem sufficient_iff_pair {m : ℕ} (S : Finset (Atom m)) :
    Access.Sufficient obs target S ↔ ∀ i, (i,false) ∈ S ∨ (i,true) ∈ S := by
  constructor
  · intro hs i
    by_contra h
    push Not at h
    have ha : Access.AgreeOn obs S none (some i) := by
      intro v hv
      rcases v with ⟨j,b⟩
      have hji : j≠i := by
        intro he
        subst j
        cases b
        · exact h.1 hv
        · exact h.2 hv
      simp [obs,Ne.symm hji]
    have hh := hs none (some i) ha
    simp [target] at hh
  · intro h x y ha
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some i =>
        obtain hi | hi := h i
        · have hh := ha (i,false) hi; simp [obs] at hh
        · have hh := ha (i,true) hi; simp [obs] at hh
    | some i =>
      cases y with
      | some j => rfl
      | none =>
        obtain hi | hi := h i
        · have hh := ha (i,false) hi; simp [obs] at hh
        · have hh := ha (i,true) hi; simp [obs] at hh

def choiceCarrier {m : ℕ} (f : Fin m → Bool) : Finset (Atom m) :=
  Finset.univ.image (fun i => (i,f i))

@[simp] theorem mem_choiceCarrier {m : ℕ} (f : Fin m → Bool) (i : Fin m) (b : Bool) :
    (i,b) ∈ choiceCarrier f ↔ b=f i := by simp [choiceCarrier,eq_comm]

theorem choice_sufficient {m : ℕ} (f : Fin m → Bool) : Access.Sufficient obs target (choiceCarrier f) := by
  apply (sufficient_iff_pair _).mpr
  intro i
  cases h : f i <;> simp [h]

theorem choice_minimal {m : ℕ} (f : Fin m → Bool) :
    Finite.Minimal (Access.Sufficient obs target) (choiceCarrier f) := by
  refine ⟨choice_sufficient f,?_⟩
  intro T hT hs
  apply Finset.Subset.antisymm hT
  intro v hv
  rcases v with ⟨i,b⟩
  have hb : b=f i := (mem_choiceCarrier f i b).mp hv
  obtain hi | hi := (sufficient_iff_pair _).mp hs i
  · have he : false=f i := (mem_choiceCarrier f i false).mp (hT hi)
    have hh : b=false := hb.trans he.symm
    simpa only [hh] using hi
  · have he : true=f i := (mem_choiceCarrier f i true).mp (hT hi)
    have hh : b=true := hb.trans he.symm
    simpa only [hh] using hi

/-- A minimal carrier has exactly one physical copy from every pair. -/
theorem minimal_iff_choice {m : ℕ} (S : Finset (Atom m)) :
    S ∈ Access.minimalCarriers obs target ↔ ∃ f : Fin m → Bool, choiceCarrier f=S := by
  constructor
  · intro hs
    let f : Fin m → Bool := fun i => if (i,false) ∈ S then false else true
    have hsub : choiceCarrier f ⊆ S := by
      intro v hv
      rcases v with ⟨i,b⟩
      have hb : b=f i := (mem_choiceCarrier f i b).mp hv
      subst b
      obtain hi | hi := (sufficient_iff_pair _).mp hs.1 i
      · simp [f,hi]
      · by_cases hfalse : (i,false) ∈ S
        · simp [f,hfalse]
        · simpa [f,hfalse] using hi
    exact ⟨f,hs.2 _ hsub (choice_sufficient f)⟩
  · rintro ⟨f,rfl⟩
    exact choice_minimal f

theorem choice_injective (m : ℕ) : Function.Injective (@choiceCarrier m) := by
  intro f g he
  funext i
  have h : (i,f i) ∈ choiceCarrier g := he ▸ (by simp : (i,f i) ∈ choiceCarrier f)
  exact (mem_choiceCarrier g i (f i)).mp h

/-- Table-derived frontier contains exactly all independently chosen copies. -/
theorem computed_family (m : ℕ) : carriers (@obs m) target=
    Finset.univ.image (fun f : Fin m → Bool => choiceCarrier f) := by
  ext S
  rw [carriers_iff_original,minimal_iff_choice]
  simp

theorem computed_card (m : ℕ) : (carriers (@obs m) target).card=2^m := by
  rw [computed_family,Finset.card_image_of_injective _ (choice_injective m)]
  simp

/-- Explicit source column list, never a powerset of columns. -/
def columns (m : ℕ) : List (Atom m) :=
  (List.ofFn (fun i : Fin m => [(i,false),(i,true)])).flatten

theorem columns_complete (m : ℕ) (v : Atom m) : v ∈ columns m := by
  rcases v with ⟨i,b⟩
  simp only [columns,List.mem_flatten,List.mem_ofFn]
  refine ⟨[(i,false),(i,true)],⟨i,rfl⟩,?_⟩
  cases b <;> simp

def actualCarriers (m : ℕ) : List (Finset (Atom m)) := carrierList (columns m) obs target

def actualCuts (m : ℕ) : List (Finset (Atom m)) := cutList (columns m) obs target

theorem actualCarriers_family (m : ℕ) : (actualCarriers m).toFinset=carriers obs target :=
  listEnumerate_family (columns m) (columns_complete m) _

theorem actual_output_length (m : ℕ) : (actualCarriers m).length=2^m := by
  change (listEnumerate (columns m) (distinguishingEdges (@obs m) target)).length=2^m
  rw [← List.toFinset_card_of_nodup (listEnumerate_nodup (columns m) _),listEnumerate_family (columns m) (columns_complete m)]
  exact computed_card m

/-- Executable source-row decoder returns the SAME target on every actual row. -/
theorem returned_decoder (m : ℕ) (S : Finset (Atom m)) (hS : S ∈ actualCarriers m) (x : Row m) :
    decode obs target S (Access.readout obs S x)=some (target x) := by
  apply decode_returned
  have h := List.mem_toFinset.mpr hS
  rwa [actualCarriers_family] at h

/-- Original decoder interface is consumed too, with realized response range. -/
theorem original_decoder (m : ℕ) (S : Finset (Atom m)) (hS : S ∈ actualCarriers m) :
    FactorsThrough target (Access.rangeReadout obs S) := by
  apply (Access.sufficient_iff_factors_range obs target S).mp
  exact ((carrierList_iff_original (columns m) (columns_complete m) obs target S).mp hS).1

/-- NEW snapshot erasure: removed atoms become None, all other physical
readouts are preserved exactly. No legacy control rights are modified. -/
def erased {m : ℕ} (D : Finset (Atom m)) (x : Row m) (v : Atom m) : Option Bool :=
  if v ∈ D then none else some (obs x v)

theorem erased_on {m : ℕ} (D : Finset (Atom m)) (x : Row m) (v : Atom m) (hv : v ∈ D) :
    erased D x v=none := by simp [erased,hv]

theorem erased_off {m : ℕ} (D : Finset (Atom m)) (x : Row m) (v : Atom m) (hv : v ∉ D) :
    erased D x v=some (obs x v) := by simp [erased,hv]

/-- Exact physical frame, proved from actual erasure, not inferred from no repair. -/
theorem erased_agree_iff {m : ℕ} (D : Finset (Atom m)) (x y : Row m) :
    Access.AgreeOn (erased D) Finset.univ x y ↔ Access.AgreeOn obs (Finset.univ\D) x y := by
  constructor
  · intro h v hv
    have hv' := Finset.mem_sdiff.mp hv
    have he := h v (Finset.mem_univ v)
    simpa [erased,hv'.2] using he
  · intro h v _
    by_cases hv : v ∈ D
    · simp [erased,hv]
    · simpa [erased,hv] using h v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v,hv⟩)

theorem physical_frame {m : ℕ} (D : Finset (Atom m)) :
    Access.Sufficient (erased D) target Finset.univ ↔ Access.Sufficient obs target (Finset.univ\D) := by
  constructor
  · intro h x y ha; exact h x y ((erased_agree_iff D x y).mpr ha)
  · intro h x y ha; exact h x y ((erased_agree_iff D x y).mp ha)

/-- Actual erasure minimal failures consume original blocker without a new
carrier/cut field. -/
theorem returned_cut_original (m : ℕ) (D : Finset (Atom m)) :
    D ∈ actualCuts m ↔ Finite.Minimal
      (fun E => ¬ Access.Sufficient (erased E) target Finset.univ) D := by
  rw [actualCuts,cutList_iff_original (columns m) (columns_complete m)]
  rw [← Access.minimal_erasure_iff_blocker obs target D]
  have he : (fun E : Finset (Atom m) => ¬ Access.Sufficient (erased E) target Finset.univ)=
      (fun E => ¬ Access.Sufficient obs target (Finset.univ\E)) := by
    funext E; exact propext (not_congr (physical_frame E))
  rw [he]

/-- Failure is actual loss of both physical copies of at least one coordinate. -/
theorem erased_failure_iff {m : ℕ} (D : Finset (Atom m)) :
    ¬ Access.Sufficient (erased D) target Finset.univ ↔ ∃ i : Fin m, pair i ⊆ D := by
  simp [physical_frame,sufficient_iff_pair,pair,Finset.insert_subset_iff]

theorem pair_subset_pair {m : ℕ} (i j : Fin m) : pair i ⊆ pair j ↔ i=j := by
  constructor
  · intro h
    exact (mem_pair j (i,false)).mp (h (by simp))
  · rintro rfl
    exact Finset.Subset.refl _

theorem minimal_erased_failure {m : ℕ} (D : Finset (Atom m)) :
    Finite.Minimal (fun E => ¬ Access.Sufficient (erased E) target Finset.univ) D ↔
      ∃ i : Fin m, pair i=D := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ := (erased_failure_iff D).mp h.1
    exact ⟨i,h.2 _ hi ((erased_failure_iff _).mpr ⟨i,Finset.Subset.refl _⟩)⟩
  · rintro ⟨i,rfl⟩
    refine ⟨(erased_failure_iff _).mpr ⟨i,Finset.Subset.refl _⟩,?_⟩
    intro T ht hf
    obtain ⟨j,hj⟩ := (erased_failure_iff T).mp hf
    have he : j=i := (pair_subset_pair j i).mp (hj.trans ht)
    subst j
    exact Finset.Subset.antisymm ht hj

theorem actual_cut_family (m : ℕ) (D : Finset (Atom m)) :
    D ∈ actualCuts m ↔ ∃ i : Fin m, pair i=D :=
  (returned_cut_original m D).trans (minimal_erased_failure D)

theorem pair_injective (m : ℕ) : Function.Injective (@pair m) := by
  intro i j he
  exact (pair_subset_pair i j).mp he.subset

theorem actual_cut_set (m : ℕ) : (actualCuts m).toFinset=Finset.univ.image (@pair m) := by
  ext D
  simp only [List.mem_toFinset,actual_cut_family,Finset.mem_image,Finset.mem_univ,true_and]

theorem actual_cut_length (m : ℕ) : (actualCuts m).length=m := by
  have hn : (actualCuts m).Nodup := listEnumerate_nodup (columns m) _
  rw [← List.toFinset_card_of_nodup hn,actual_cut_set,
    Finset.card_image_of_injective _ (pair_injective m)]
  exact Fintype.card_fin m

/-- No two erased atom sets silently denote the same physical intervention. -/
theorem erased_damage_exact {m : ℕ} (D : Finset (Atom m)) (x : Row m) (v : Atom m) :
    erased D x v=none ↔ v∈D := by simp [erased]

theorem erasure_injective (m : ℕ) : Function.Injective (@erased m) := by
  intro D E he
  ext v
  have hv := congrFun (congrFun he none) v
  exact (erased_damage_exact D none v).symm.trans (hv ▸ erased_damage_exact E none v)

/-- Explicitly writing every output cannot have a polynomial bound in the
number of source rows: the source family has m+1 rows but exactly 2^m distinct
minimal carriers. This is only an output-size obstruction, not a claim about
compressed answers, single-carrier search or a complexity-class separation. -/
theorem no_row_polynomial_output_bound (C k : ℕ) :
    ∃ m, C*(Fintype.card (Row m))^k < (actualCarriers m).length := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt k (r := (2 : ℝ)) (by norm_num)).comp
    (Filter.tendsto_add_atTop_nat 1)
  have he : (fun m : ℕ => (C : ℝ)*((m : ℝ)+1)^k/(2 : ℝ)^m)=
      (fun m : ℕ => (2*(C : ℝ))*(((m+1 : ℕ) : ℝ)^k/(2 : ℝ)^(m+1))) := by
    funext m
    simp only [Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp
  have hl : Filter.Tendsto (fun m : ℕ => (C : ℝ)*((m : ℝ)+1)^k/(2 : ℝ)^m)
      Filter.atTop (nhds 0) := by
    rw [he]
    simpa only [mul_zero,Function.comp_apply] using h.const_mul (2*(C : ℝ))
  obtain ⟨m,hm⟩ := (hl.eventually_lt_const (by norm_num : (0 : ℝ)<1)).exists
  have hh : (C : ℝ)*((m : ℝ)+1)^k < (2 : ℝ)^m := (div_lt_one (by positivity)).mp hm
  refine ⟨m,?_⟩
  rw [actual_output_length]
  simp only [Fintype.card_option,Fintype.card_fin]
  exact_mod_cast hh

/-- The same obstruction holds even when source size counts ALL observation
and target cells, not merely its row count. -/
theorem no_table_polynomial_output_bound (C k : ℕ) :
    ∃ m, C*(Fintype.card (Row m)*(Fintype.card (Atom m)+1))^k < (actualCarriers m).length := by
  obtain ⟨m,hm⟩ := no_row_polynomial_output_bound (C*3^k) (2*k)
  refine ⟨m,lt_of_le_of_lt ?_ hm⟩
  have hcells : Fintype.card (Row m)*(Fintype.card (Atom m)+1) ≤ 3*(m+1)^2 := by
    rw [(table_dimensions m).1,(table_dimensions m).2]
    nlinarith
  calc
    C*(Fintype.card (Row m)*(Fintype.card (Atom m)+1))^k ≤ C*(3*(m+1)^2)^k :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left hcells k)
    _ = (C*3^k)*(Fintype.card (Row m))^(2*k) := by
      rw [(table_dimensions m).1,mul_pow,← pow_mul]
      ring

/-- The generic engine also handles the zero-dimensional constant source:
one empty sufficient carrier and no physical cut. -/
theorem zero_dimension : (actualCarriers 0).length=1 ∧ actualCuts 0=[] := by
  constructor
  · simpa using actual_output_length 0
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro D hD
    obtain ⟨i,_⟩ := (actual_cut_family 0 D).mp hD
    exact Fin.elim0 i

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteReplicaCarrierErasureSource
