import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionInformation

/-!
# Attained minimax regret, and the exact deterministic gap

The all-kernel lower bound in Consumer already covers real randomized causal
policies legal on actual supported histories. Here a finite private seed chooses
one complete receipt table before the fixed mechanism runs; all of its weights
are real. A raw finite-horizon kernel can equivalently be realized as such a law
on finite response trees. This representation is only for the mathematical
comparison class: the executable artifact remains the two H3 tables and Fin 4.

The deterministic gap is a source-specific lattice theorem. Hidden labels are
summed out using the proved label-blind packed source; they are not a controller
randomness interface. Eight equal-probability mode paths and quarter-valued
path payoffs force the denominator 32, for every deterministic table.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionRegret

open scoped BigOperators
open RegisterJointDecisionSource (Act Obs Noise)
open RegisterMechanismDecisionSource
open RegisterMechanismDecisionConsumer
open FiniteJointDecisionBelief FiniteJointDecisionSolver
open FiniteJointDecisionFilteredModel FiniteJointDecisionSupportedPolicy
open FiniteMechanismRegretCertificate

 theorem feasible_supported (P : Parameters) :
    ∀ {H : ℕ} (table : Table Act Obs H) (i : Info),
      Feasible (model P) i table → SupportedFeasible (model P) i table := by
  intro H
  induction H with
  | zero => intro table i hf; cases table; trivial
  | succ H ih =>
      intro table i hf
      cases table with
      | node a children =>
          exact ⟨hf.1, fun o _ => ih _ _ (hf.2 o)⟩

 theorem commonTwo_feasible (q : Input) :
    Feasible (model parameters) (registeredInfo q) commonTwo := by
  simp only [commonTwo, cachedAt_eq]
  exact feasible_same_wallet parameters _ (registeredInfo .knownS) (registeredInfo q)
    rfl (solve_feasible _ _ _)

 theorem nonzero_common_optimum :
    Feasible (model parameters) (registeredInfo .dual) commonTwo ∧
      tableJ commonTwo .S = optimalValue (model parameters) 2 (registeredInfo .knownS) ∧
      tableJ commonTwo .G = optimalValue (model parameters) 2 (registeredInfo .knownG) ∧
      0 < tableJ commonTwo .S := by
  refine ⟨commonTwo_feasible .dual, ?_, ?_, ?_⟩
  · rw [short_common_values.1, short_common_values.2.2.1]
  · rw [short_common_values.2.1, short_common_values.2.2.2]
  · rw [short_common_values.2.2.1]
    norm_num

 theorem table_mixture_identity (table : Table Act Obs 3) :
    value (model parameters) (registeredInfo .dual) table =
      (3/4) * tableJ table .S + (1/4) * tableJ table .G := by
  rw [RegisterMechanismDecisionSource.value_eq_source]
  change (∑ m, prior .dual m * tableJ table m) = _
  rw [sum_mechanisms]
  rfl

/-- All supported deterministic alternatives, including actions absent from
both returned execution paths, enter the same old solver upper bound. -/
 theorem table_weighted_upper (table : Table Act Obs 3)
    (hl : SupportedFeasible (model parameters) (registeredInfo .dual) table) :
    (∑ m, dualWeight m * (tableJ table m : ℝ)) ≤ 5/4 := by
  have hu := supported_value_le_solve (model parameters) 3 (registeredInfo .dual) table hl
  rw [dual_value, table_mixture_identity] at hu
  rw [sum_mechanisms]
  change (3/4 : ℝ) * (tableJ table .S : ℝ) + (1/4) * (tableJ table .G : ℝ) ≤ 5/4
  have hu' : (((3/4) * tableJ table .S + (1/4) * tableJ table .G : ℚ) : ℝ) ≤
      ((5/4 : ℚ) : ℝ) := Rat.cast_le.mpr hu
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hu'

 theorem deterministic_regret_lower (table : Table Act Obs 3)
    (hl : SupportedFeasible (model parameters) (registeredInfo .dual) table) :
    (3/128 : ℝ) ≤ worst oracle (fun m => (tableJ table m : ℝ)) := by
  have hb := lower_bound oracle (fun m => (tableJ table m : ℝ)) dualWeight (5/4)
    dualWeight_nonneg dualWeight_total (table_weighted_upper table hl)
  rw [sum_mechanisms] at hb
  norm_num [dualWeight, oracle] at hb
  exact hb

/-- A finite independent private law on complete allowed response tables.
The mechanism is not an argument to the weights or to the chosen table. -/
structure MixedPolicy where
  Seed : Type
  seeds : Fintype Seed
  weight : Seed → ℝ
  nonneg : ∀ s, 0 ≤ weight s
  total : ∑ s, weight s = 1
  table : Seed → Table Act Obs 3
  legal : ∀ s, weight s ≠ 0 →
    SupportedFeasible (model parameters) (registeredInfo .dual) (table s)

attribute [instance] MixedPolicy.seeds

noncomputable def mixedJ (p : MixedPolicy) (m : FaultMechanism) : ℝ :=
  ∑ s, p.weight s * (tableJ (p.table s) m : ℝ)

 theorem every_mixed_weighted_upper (p : MixedPolicy) :
    (∑ m, dualWeight m * mixedJ p m) ≤ 5/4 := by
  unfold mixedJ
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ s, ∑ m, dualWeight m * (p.weight s * (tableJ (p.table s) m : ℝ))) =
        ∑ s, p.weight s * ∑ m, dualWeight m * (tableJ (p.table s) m : ℝ) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ ≤ ∑ s, p.weight s * (5/4) := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hz : p.weight s = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (table_weighted_upper (p.table s) (p.legal s hz)) (p.nonneg s)
    _ = 5/4 := by rw [← Finset.sum_mul, p.total, one_mul]

/-- The implemented four-point law. It uses the identical returned definition
consumed by the output/native driver, not a separately reconstructed table. -/
noncomputable def rho : MixedPolicy where
  Seed := Fin 4
  seeds := inferInstance
  weight := fun _ => 1/4
  nonneg := by intro s; norm_num
  total := by norm_num [Fin.sum_univ_succ]
  table := returned
  legal := fun s _ => feasible_supported parameters _ _ (returned_feasible s .dual)

 theorem rho_value (m : FaultMechanism) : mixedJ rho m = (rhoJ m : ℝ) := by
  change (∑ s : Fin 4, (1/4 : ℝ) * (tableJ (returned s) m : ℝ)) =
    ((∑ s : Fin 4, (1/4 : ℚ) * tableJ (returned s) m) : ℝ)
  push_cast <;> rfl

 theorem rho_worst : worst oracle (mixedJ rho) = 3/128 := by
  have heq : mixedJ rho = fun m => (rhoJ m : ℝ) := funext rho_value
  rw [heq]
  exact returned_worst_regret

/-- Exact minimax over the complete finite real-randomized response-tree law
class. Consumer.all_shared_regret_lower separately gives the same lower bound
in the original arbitrary-memory RawCausalPolicy interface. -/
 theorem minimax_regret_exact : minimax oracle mixedJ = 3/128 ∧ worst oracle (mixedJ rho) = 3/128 := by
  apply matched_certificate oracle dualWeight mixedJ (5/4) (3/128) rho
    dualWeight_nonneg dualWeight_total every_mixed_weighted_upper
  · rw [sum_mechanisms]
    norm_num [dualWeight, oracle]
  · exact rho_worst

/-- Last-step payoffs at the same actually reachable 11/00 prefix. These
are continuations in the existing world and its remaining wallet, not fresh
experiments. The distinguishing receipt, if obtained, arrives after this action. -/
 theorem ambiguous_last_values :
    sourceValue (source parameters) (gain parameters) 1
      (.node RegisterMechanismDecisionInformation.childIdle (fun _ => .halt))
      (RegisterMechanismDecisionInformation.ambiguousWorld true .S) = 1/2 ∧
    sourceValue (source parameters) (gain parameters) 1
      (.node RegisterMechanismDecisionInformation.childIdle (fun _ => .halt))
      (RegisterMechanismDecisionInformation.ambiguousWorld true .G) = 0 ∧
    sourceValue (source parameters) (gain parameters) 1
      (.node (RegisterMechanismDecisionInformation.rootWrite true) (fun _ => .halt))
      (RegisterMechanismDecisionInformation.ambiguousWorld true .S) = 3/8 ∧
    sourceValue (source parameters) (gain parameters) 1
      (.node (RegisterMechanismDecisionInformation.rootWrite true) (fun _ => .halt))
      (RegisterMechanismDecisionInformation.ambiguousWorld true .G) = 3/8 := by
  norm_num [sourceValue, source, parameters, gain, RegisterJointDecisionConsumer.charge,
    RegisterMechanismDecisionInformation.childIdle, RegisterMechanismDecisionInformation.rootWrite,
    RegisterMechanismDecisionInformation.ambiguousWorld, observe,
    RegisterJointDecisionSource.observe, RegisterJointDecisionSource.effective,
    RegisterJointDecisionSource.address, RegisterJointDecisionSource.packedObserve,
    RegisterJointDecisionSource.packedLookup, RegisterJointDecisionSource.childBit,
    RegisterJointDecisionSource.primitiveWeight, Fintype.sum_prod_type, Fintype.sum_bool,
    show FaultMechanism.G ≠ FaultMechanism.S from by decide]

 theorem ambiguous_mass_and_wallet (m : FaultMechanism) :
    RegisterMechanismDecisionInformation.historyIntegral true (1/2) (fun _ => 1)
      (initialWorld true m) (RegisterMechanismDecisionInformation.ambiguousHistory true) = 1/4 ∧
    (RegisterMechanismDecisionSource.historyInfo parameters (registeredInfo .dual)
      (RegisterMechanismDecisionInformation.ambiguousHistory true)).2.val = 1 := by
  constructor
  · rw [RegisterMechanismDecisionInformation.ambiguous_likelihood]
    norm_num
  · change max 0 (max 0 ((2:ℚ) - 1) - 0) = 1
    norm_num

/-- A source receipt has a literal quarter-integral reward. -/
def quarterGain (o : Obs) : ℤ := (if o.1 then 4 else 0) - (if o.2 then 1 else 0)

 theorem gain_quarters (a : Act) (o : Obs) :
    4 * gain parameters a o = (quarterGain o : ℚ) := by
  rcases o with ⟨b,c⟩
  cases b <;> cases c <;> norm_num [gain, parameters, RegisterJointDecisionConsumer.charge,
    quarterGain]

/-- The original four primitive outcomes reduce to two modes because labels
never enter this source's physical projection, receipt, action or payoff. -/
 theorem sourceValue_half_modes {H : ℕ} (a : Act) (children : Obs → Table Act Obs H) (w : World) :
    sourceValue (source parameters) (gain parameters) 1 (.node a children) w =
      (1/2) * (gain parameters a (observe true w a (false,false)) +
        sourceValue (source parameters) (gain parameters) 1
          (children (observe true w a (false,false))) (step true w a (false,false))) +
      (1/2) * (gain parameters a (observe true w a (true,false)) +
        sourceValue (source parameters) (gain parameters) 1
          (children (observe true w a (true,false))) (step true w a (true,false))) := by
  rw [sourceValue, Fintype.sum_prod_type]
  simp only [primitive_quarter, one_mul]
  change (∑ mode : Bool, ∑ _label : Bool, (1/4 : ℚ) *
    (gain parameters a (observe true w a (mode,false)) +
      sourceValue (source parameters) (gain parameters) 1
        (children (observe true w a (mode,false))) (step true w a (mode,false)))) = _
  simp only [Fintype.sum_bool]
  ring

/-- An integer numerator derived recursively from the actual two-mode source.
This definition does not enumerate or restrict the deterministic strategy. -/
def scaledValue : {H : ℕ} → Table Act Obs H → World → ℤ
  | 0, .halt, _ => 0
  | H+1, .node a children, w =>
      let obsF := observe true w a (false,false)
      let obsN := observe true w a (true,false)
      (2:ℤ)^H * (quarterGain obsF + quarterGain obsN) +
        scaledValue (children obsF) (step true w a (false,false)) +
        scaledValue (children obsN) (step true w a (true,false))

 theorem source_value_lattice :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : World),
      4 * (2:ℚ)^H * sourceValue (source parameters) (gain parameters) 1 table w =
        (scaledValue table w : ℚ) := by
  intro H
  induction H with
  | zero => intro table w; cases table; simp [sourceValue, scaledValue]
  | succ H ih =>
      intro table w
      cases table with
      | node a children =>
          rw [sourceValue_half_modes]
          simp only [scaledValue, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
          rw [← ih (children (observe true w a (false,false))) (step true w a (false,false)),
            ← ih (children (observe true w a (true,false))) (step true w a (true,false)),
            ← gain_quarters a (observe true w a (false,false)),
            ← gain_quarters a (observe true w a (true,false)), pow_succ]
          ring

 theorem deterministic_J_lattice (table : Table Act Obs 3) (m : FaultMechanism) :
    ∃ z : ℤ, (tableJ table m : ℝ) = (z : ℝ) / 32 := by
  let z := scaledValue table (initialWorld true m)
  have he := source_value_lattice table (initialWorld true m)
  change 4 * (2:ℚ)^3 * tableJ table m = (z : ℚ) at he
  have hq : tableJ table m = (z : ℚ) / 32 := by norm_num at he; linarith
  refine ⟨z, ?_⟩
  exact_mod_cast hq

 theorem worst_two (J : FaultMechanism → ℝ) :
    worst oracle J = max (oracle .S - J .S) (oracle .G - J .G) := by
  apply le_antisymm
  · apply worst_le
    intro m
    cases m
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (regret_le_worst oracle J .S) (regret_le_worst oracle J .G)

 theorem deterministic_regret_lattice (table : Table Act Obs 3) :
    ∃ z : ℤ, worst oracle (fun m => (tableJ table m : ℝ)) = (z : ℝ) / 32 := by
  obtain ⟨zs, hs⟩ := deterministic_J_lattice table .S
  obtain ⟨zg, hg⟩ := deterministic_J_lattice table .G
  have hs' : oracle .S - (tableJ table .S : ℝ) = ((41-zs : ℤ) : ℝ)/32 := by
    rw [hs]
    norm_num [oracle]
    ring
  have hg' : oracle .G - (tableJ table .G : ℝ) = ((40-zg : ℤ) : ℝ)/32 := by
    rw [hg]
    norm_num [oracle]
    ring
  rw [worst_two, hs', hg']
  by_cases h : ((41-zs : ℤ) : ℝ)/32 ≤ ((40-zg : ℤ) : ℝ)/32
  · exact ⟨40-zg, max_eq_right h⟩
  · exact ⟨41-zs, max_eq_left (le_of_lt (lt_of_not_ge h))⟩

/-- The positive all-policy lower bound excludes zero on the deterministic
1/32 lattice. This quantifies every legal deterministic receipt table. -/
 theorem deterministic_lower_exact (table : Table Act Obs 3)
    (hl : SupportedFeasible (model parameters) (registeredInfo .dual) table) :
    (1/32 : ℝ) ≤ worst oracle (fun m => (tableJ table m : ℝ)) := by
  have hp := deterministic_regret_lower table hl
  obtain ⟨z, hz⟩ := deterministic_regret_lattice table
  rw [hz] at hp ⊢
  have hzpos : (0:ℝ) < z := by linarith
  have hzint : (0:ℤ) < z := by exact_mod_cast hzpos
  have hz1 : (1:ℤ) ≤ z := hzint
  have hzreal : (1:ℝ) ≤ z := by exact_mod_cast hz1
  linarith

 theorem returnedG_worst : worst oracle (fun m => (tableJ returnedG m : ℝ)) = 1/32 := by
  rw [worst_two, returned_matrix.2.2.1, returned_matrix.2.2.2]
  norm_num [oracle]

abbrev DeterministicPolicy :=
  {table : Table Act Obs 3 // SupportedFeasible (model parameters) (registeredInfo .dual) table}

def deterministicAchiever : DeterministicPolicy :=
  ⟨returnedG, by
    have hf := returned_feasible (1 : Fin 4) .dual
    have he : returned (1 : Fin 4) = returnedG := rfl
    rw [he] at hf
    exact feasible_supported parameters _ _ hf⟩

noncomputable def deterministicJ (p : DeterministicPolicy) (m : FaultMechanism) : ℝ :=
  tableJ p.val m

 theorem deterministic_minimax_exact :
    minimax oracle deterministicJ = 1/32 := by
  have hl (p : DeterministicPolicy) : (1/32:ℝ) ≤ worst oracle (deterministicJ p) :=
    deterministic_lower_exact p.val p.property
  have hb : BddBelow (Set.range (fun p => worst oracle (deterministicJ p))) := by
    refine ⟨1/32, ?_⟩
    rintro y ⟨p,rfl⟩
    exact hl p
  apply le_antisymm
  · have hu := csInf_le hb (show worst oracle (deterministicJ deterministicAchiever) ∈
        Set.range (fun p => worst oracle (deterministicJ p)) from ⟨deterministicAchiever,rfl⟩)
    change minimax oracle deterministicJ ≤ worst oracle (fun m => (tableJ returnedG m : ℝ)) at hu
    rw [returnedG_worst] at hu
    exact hu
  · apply le_csInf (show (Set.range (fun p => worst oracle (deterministicJ p))).Nonempty from
      ⟨_,deterministicAchiever,rfl⟩)
    rintro y ⟨p,rfl⟩
    exact hl p

 theorem private_randomization_strict_gain : (3/128:ℝ) < 1/32 := by norm_num

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionRegret
