import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionFastSolver
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMechanismRegretCertificate

/-!
# The registered H3 fixed-mechanism consumer

The source, seven actions, single wallet and whole-run evaluation are fixed.
The three exact finite computations use the old solver on the NEW joint belief:
S oracle, G oracle, and the (3/4,1/4) lower-bound witness. The deployed program
is the very same returned pair of tables, selected by an independent uniform
four-point seed, once at initialization. Mechanism and world noise are not
arguments of `returned`. No reset or additional learning budget is used.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer

open scoped BigOperators
open RegisterJointDecisionSource (Act Obs Noise)
open RegisterMechanismDecisionSource
open FiniteJointDecisionBelief FiniteJointDecisionSolver
open FiniteJointDecisionFilteredModel FiniteJointDecisionSupportedPolicy

instance : Nonempty FaultMechanism := ⟨.S⟩

theorem sum_mechanisms {X : Type*} [AddCommMonoid X] (f : FaultMechanism → X) :
    (∑ m, f m) = f .S + f .G := by
  have hu : (Finset.univ : Finset FaultMechanism) = {.S,.G} := by decide
  rw [hu]
  simp

def parameters : Parameters where
  goal := true
  normal := 1/2
  normal_bounds := by norm_num
  tariff := 1
  tariff_pos := by norm_num
  price := 1/4
  price_nonneg := by norm_num
  discount := 1
  discount_bounds := by norm_num

inductive Input where
  | knownS
  | knownG
  | dual
  deriving DecidableEq, Repr

def prior : Input → FaultMechanism → ℚ
  | .knownS, .S => 1
  | .knownS, .G => 0
  | .knownG, .S => 0
  | .knownG, .G => 1
  | .dual, .S => 3/4
  | .dual, .G => 1/4

theorem prior_nonneg (q : Input) (m : FaultMechanism) : 0 ≤ prior q m := by
  cases q <;> cases m <;> norm_num [prior]

theorem prior_total (q : Input) : ∑ m, prior q m = 1 := by
  rw [sum_mechanisms]
  cases q <;> norm_num [prior]

def registeredInfo (q : Input) : Info :=
  initialInfo parameters (prior q) (prior_nonneg q) (prior_total q) ⟨2, by norm_num⟩

def observations : List Obs := [(false,false),(false,true),(true,false),(true,true)]

theorem observations_complete (o : Obs) : o ∈ observations := by
  rcases o with ⟨b,c⟩
  cases b <;> cases c <;> simp [observations]

/-- This is the old cached implementation, whose complete value/table pair is
proved equal to the original solver, including all counterfactual rows. -/
def cachedAt (q : Input) (H : ℕ) : ℚ × Table Act Obs H :=
  FiniteJointDecisionFastSolver.fastSolve (model parameters) observations
    observations_complete H (registeredInfo q)

def cachedResult (q : Input) : ℚ × Table Act Obs 3 := cachedAt q 3

def returnedS : Table Act Obs 3 := (cachedResult .knownS).2
def returnedG : Table Act Obs 3 := (cachedResult .knownG).2

/-- The complete executable return. `seed` is independent controller randomness,
not a hidden source label. Its distribution is fixed before the mechanism run. -/
def returned (seed : Fin 4) : Table Act Obs 3 :=
  if seed.val = 0 then returnedS else returnedG

 theorem cachedAt_eq (q : Input) (H : ℕ) :
    cachedAt q H = (optimalValue (model parameters) H (registeredInfo q),
      solve (model parameters) H (registeredInfo q)) :=
  FiniteJointDecisionFastSolver.fastSolve_eq _ _ _ _ _

 theorem returnedS_eq_solve : returnedS = solve (model parameters) 3 (registeredInfo .knownS) := by
  simp only [returnedS, cachedResult, cachedAt_eq]

 theorem returnedG_eq_solve : returnedG = solve (model parameters) 3 (registeredInfo .knownG) := by
  simp only [returnedG, cachedResult, cachedAt_eq]

/-- Complete actual source value, from the damaged founder with fixed m. -/
def tableJ {H : ℕ} (table : Table Act Obs H) (m : FaultMechanism) : ℚ :=
  sourceValue (source parameters) (gain parameters) parameters.discount table
    (initialWorld parameters.goal m)

/-- Small exact computation of ALL legal action scores, through the old solver.
This is not a check of only the deployed path. The separate matrix fields
execute the same returned tables in each actual fixed mechanism. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
 theorem exact_cached_data :
    let s := cachedResult .knownS
    let g := cachedResult .knownG
    let b := cachedResult .dual
    s.1 = 41/32 ∧ g.1 = 5/4 ∧ b.1 = 5/4 ∧
      tableJ s.2 .S = 41/32 ∧ tableJ s.2 .G = 37/32 ∧
      tableJ g.2 .S = 5/4 ∧ tableJ g.2 .G = 5/4 := by
  decide

 theorem oracleS_value : optimalValue (model parameters) 3 (registeredInfo .knownS) = 41/32 := by
  have h := exact_cached_data
  simpa only [cachedResult, cachedAt_eq] using h.1

 theorem oracleG_value : optimalValue (model parameters) 3 (registeredInfo .knownG) = 5/4 := by
  have h := exact_cached_data
  simpa only [cachedResult, cachedAt_eq] using h.2.1

 theorem dual_value : optimalValue (model parameters) 3 (registeredInfo .dual) = 5/4 := by
  have h := exact_cached_data
  simpa only [cachedResult, cachedAt_eq] using h.2.2.1

 theorem returned_matrix :
    tableJ returnedS .S = 41/32 ∧ tableJ returnedS .G = 37/32 ∧
      tableJ returnedG .S = 5/4 ∧ tableJ returnedG .G = 5/4 :=
  exact_cached_data.2.2.2

/-- Menu and wallet evolution depend on actual receipts, never on a hidden
mechanism. Thus every returned row is affordable under either prior. -/
 theorem feasible_same_wallet (P : Parameters) :
    ∀ {H : ℕ} (table : Table Act Obs H) (i j : Info), i.2 = j.2 →
      Feasible (model P) i table → Feasible (model P) j table := by
  intro H
  induction H with
  | zero => intro table i j hw hf; cases table; trivial
  | succ H ih =>
      intro table i j hw hf
      cases table with
      | node a children =>
          constructor
          · change a ∈ RegisterJointDecisionConsumer.menu P.tariff j.2
            have ha := hf.1
            change a ∈ RegisterJointDecisionConsumer.menu P.tariff i.2 at ha
            simpa only [hw] using ha
          · intro o
            apply ih (children o) ((model P).next i a o) ((model P).next j a o)
            · change RegisterJointDecisionConsumer.advance P.tariff i.2 a o =
                RegisterJointDecisionConsumer.advance P.tariff j.2 a o
              rw [hw]
            · exact hf.2 o

 theorem returned_feasible (seed : Fin 4) (q : Input) :
    Feasible (model parameters) (registeredInfo q) (returned seed) := by
  unfold returned
  split
  · rw [returnedS_eq_solve]
    exact feasible_same_wallet parameters _ (registeredInfo .knownS) (registeredInfo q)
      rfl (solve_feasible _ _ _)
  · rw [returnedG_eq_solve]
    exact feasible_same_wallet parameters _ (registeredInfo .knownG) (registeredInfo q)
      rfl (solve_feasible _ _ _)

 theorem returned_prefix_payment (seed : Fin 4) (q : Input) (w : Tape Obs 3)
    (hw : 0 < tapeWeight (model parameters) (registeredInfo q) (returned seed) w) :
    PrepaidAlong (model parameters) (walletContract parameters) (registeredInfo q)
      (returned seed) w ∧ ∀ k,
      (walletContract parameters).balance
          (prefixInfo (model parameters) (registeredInfo q) (returned seed) w k) =
        2 - prefixCost (model parameters) (walletContract parameters) (registeredInfo q)
          (returned seed) w k ∧
      0 ≤ prefixCost (model parameters) (walletContract parameters) (registeredInfo q)
          (returned seed) w k ∧
      prefixCost (model parameters) (walletContract parameters) (registeredInfo q)
          (returned seed) w k ≤ 2 := by
  exact ⟨feasible_prepaid _ _ 3 _ _ (returned_feasible seed q) w,
    feasible_prefix_ledger _ _ 3 _ _ (returned_feasible seed q) (by norm_num [walletContract,
      registeredInfo, initialInfo]) w hw⟩

def rhoJ (m : FaultMechanism) : ℚ := ∑ seed : Fin 4, (1/4) * tableJ (returned seed) m

 theorem rhoJ_eq (m : FaultMechanism) :
    rhoJ m = (1/4) * tableJ returnedS m + (3/4) * tableJ returnedG m := by
  norm_num [rhoJ, Fin.sum_univ_succ, returned]
  ring

 theorem returned_randomized_values : rhoJ .S = 161/128 ∧ rhoJ .G = 157/128 := by
  rw [rhoJ_eq, rhoJ_eq, returned_matrix.1, returned_matrix.2.1,
    returned_matrix.2.2.1, returned_matrix.2.2.2]
  norm_num

def oracle : FaultMechanism → ℝ
  | .S => 41/32
  | .G => 5/4

def dualWeight : FaultMechanism → ℝ
  | .S => 3/4
  | .G => 1/4

 theorem dualWeight_nonneg (m : FaultMechanism) : 0 ≤ dualWeight m := by
  cases m <;> norm_num [dualWeight]

 theorem dualWeight_total : ∑ m, dualWeight m = 1 := by
  rw [sum_mechanisms]
  norm_num [dualWeight]

/-- Every allowed full-history real-randomized kernel uses the same physical
source and the same private memory transition. No m is passed to actionProb. -/
noncomputable def actualJ (pi : RawCausalPolicy (model parameters))
    (h : pi.Memory) (m : FaultMechanism) : ℝ :=
  rawSourceValue (source parameters) (gain parameters) parameters.discount pi 3 h
    (initialWorld parameters.goal m)

 theorem raw_mixture_identity (pi : RawCausalPolicy (model parameters))
    (h : pi.Memory) (hi : pi.info h = registeredInfo .dual) :
    (∑ m, dualWeight m * actualJ pi h m) =
      rawValue (model parameters) pi 3 h := by
  rw [← rawSourceValue_eq_model (source parameters)
    (fun i => RegisterJointDecisionConsumer.menu parameters.tariff i.2)
    (fun i => RegisterJointDecisionConsumer.menu_nonempty parameters.tariff i.2)
    (RegisterJointDecisionConsumer.advance parameters.tariff) (gain parameters)
    parameters.discount parameters.discount_bounds.1 pi 3 h, hi]
  change (∑ m, dualWeight m * actualJ pi h m) =
    ∑ m, ((prior .dual m : ℚ) : ℝ) * actualJ pi h m
  apply Finset.sum_congr rfl
  intro m _
  cases m <;> norm_num [dualWeight, prior]

/-- The essential full comparison-class bound. The finite computation above
is plugged into the already proved raw supported-history Bayes theorem. -/
 theorem all_shared_weighted_upper (pi : RawCausalPolicy (model parameters))
    (h : pi.Memory) (hi : pi.info h = registeredInfo .dual)
    (hl : SupportedAdmissible (model parameters) pi 3 h) :
    (∑ m, dualWeight m * actualJ pi h m) ≤ 5/4 := by
  rw [raw_mixture_identity pi h hi]
  have hu := rawValue_le_solve (model parameters) pi 3 h hl
  rw [hi, dual_value] at hu
  norm_num at hu ⊢
  exact hu

 theorem all_shared_regret_lower (pi : RawCausalPolicy (model parameters))
    (h : pi.Memory) (hi : pi.info h = registeredInfo .dual)
    (hl : SupportedAdmissible (model parameters) pi 3 h) :
    (3/128 : ℝ) ≤ FiniteMechanismRegretCertificate.worst oracle (actualJ pi h) := by
  have hb := FiniteMechanismRegretCertificate.lower_bound oracle (actualJ pi h)
    dualWeight (5/4) dualWeight_nonneg dualWeight_total
    (all_shared_weighted_upper pi h hi hl)
  rw [sum_mechanisms] at hb
  norm_num [dualWeight, oracle] at hb
  exact hb

 theorem returned_regrets :
    oracle .S - (rhoJ .S : ℝ) = 3/128 ∧ oracle .G - (rhoJ .G : ℝ) = 3/128 := by
  rw [returned_randomized_values.1, returned_randomized_values.2]
  norm_num [oracle]

 theorem returned_worst_regret :
    FiniteMechanismRegretCertificate.worst oracle (fun m => (rhoJ m : ℝ)) = 3/128 := by
  apply le_antisymm
  · apply FiniteMechanismRegretCertificate.worst_le
    intro m
    cases m
    · exact returned_regrets.1.le
    · exact returned_regrets.2.le
  · simpa only [returned_regrets.1] using
      FiniteMechanismRegretCertificate.regret_le_worst oracle (fun m => (rhoJ m : ℝ)) .S

/-- Known-mechanism oracle values are certified over exactly the same legal
information class; only the initialization prior is concentrated on m. -/
 theorem knownS_all_policy_upper (pi : RawCausalPolicy (model parameters))
    (h : pi.Memory) (hi : pi.info h = registeredInfo .knownS)
    (hl : SupportedAdmissible (model parameters) pi 3 h) : actualJ pi h .S ≤ 41/32 := by
  have hu := rawValue_le_solve (model parameters) pi 3 h hl
  have he := rawSourceValue_eq_model (source parameters)
    (fun i => RegisterJointDecisionConsumer.menu parameters.tariff i.2)
    (fun i => RegisterJointDecisionConsumer.menu_nonempty parameters.tariff i.2)
    (RegisterJointDecisionConsumer.advance parameters.tariff) (gain parameters)
    parameters.discount parameters.discount_bounds.1 pi 3 h
  rw [← he, hi] at hu
  rw [oracleS_value] at hu
  change (∑ m, ((prior .knownS m : ℚ) : ℝ) * actualJ pi h m) ≤ ((41/32 : ℚ) : ℝ) at hu
  rw [sum_mechanisms] at hu
  norm_num [prior] at hu ⊢
  exact hu

 theorem knownG_all_policy_upper (pi : RawCausalPolicy (model parameters))
    (h : pi.Memory) (hi : pi.info h = registeredInfo .knownG)
    (hl : SupportedAdmissible (model parameters) pi 3 h) : actualJ pi h .G ≤ 5/4 := by
  have hu := rawValue_le_solve (model parameters) pi 3 h hl
  have he := rawSourceValue_eq_model (source parameters)
    (fun i => RegisterJointDecisionConsumer.menu parameters.tariff i.2)
    (fun i => RegisterJointDecisionConsumer.menu_nonempty parameters.tariff i.2)
    (RegisterJointDecisionConsumer.advance parameters.tariff) (gain parameters)
    parameters.discount parameters.discount_bounds.1 pi 3 h
  rw [← he, hi] at hu
  rw [oracleG_value] at hu
  change (∑ m, ((prior .knownG m : ℚ) : ℝ) * actualJ pi h m) ≤ ((5/4 : ℚ) : ℝ) at hu
  rw [sum_mechanisms] at hu
  norm_num [prior] at hu ⊢
  exact hu

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer
