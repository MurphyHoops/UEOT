import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionNativeConsumer
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionFastSolver

open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterJointDecisionSource RegisterJointDecisionConsumer
open FiniteJointDecisionBelief FiniteJointDecisionSolver

def diagnosticFamily : Family Bool where
  goal := true
  normal := fun t => if t then 3/4 else 1/4
  normal_bounds := by intro t; cases t <;> norm_num
  tariff := 1
  tariff_pos := by norm_num
  price := 13/10
  price_nonneg := by norm_num
  discount := 1/2
  discount_bounds := by norm_num

def populationFamily : Family Bool :=
  { diagnosticFamily with
    price := 7/4, price_nonneg := by norm_num
    discount := 3/4, discount_bounds := by norm_num }

def feedbackFamily : Family Bool :=
  { populationFamily with
    normal := fun t => if t then 7/8 else 3/4
    normal_bounds := by intro t; cases t <;> norm_num
    price := 37/16, price_nonneg := by norm_num }

def registeredInput (P : Family Bool) : Info Bool :=
  (initialBelief P (fun _ => 1/2) (by intro t; norm_num) (by norm_num [Fintype.sum_bool]),
    ⟨1, by norm_num⟩)

def registeredObservations : List Obs := [(false,false),(false,true),(true,false),(true,true)]

theorem registeredObservations_complete (o : Obs) : o ∈ registeredObservations := by
  rcases o with ⟨b,c⟩
  cases b <;> cases c <;> simp [registeredObservations]

def cachedResult (P : Family Bool) (H : ℕ) : ℚ × Table Act Obs H :=
  FiniteJointDecisionFastSolver.fastSolve (model P) registeredObservations
    registeredObservations_complete H (registeredInput P)

theorem cachedResult_sound (P : Family Bool) (H : ℕ) :
    (cachedResult P H).2 = returned P H (registeredInput P) ∧
    (cachedResult P H).1 = value (model P) (registeredInput P) (cachedResult P H).2 := by
  simp only [cachedResult, FiniteJointDecisionFastSolver.fastSolve_eq]
  exact ⟨rfl, rfl⟩

def actionName : Act → String
  | none => "stop"
  | some (false, none) => "root_idle"
  | some (true, none) => "child1_idle"
  | some (false, some false) => "root_write_false"
  | some (false, some true) => "root_write_true"
  | some (true, some false) => "child1_write_false"
  | some (true, some true) => "child1_write_true"

def obsJson (o : Obs) : Lean.Json := Lean.Json.arr #[.bool o.1, .bool o.2]

def tableJson (H : ℕ) (p : Table Act Obs H) : Lean.Json :=
  Lean.Json.arr ((rows [(false,false),(false,true),(true,false),(true,true)] p).toArray.map
    (fun row => Lean.Json.mkObj [
      ("history", Lean.Json.arr (row.1.toArray.map obsJson)),
      ("action", Lean.Json.str (actionName row.2))]))

/-- Cached execution is proved equal to the original exact value and entire
returned table, including all zero-mass branches and ties. No Python table or
equal-valued substitute is imported. -/
def resultJson (name : String) (P : Family Bool) (H : ℕ) : Lean.Json :=
  let cached := cachedResult P H
  let table := cached.2
  Lean.Json.mkObj [
    ("schema", .str "UEOT/JOINT_DECISION_RETURN/V1"),
    ("case", .str name),
    ("horizon", Lean.toJson H),
    ("normal_probabilities", .arr #[.str (toString (P.normal false)), .str (toString (P.normal true))]),
    ("prior", .arr #[.str "1/2",.str "1/2"]),
    ("tariff", .str (toString P.tariff)),
    ("price", .str (toString P.price)),
    ("discount", .str (toString P.discount)),
    ("wallet", .str "1"),
    ("goal", .bool true),
    ("initial_damaged", .bool true),
    ("value", .str (toString cached.1)),
    ("rows", tableJson H table)]

def main (args : List String) : IO UInt32 := do
  match args with
  | ["two"] => IO.println (resultJson "persistent_theta_two_step" diagnosticFamily 2).compress; return 0
  | ["three"] => IO.println (resultJson "population_backup_three_step" populationFamily 3).compress; return 0
  | ["posterior"] => IO.println (resultJson "posterior_changes_retry_three_step" diagnosticFamily 3).compress; return 0
  | ["four"] => IO.println (resultJson "receipt_feedback_four_step" feedbackFamily 4).compress; return 0
  | _ => IO.eprintln "expected two, three, posterior, or four"; return 2
