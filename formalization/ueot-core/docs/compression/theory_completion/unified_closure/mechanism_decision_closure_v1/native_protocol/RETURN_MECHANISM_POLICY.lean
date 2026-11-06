import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer

open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterJointDecisionSource (Act Obs Noise)
open RegisterMechanismDecisionSource
open RegisterMechanismDecisionConsumer
open FiniteJointDecisionSolver

def actionName : Act → String
  | none => "stop"
  | some (false, none) => "root_idle"
  | some (true, none) => "child1_idle"
  | some (false, some false) => "root_write_false"
  | some (false, some true) => "root_write_true"
  | some (true, some false) => "child1_write_false"
  | some (true, some true) => "child1_write_true"

def obsJson (o : Obs) : Lean.Json := .arr #[.bool o.1, .bool o.2]

def tableJson {H : ℕ} (p : Table Act Obs H) : Lean.Json :=
  .arr ((rows observations p).toArray.map (fun row => Lean.Json.mkObj [
    ("history", .arr (row.1.toArray.map obsJson)),
    ("action", .str (actionName row.2))]))

def boolTape (word : Nat) (j : Fin 3) : Noise :=
  (decide ((word / 4^j.val) % 2 = 1),
   decide ((word / 4^j.val / 2) % 2 = 1))

def packedRunJson (s g : Table Act Obs 3) (m : FaultMechanism)
    (seed : Fin 4) (word : Fin 64) : Lean.Json :=
  let table := if seed.val = 0 then s else g
  let tape := boolTape word.val
  let run := packedExecute true table (initialWorld true m) tape
  Lean.Json.mkObj [
    ("mechanism", .str (if m = .S then "S" else "G")),
    ("seed", Lean.toJson seed.val),
    ("modes", .arr ((List.finRange 3).toArray.map (fun j => .bool (tape j).1))),
    ("labels", .arr ((List.finRange 3).toArray.map (fun j => .bool (tape j).2))),
    ("actions", .arr (run.history.toArray.map (fun h => .str (actionName h.1)))),
    ("receipts", .arr (run.records.toArray.map obsJson)),
    ("final_store", .arr (run.finalWorld.store.toArray.map
      (fun b => match b with | none => .null | some x => .bool x))),
    ("stopped", .bool run.finalWorld.stopped),
    ("J_path", .str (toString (RegisterJointDecisionExecution.packedPayoff (1/4) 1 run.records)))]

def resultJson : Lean.Json :=
  let s := cachedResult .knownS
  let g := cachedResult .knownG
  let dual := cachedResult .dual
  let runs := [FaultMechanism.S, FaultMechanism.G].flatMap (fun m =>
    (List.finRange 4).flatMap (fun seed =>
      (List.finRange 64).map (fun word => packedRunJson s.2 g.2 m seed word)))
  Lean.Json.mkObj [
    ("schema", .str "UEOT/MECHANISM_DECISION_RETURN/V1"),
    ("parameters", Lean.Json.mkObj [
      ("goal", .bool true), ("r", .str "1/2"), ("horizon", Lean.toJson (3 : Nat)),
      ("initial_wallet", .str "2"), ("write_tariff", .str "1"),
      ("price", .str "1/4"), ("discount", .str "1"), ("terminal", .str "0")]),
    ("private_seed", Lean.Json.mkObj [
      ("size", Lean.toJson (4 : Nat)), ("mass_each", .str "1/4"),
      ("component_S_seeds", .arr #[Lean.toJson (0 : Nat)]),
      ("component_G_seeds", .arr #[Lean.toJson (1 : Nat), Lean.toJson (2 : Nat), Lean.toJson (3 : Nat)])]),
    ("components", Lean.Json.mkObj [
      ("S", Lean.Json.mkObj [("solver_value", .str (toString s.1)), ("rows", tableJson s.2)]),
      ("G", Lean.Json.mkObj [("solver_value", .str (toString g.1)), ("rows", tableJson g.2)])]),
    ("dual_witness", Lean.Json.mkObj [
      ("weights", .arr #[.str "3/4", .str "1/4"]),
      ("solver_value", .str (toString dual.1)), ("rows", tableJson dual.2)]),
    ("packed_runs", .arr runs.toArray)]

def main : IO UInt32 := do
  IO.println resultJson.compress
  return 0
