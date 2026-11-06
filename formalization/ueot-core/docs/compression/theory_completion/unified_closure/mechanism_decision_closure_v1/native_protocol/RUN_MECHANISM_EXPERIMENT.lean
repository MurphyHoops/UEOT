import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentPaths

/-! Execute the very separation table used in the sharp-TV theorem, at B=c=1.
Each mechanism has 4³ source atoms at r=1/2, retaining the original labels. -/
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterJointDecisionSource (Act Obs Noise cap)
open RegisterJointDecisionConsumer (charge)
open RegisterMechanismDecisionSource RegisterMechanismExperimentPaths

namespace RegisteredH3Experiment

def tick (n : Nat) (j : Fin 3) : Noise :=
  (decide ((n / 4^j.val) % 2 = 1), decide ((n / 4^j.val / 2) % 2 = 1))

def actionName : Act → String
  | none => "stop"
  | some (false,none) => "root_idle"
  | some (true,none) => "child1_idle"
  | some (false,some true) => "root_write_true"
  | some (false,some false) => "root_write_false"
  | some (true,some true) => "child1_write_true"
  | some (true,some false) => "child1_write_false"

def ledger : ℚ → List (Act × Obs) → List Lean.Json
  | _, [] => []
  | B, (a,o)::rest =>
    let cost := charge 1 o
    (Lean.Json.mkObj [
      ("action",.str (actionName a)), ("receipt",.arr #[.bool o.1,.bool o.2]),
      ("cap",.str (toString (cap a))), ("balance_before",.str (toString B)),
      ("prepaid",.bool (decide (cap a ≤ B))), ("fee",.str (toString cost)),
      ("balance_after",.str (toString (B-cost)))]) :: ledger (B-cost) rest

def one (m : FaultMechanism) (n : Nat) : Lean.Json :=
  let z := tick n
  let run := packedExecute true (separationTable true) (initialWorld true m) z
  Lean.Json.mkObj [
    ("mechanism",.str (if m = .S then "S" else "G")),
    ("modes",.arr ((List.finRange 3).toArray.map fun j => .bool (z j).1)),
    ("labels",.arr ((List.finRange 3).toArray.map fun j => .bool (z j).2)),
    ("ledger",.arr (ledger 1 run.history).toArray),
    ("exclusive",.bool (decide (run.history = separationHistory true)))]

def report : Lean.Json :=
  Lean.Json.mkObj [("schema",.str "UEOT/H3_SHARP_EXPERIMENT/V1"),
    ("budget",.str "1"),("tariff",.str "1"),("r",.str "1/2"),
    ("atoms",.arr (([FaultMechanism.S,FaultMechanism.G].flatMap
      (fun m => (List.range 64).map (one m))).toArray))]

end RegisteredH3Experiment

def main : IO Unit := IO.println RegisteredH3Experiment.report.compress
