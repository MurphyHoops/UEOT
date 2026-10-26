import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.NoisyFiniteRiskOracleWitness
import Lean

open Lean UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open NoisyFiniteRiskOracle NoisyFiniteRiskOracleWitness
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure

local instance : LinearOrder State := stateOrder
local instance : DecidableEq State := stateOrder.toDecidableEq

def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def r2LiftExcept {a : Type} : Except String a → IO a
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def decodeState : Nat → State
  | 1 => some false
  | 2 => some true
  | _ => none

def regressionChecks : IO Unit := do
  check (oracle quarterSamples 0 == .rejected) "coarse record was not rejected"
  check (oracle quarterSamples 1 == .certified) "fine record was not certified"
  let run := scanNoisy (oracle quarterSamples) 2
  check (run.found == some 1 && run.queries == [0, 1]) "wrong first PASS or trace"
  check (referenceRisk (program true) initialMass (observe true) (some false)
    quarterSamples 2 (missedGoal 2) == 9 / 16) "wrong computed reference risk"
  check (computedBudget quarterSamples true == 53 / 80) "wrong computed risk budget"
  check (computedAccepts quarterSamples true) "valid finite certificate rejected"
  check (computedSelection quarterSamples |>.map Fin.val == some 1)
    "actual finite selector disagrees with the scan"
  check (computedSelectedAccepts quarterSamples) "selected certificate rejected"
  check (referenceRisk (program true) initialMass (observe true) (some false)
    eighthSamples 2 (missedGoal 2) == 49 / 64) "wrong contrasting reference risk"
  check (!(computedSelectedAccepts eighthSamples)) "over-cap reference budget accepted"
  check (!(accepts (program true) initialMass (observe true) (some false)
    quarterSamples (1 / 20) (1 / 8) (3 / 5) 2 (missedGoal 2)))
    "insufficient risk budget accepted"
  let ambiguous : Nat → CertificationDecision := fun i =>
    if i = 0 then decideRat (1 / 8) (1 / 10) (1 / 8) else .certified
  check (scanOutcome ambiguous 2 == some (0, .ambiguous)) "ambiguity was skipped"
  check ((scanNoisy ambiguous 2).queries == [0]) "queried past ambiguity"
  check ((scanNoisy ambiguous 0).found.isNone && (scanNoisy ambiguous 0).queries.isEmpty)
    "empty candidate list was not exhausted"
  let empty : SampleTable State Unit 0 := fun _ _ k => Fin.elim0 k
  check (!(computedAccepts empty true)) "zero samples accepted"
  let noQ : Fin 0 → State → State := fun j => Fin.elim0 j
  let noProgram : Fin 0 → ExecutableSupportSynthesis.Program State State Unit :=
    fun j => Fin.elim0 j
  check ((selectCandidate noQ quarterSamples (1 / 20) (1 / 8)).isNone)
    "empty finite family selected a candidate"
  check (!(selectedAccepts noQ noProgram initialMass (some false) quarterSamples
    (1 / 20) (1 / 8) (7 / 10) 2 (fun _ => missedGoal 2))) "empty family accepted"
  IO.println "R2_FIXED_REGRESSION_PASS: FAIL/PASS; first trace; reference 9/16; budget 53/80; contrasting 49/64 rejected; AMBIGUOUS stops; low budget, zero samples and empty family rejected"

def sampledRun (path : String) : IO Unit := do
  let contents ← IO.FS.readFile path
  let dataset ← r2LiftExcept (Json.parse contents)
  let count ← r2LiftExcept (dataset.getObjValAs? Nat "sample_count")
  check (count == 4096) "registered sample allocation changed"
  let rows ← r2LiftExcept (dataset.getObjValAs? (Array (Array Nat)) "rows")
  check (rows.size == 3) "expected the three registered source rows"
  for i in [0:3] do
    let row := rows[i]!
    check (row.size == 4096) "a registered row has the wrong sample count"
    for value in row do
      check (decide (value ≤ 2)) "unknown state encoding"
      check (decide (relation (decodeState i) () (decodeState value)))
        "sample outside declared structural support"
  let sample : SampleTable State Unit 4096 := fun x _ k =>
    decodeState ((rows.getD (stateRank x).val #[]).getD k.val 0)
  let run := scanNoisy (oracle sample) 2
  let selected := scanOutcome (oracle sample) 2
  let finiteSelected := computedSelection sample
  let accepted := computedSelectedAccepts sample
  match selected with
  | some (i, .certified) =>
      check (finiteSelected.map Fin.val == some i) "finite selector and trace disagree"
  | _ => check finiteSelected.isNone "selected a candidate without a PASS"
  let status := match selected with
    | none => "EXHAUSTED"
    | some (_, .ambiguous) => "AMBIGUOUS"
    | some (_, .certified) => if accepted then "ACCEPTED" else "BUDGET_EXCEEDED"
    | some (_, .rejected) => "INVALID_SCAN_RESULT"
  let result := Json.mkObj [
    ("state", toJson status), ("accepted", toJson accepted),
    ("sample_count", toJson count), ("queries", toJson run.queries),
    ("first_non_fail", toJson run.found),
    ("selected_candidate", toJson (finiteSelected.map Fin.val)),
    ("empirical_progress", toJson (toString (empiricalMass (sample (some false) ()) (some true)))),
    ("coarse_defect", toJson (toString (empiricalDefect (observe false) sample))),
    ("fine_defect", toJson (toString (empiricalDefect (observe true) sample))),
    ("fine_reference_risk", toJson (toString (referenceRisk (program true) initialMass
      (observe true) (some false) sample 2 (missedGoal 2)))),
    ("fine_budget", toJson (toString (computedBudget sample true))),
    ("threshold", toJson "1/8"), ("row_tv_radius", toJson "1/20"),
    ("defect_interval_radius", toJson "1/10"),
    ("risk_cap", toJson "7/10"), ("horizon", toJson (2 : Nat))]
  IO.println ("R2_SAMPLED_RESULT " ++ result.compress)

def main (args : List String) : IO Unit := do
  regressionChecks
  match args with
  | [] => pure ()
  | [path] => sampledRun path
  | _ => throw (IO.userError "provide at most one preserved dataset")
