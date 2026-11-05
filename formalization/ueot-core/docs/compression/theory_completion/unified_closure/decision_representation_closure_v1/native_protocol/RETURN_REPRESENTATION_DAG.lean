import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationModel
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationNative
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationBounds
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionDAGGenerator

open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open scoped BigOperators
open RegisterJointDecisionSource RegisterJointDecisionConsumer RegisterJointDecisionExecution
open RegisterDecisionObserver RegisterDecisionRepresentationNative
open RegisterDecisionRepresentationBounds
open FiniteJointDecisionSolver FiniteJointDecisionDAG FiniteJointDecisionDAGGenerator

namespace RegisterDecisionRepresentationRun

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

def longerFamily : Family Bool :=
  { diagnosticFamily with discount := 3/4, discount_bounds := by norm_num }

def faultFamily : Family Bool :=
  { longerFamily with normal := fun _ => 0, normal_bounds := by intro t; norm_num }

def normalFamily : Family Bool :=
  { longerFamily with normal := fun _ => 1, normal_bounds := by intro t; norm_num }

def duplicateFamily : Family Bool :=
  { longerFamily with normal := fun _ => 1/2, normal_bounds := by intro t; norm_num }

structure Input where
  caseKey : String
  name : String
  family : Family Bool
  prior : Bool → ℚ
  prior_nonneg : ∀ t, 0 ≤ prior t
  prior_total : ∑ t, prior t = 1
  wallet : Wallet
  horizon : ℕ

def equalInput (caseKey name : String) (P : Family Bool) (H : ℕ) (B : ℚ) (hB : 0 ≤ B) : Input :=
  ⟨caseKey, name, P, fun _ => 1/2,
    (by intro t; norm_num), (by norm_num [Fintype.sum_bool]), ⟨B, hB⟩, H⟩

def zeroPriorInput : Input :=
  { equalInput "zero_prior" "zero_prior_endpoint" longerFamily 3 1 (by norm_num) with
    prior := fun t => if t then 1 else 0
    prior_nonneg := by intro t; cases t <;> norm_num
    prior_total := by norm_num [Fintype.sum_bool] }

/-- The longer consumer was registered before its result: H8, B2, c1,
equal 1/4 and 3/4 prior, d3/4, lambda13/10, public goal true. -/
def registeredCases : List Input := [
  equalInput "two" "persistent_theta_two_step" diagnosticFamily 2 1 (by norm_num),
  equalInput "three" "population_backup_three_step" populationFamily 3 1 (by norm_num),
  equalInput "posterior" "posterior_changes_retry_three_step" diagnosticFamily 3 1 (by norm_num),
  equalInput "four" "receipt_feedback_four_step" feedbackFamily 4 1 (by norm_num),
  equalInput "long" "registered_h8_two_write_wallet" longerFamily 8 2 (by norm_num),
  equalInput "zero_horizon" "zero_horizon" diagnosticFamily 0 1 (by norm_num),
  equalInput "zero_budget" "zero_budget" diagnosticFamily 3 0 (by norm_num),
  equalInput "insufficient_prepay" "insufficient_prepay" diagnosticFamily 3 (3/4) (by norm_num),
  equalInput "all_fault" "all_fault" faultFamily 3 2 (by norm_num),
  equalInput "all_normal" "all_normal" normalFamily 3 2 (by norm_num),
  zeroPriorInput,
  equalInput "duplicate_rates" "duplicate_rates" duplicateFamily 3 1 (by norm_num),
  equalInput "false_goal" "false_public_goal" { longerFamily with goal := false } 3 1 (by norm_num)]

def observations : List Obs := [(false,false),(false,true),(true,false),(true,true)]

def actionName : Act → String
  | none => "stop"
  | some (false, none) => "root_idle"
  | some (true, none) => "child1_idle"
  | some (false, some false) => "root_write_false"
  | some (false, some true) => "root_write_true"
  | some (true, some false) => "child1_write_false"
  | some (true, some true) => "child1_write_true"

def ratJson (q : ℚ) : Lean.Json := .str (toString q)
def obsJson (o : Obs) : Lean.Json := .arr #[.bool o.1, .bool o.2]
def optionalBit : Option Bool → Lean.Json
  | none => .null
  | some b => .bool b

def stateJson (st : Stat) : Lean.Json := Lean.Json.mkObj [
  ("elapsed", Lean.toJson st.elapsed), ("s", Lean.toJson st.s),
  ("f", Lean.toJson st.f), ("paidCount", Lean.toJson st.paidCount),
  ("q", Lean.Json.mkObj [("root", .bool st.q.root), ("child", optionalBit st.q.child),
    ("stopped", .bool st.q.stopped), ("fresh", .bool st.q.fresh)])]

def edgeJson (M : Model Stat Act Obs) (r : Node Stat Act Obs) (a : Act) (o : Obs) : Lean.Json :=
  Lean.Json.mkObj [("obs", obsJson o), ("prob", ratJson (M.prob r.state a o)),
    ("next", match r.next a o with | none => .null | some j => Lean.toJson j)]

def alternativeJson (M : Model Stat Act Obs) (G : Graph Stat Act Obs)
    (r : Node Stat Act Obs) (a : Act) : Lean.Json :=
  Lean.Json.mkObj [("action", .str (actionName a)), ("q", ratJson (score M G r a)),
    ("edges", .arr ((observations.filter (fun o => decide (0 < M.prob r.state a o))).toArray.map
      (edgeJson M r a)))]

def nodeJson (M : Model Stat Act Obs) (G : Graph Stat Act Obs)
    (id : ℕ) (r : Node Stat Act Obs) : Lean.Json :=
  Lean.Json.mkObj [("id", Lean.toJson id), ("remaining", Lean.toJson r.remaining),
    ("state", stateJson r.state), ("value", ratJson r.value),
    ("chosen_action", .str (actionName r.choice)),
    ("alternatives", if r.remaining = 0 then .arr #[] else
      .arr ((M.actions r.state).toArray.map (alternativeJson M G r)))]

def graphJson (M : Model Stat Act Obs) (G : Graph Stat Act Obs) : Lean.Json :=
  .arr ((List.range G.size).toArray.map (fun j =>
    if hj : j < G.size then nodeJson M G j (G[j]'hj) else .null))

def proofEdgeCount (M : Model Stat Act Obs) (G : Graph Stat Act Obs) : ℕ :=
  G.toList.foldl (fun total r => total + if r.remaining = 0 then 0 else
    (M.actions r.state).foldl (fun total a => total +
      (observations.filter (fun o => decide (0 < M.prob r.state a o))).length) 0) 0

def auditNoise (P : Family Bool) (theta : Bool) (t : ℕ) : Noise :=
  ((if P.normal theta = 0 then false else if P.normal theta = 1 then true
    else decide (t % 3 ≠ 1)), decide (t % 2 = 0))

/-- These are actual direct graph executions, kept separate from the permitted
controller input. Hidden theta/noise/full physical slots occur only in audit. -/
def directRunJson (x : Input) (M : Model Stat Act Obs) (G : Graph Stat Act Obs)
    (root : ℕ) (theta : Bool) : Lean.Json :=
  let noise : Fin x.horizon → Noise := fun j => auditNoise x.family theta j.val
  let w : World Bool := ⟨theta, [some (!x.family.goal)], false⟩
  let execution := packedRun x.family.goal M G x.horizon (initialStat x.family.goal)
    (some root) w noise
  let sourceMass := (List.range x.horizon).foldl (fun mass t =>
    mass * ((if (auditNoise x.family theta t).1 then x.family.normal theta
      else 1 - x.family.normal theta) / 2)) (x.prior theta)
  Lean.Json.mkObj [
    ("theta", Lean.toJson (if theta then 1 else 0 : ℕ)),
    ("noise", .arr ((List.range x.horizon).toArray.map
      (fun t => obsJson (auditNoise x.family theta t)))),
    ("source_mass", ratJson sourceMass),
    ("requests", .arr (execution.history.toArray.map (fun e => .str (actionName e.1)))),
    ("receipts", .arr (execution.records.toArray.map obsJson)),
    ("payoff", ratJson (packedPayoff (x.family.price*x.family.tariff) x.family.discount execution.records)),
    ("final_store", .arr (execution.finalWorld.store.toArray.map optionalBit)),
    ("final_stopped", .bool execution.finalWorld.stopped)]

def directRunsJson (x : Input) (M : Model Stat Act Obs) (G : Graph Stat Act Obs)
    (root : ℕ) : Lean.Json :=
  .arr (([false,true].filter (fun t => decide (0 < x.prior t))).toArray.map
    (directRunJson x M G root))

/-- Every print path has both the proved Bellman checker and the source-bound
checker behind it. No old tree is constructed to obtain either this graph or
its direct execution records. IO refs force each measured pure stage before
the following timestamp. Encoding/output time is reported separately on stderr. -/
def runInput (x : Input) : IO Lean.Json := do
  let M := RegisterDecisionRepresentationModel.model x.family x.prior
    x.prior_nonneg x.prior_total x.wallet
  let initial := initialStat x.family.goal
  let t0 ← IO.monoMsNow
  let candidateRef ← IO.mkRef (generate M observations x.horizon initial)
  let candidate ← candidateRef.get
  let t1 ← IO.monoMsNow
  unless candidate.computedNodes = candidate.graph.size ∧ candidate.memoEntries = candidate.graph.size do
    throw (IO.userError "candidate storage counters disagree with the actual unique-node array")
  let certifiedRef ← IO.mkRef (certify M x.horizon initial candidate)
  let certified ← certifiedRef.get
  let t2 ← IO.monoMsNow
  match certified with
  | none => throw (IO.userError "Lean exact all-action DAG/root certificate rejected")
  | some c =>
      if _hb : boundCheck x.horizon c.graph = true then
        let t3 ← IO.monoMsNow
        let runsRef ← IO.mkRef (directRunsJson x M c.graph c.root.val)
        let runs ← runsRef.get
        let t4 ← IO.monoMsNow
        let nodesRef ← IO.mkRef (graphJson M c.graph)
        let nodes ← nodesRef.get
        let edgesRef ← IO.mkRef (proofEdgeCount M c.graph)
        let edges ← edgesRef.get
        let t5 ← IO.monoMsNow
        pure (Lean.Json.mkObj [
          ("schema", .str "UEOT/DECISION_REPRESENTATION_DAG/V1"),
          ("case", .str x.name), ("horizon", Lean.toJson x.horizon),
          ("normal_probabilities", .arr #[ratJson (x.family.normal false), ratJson (x.family.normal true)]),
          ("prior", .arr #[ratJson (x.prior false), ratJson (x.prior true)]),
          ("tariff", ratJson x.family.tariff), ("price", ratJson x.family.price),
          ("discount", ratJson x.family.discount), ("wallet", ratJson x.wallet.val),
          ("goal", .bool x.family.goal), ("initial_damaged", .bool true),
          ("root_id", Lean.toJson c.root.val), ("value", ratJson (c.graph[c.root.val]).value),
          ("checks", Lean.Json.mkObj [("bellman", .bool true), ("node_bounds", .bool true)]),
          ("metrics", Lean.Json.mkObj [
            ("node_count", Lean.toJson c.graph.size), ("proof_edges", Lean.toJson edges),
            ("cache_hits", Lean.toJson candidate.cacheHits),
            ("computed_nodes", Lean.toJson candidate.computedNodes),
            ("memo_entries", Lean.toJson candidate.memoEntries),
            ("solve_ms", Lean.toJson (t1-t0)), ("certificate_ms", Lean.toJson (t2-t1)),
            ("bound_check_ms", Lean.toJson (t3-t2)), ("direct_run_ms", Lean.toJson (t4-t3)),
            ("serialization_prepare_ms", Lean.toJson (t5-t4)),
            ("node_bound", Lean.toJson (24*(x.horizon+1)^4))]),
          ("nodes", nodes), ("direct_packed_runs", runs)])
      else throw (IO.userError "actual all-row horizon/count node-bound check rejected")

end RegisterDecisionRepresentationRun

def main (args : List String) : IO UInt32 := do
  match args with
  | [caseKey] =>
      match RegisterDecisionRepresentationRun.registeredCases.find? (fun x => x.caseKey == caseKey) with
      | none => IO.eprintln "unknown registered case"; return 2
      | some x =>
          let result ← RegisterDecisionRepresentationRun.runInput x
          let start ← IO.monoMsNow
          let encodedRef ← IO.mkRef result.compress
          let encoded ← encodedRef.get
          let finish ← IO.monoMsNow
          IO.eprintln s!"UEOT_ENCODING milliseconds={finish-start} bytes={encoded.utf8ByteSize}"
          IO.println encoded
          return 0
  | _ => IO.eprintln "expected one registered case: two, three, posterior, four, long, or a boundary alias"; return 2
