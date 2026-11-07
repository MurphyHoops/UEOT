import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativePopulation

open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open CoreRegenerativeSource CoreRegenerativePopulation
open Lean

def jnat (n : Nat) : Json := toJson n
def jbool (b : Bool) : Json := toJson b
def jlist (xs : List Json) : Json := Json.arr xs.toArray

def jtriple (x : Triple) : Json := jlist [jbool x.active, jbool x.backup1, jbool x.backup2]
def jbody (x : Body) : Json := Json.mkObj
  [("code", jlist [jtriple x.rowH, jtriple x.rowD]),
   ("gate", jbool x.gate), ("bootstrap", jbool x.bootstrap), ("tag", jbool x.tag)]
def jid (x : Identity) : Json := Json.mkObj
  [("founder", jnat x.founder), ("births", jlist (x.births.map jnat))]
def joption {A : Type} (f : A → Json) : Option A → Json
  | none => Json.null | some x => f x
def jedge (e : AncestralEdge) : Json := Json.mkObj
  [("census", jnat e.census), ("source_id", jid e.sourceId), ("target_id", jid e.targetId),
   ("newborn", jbool e.newborn), ("source_kind", jbool e.sourceKind),
   ("target_kind", jbool e.targetKind)]
def jmember (x : Member) : Json := Json.mkObj
  [("identity", jid x.identity), ("parent", joption jid x.parent),
   ("born_at", jnat x.bornAt), ("age", jnat x.age), ("body", jbody x.body),
   ("wallet", jnat (capital x)), ("ancestry", jlist (x.ancestry.map jedge))]
def actionName : Action → String
  | .care => "care" | .bloom => "bloom" | .stop => "stop"
def statusName : Status → String
  | .executed => "executed" | .rejected => "rejected" | .stopped => "stopped"
def jnoise (z : Noise) : Json :=
  jlist [jnat z.1.1.val, jnat z.1.2.val, jbool z.2.1, jbool z.2.2]
def jresult (r : LocalResult) : Json := Json.mkObj
  [("retained", joption jbody r.retained), ("newborn", joption jbody r.newborn),
   ("repair_paid", jnat r.repairPaid), ("operation_paid", jnat r.operationPaid),
   ("output_capital", jnat (outputCapital r)), ("refund", jnat r.refund),
   ("status", toJson (statusName r.status))]

def allNoise : List Noise :=
  (List.finRange 3).flatMap fun u => (List.finRange 3).flatMap fun v =>
    [false, true].flatMap fun dp => [false, true].map fun dc => ((u,v),(dp,dc))

def eventRecord (theta kind tag : Bool) (a : Action) (z : Noise) (program : Bool) : Json :=
  let old := founder 0 theta kind tag
  let r := if program then programStep old.body z else step old.body a z
  Json.mkObj [("theta", jbool theta), ("kind", jbool kind), ("tag", jbool tag),
    ("program", jbool program), ("request", toJson (actionName a)), ("noise", jnoise z),
    ("before", jmember old), ("diagnostic", jbool (diagnostic old.body)),
    ("cap", jnat (requestCap old.body a)), ("raw_before", joption (toJson ∘ actionName)
      (rawExecute old.body (diagnostic old.body))),
    ("raw_restored", joption (toJson ∘ actionName)
      (rawExecute (restore old.body) (diagnostic old.body))),
    ("result", jresult r), ("outputs", jlist ((liftResult 0 old r).map jmember))]

def pairedRound (t : Nat) (population : List Member) (z : Noise) : List Member :=
  population.flatMap fun old => liftResult t old (programStep old.body z)

def twoRound : Json :=
  let first : Noise := ((2,2),(false,true))
  let second : Noise := ((2,2),(false,false))
  let start := [founder 0 true true false, founder 1 false false true]
  let pop1 := pairedRound 0 start first
  let pop2 := pairedRound 1 pop1 second
  Json.mkObj [("start", jlist (start.map jmember)), ("noise_first",jnoise first),
    ("noise_second",jnoise second), ("after_first",jlist (pop1.map jmember)),
    ("after_second",jlist (pop2.map jmember))]

def cutRecords : List Json :=
  let original := programBody true true false
  let bootcut := { original with bootstrap := false }
  let healthy := programBody true false false
  let gatecut := { healthy with gate := false }
  let wrongcode := { healthy with rowH := flipActive healthy.rowH }
  let z : Noise := ((2,2),(false,false))
  [Json.mkObj [("name",toJson "bootstrap"),("body",jbody bootcut),
      ("step",jresult (programStep bootcut z))],
   Json.mkObj [("name",toJson "main_gate"),("body",jbody gatecut),
      ("raw",joption (toJson ∘ actionName) (rawExecute gatecut false))],
   Json.mkObj [("name",toJson "active_code"),("body",jbody wrongcode),
      ("raw",joption (toJson ∘ actionName) (rawExecute wrongcode false))],
   Json.mkObj [("name",toJson "erasure"),("body",jbody (eraseCode healthy)),
      ("restored",jbody (restore (eraseCode healthy)))]]

def main : IO Unit := do
  let ports := [false,true].flatMap fun theta => [false,true].flatMap fun kind =>
    [false,true].flatMap fun tag => [.care,.bloom,.stop].flatMap fun a =>
      allNoise.map fun z => eventRecord theta kind tag a z false
  let programs := [false,true].flatMap fun theta => [false,true].flatMap fun kind =>
    [false,true].flatMap fun tag => allNoise.map fun z =>
      eventRecord theta kind tag (requestOf (programBody theta kind tag)) z true
  IO.println (Json.mkObj [("schema",toJson "UEOT/CORE_REGENERATIVE_LEAN_EXECUTION/V1"),
    ("port_count",jnat ports.length), ("program_count",jnat programs.length),
    ("ports",jlist ports),("programs",jlist programs),("two_round",twoRound),
    ("cuts",jlist cutRecords)]).compress
