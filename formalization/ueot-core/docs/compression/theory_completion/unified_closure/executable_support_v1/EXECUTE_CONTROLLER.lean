import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ExecutableSupportControllerWitness

open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open ExecutableSupportSynthesis ExecutableSupportControllerWitness

def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main : IO Unit := do
  let some controller :=
      synthesize observe relation certification initialTable actionOrder false
    | throw (IO.userError "viable initial support was rejected")
  let mut state : Option Bool := some false
  let mut memory := controller.initialMemory ()
  let mut actions : Array Bool := #[]
  for index in [0:12] do
    check (decide (state ∈ memory)) s!"state missing from memory at {index}"
    let action := controller.action memory
    check (decide (certification state action)) s!"uncertified action at {index}"
    let next := nextState state action
    check next.isSome s!"entered the failure state at {index}"
    memory := controller.update memory action ()
    check (decide (memory = {next})) s!"incorrect source-support update at {index}"
    state := next
    actions := actions.push action
  check (actions == #[false, true, false, true, false, true,
    false, true, false, true, false, true]) "wrong phase sequence"
  check (synthesize observe relation certification mixedTable actionOrder false).isNone
    "ambiguous initial phase was accepted"
  check (synthesize observe relation certification initialTable [false] false).isNone
    "incomplete action list was accepted"
  check (synthesize observe relation certification (∅ : Finset (Option Bool))
    actionOrder false).isNone "empty initial support was accepted"
  check (selectedAction observe relation certification actionOrder true
    (∅ : Finset (Option Bool))) "empty memory did not use the true fallback"
  check (!(selectedAction (fun _ : Unit => ()) freeRelation freeCertification
    [false, true] true ({()} : Finset Unit))) "forward list order was ignored"
  check (selectedAction (fun _ : Unit => ()) freeRelation freeCertification
    [true, false] false ({()} : Finset Unit)) "reverse list order was ignored"
  IO.println s!"R1_RUNTIME_PASS: 12 safe transitions, actions={actions.toList}; mixed/incomplete/empty rejected; fallback and list order checked"
