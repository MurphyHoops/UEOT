import UEOT
open Lean Elab Command Meta
run_cmd do
  let env ← getEnv
  let content ← liftIO <| IO.FS.readFile "docs/compression/theory_completion/knowledge/audits/2026-10-10/BINDER_NORMALIZED_TYPE_PAIRS_40.tsv"
  let mut okCount := 0
  let mut errors : Array String := #[]
  for line in (content.splitOn "\n").filter (!·.isEmpty) do
    match line.splitOn "\t" with
    | [a,b] =>
      let na := (a.splitOn ".").foldl (fun n s => Name.str n s) Name.anonymous
      let nb := (b.splitOn ".").foldl (fun n s => Name.str n s) Name.anonymous
      match env.find? na, env.find? nb with
      | some ca, some cb =>
        let eq ← liftTermElabM do
          Meta.isDefEq ca.type cb.type
        if eq then okCount := okCount + 1
        else errors := errors.push s!"TYPE_NOT_DEF_EQ {a} {b}"
      | _,_ => errors := errors.push s!"SYMBOL_MISSING {a} {b}"
    | _ => errors := errors.push "MALFORMED_PAIR"
  liftIO <| IO.println s!"LEAN_META_DEFINITIONAL_TYPE_EQ: {okCount} PASSED, {errors.size} FAILED"
  for e in errors do liftIO <| IO.println e
  if okCount != 40 || !errors.isEmpty then
    throwError "source duplicate type verification failed (expected 40 Lean Meta.isDefEq passes)"
