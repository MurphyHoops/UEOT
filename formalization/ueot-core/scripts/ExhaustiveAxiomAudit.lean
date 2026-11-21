import UEOT
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Exhaustive Kernel Axiom Audit for UEOT Core

Scans every non-internal declaration defined in any `UEOT.*` module in the
compiled environment and verifies that its transitive axiom closure is a subset
of Lean's standard logical foundation `{propext, Classical.choice, Quot.sound}`
(no `sorryAx`, no `Lean.ofReduceBool` / `Lean.trustCompiler` from `native_decide`,
no custom `axiom` or `opaque` proof escapes, and no `unsafe` declarations).
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let std : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut nThm : Nat := 0
  let mut nDef : Nat := 0
  let mut nAx : Nat := 0
  let mut nOpaque : Nat := 0
  let mut nUnsafe : Nat := 0
  let mut total : Nat := 0
  let mut nBad : Nat := 0
  let mut nSorry : Nat := 0
  let mut nonstd : List Name := []
  let mut samples : List (Name × List Name) := []
  let mut modsSeen : NameSet := {}
  for (n, ci) in env.constants.map₁.toList do
    match env.getModuleIdxFor? n with
    | none => continue
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      unless (`UEOT).isPrefixOf m do continue
      if n.isInternal then continue
      modsSeen := modsSeen.insert m
      total := total + 1
      match ci with
      | .thmInfo _ => nThm := nThm + 1
      | .defnInfo _ => nDef := nDef + 1
      | .axiomInfo _ => nAx := nAx + 1
      | .opaqueInfo _ => nOpaque := nOpaque + 1
      | _ => pure ()
      if ci.isUnsafe then nUnsafe := nUnsafe + 1
      let axs ← liftCoreM (Lean.collectAxioms n)
      let extra := List.filter (fun a => !std.contains a) axs.toList
      if !extra.isEmpty then
        nBad := nBad + 1
        if extra.contains `sorryAx then nSorry := nSorry + 1
        for a in extra do
          unless nonstd.contains a do nonstd := a :: nonstd
        if samples.length < 25 then samples := (n, extra) :: samples
  logInfo m!"EXHAUSTIVE_AXIOM_AUDIT modules={modsSeen.size} constants={total} theorems={nThm} defs={nDef} axiomDecls={nAx} opaque={nOpaque} unsafe={nUnsafe}"
  logInfo m!"nonstandard_users={nBad} sorryAx_users={nSorry} nonstandard_axioms={nonstd}"
  for (n, e) in samples do
    logInfo m!"  NONSTANDARD {n}: {e}"
  if nBad > 0 || nAx > 0 || nOpaque > 0 || nUnsafe > 0 then
    throwError m!"EXHAUSTIVE_AXIOM_AUDIT_FAILED: nonstandard_users={nBad} axiomDecls={nAx} opaque={nOpaque} unsafe={nUnsafe}"
