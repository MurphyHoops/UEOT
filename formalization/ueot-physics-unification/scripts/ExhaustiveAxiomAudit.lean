import UEOTPhysicsUnification
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Exhaustive Pure-Kernel Axiom Audit for `UEOTPhysicsUnification`

Verifies that every non-internal declaration in `UEOTPhysicsUnification.*` depends only
on Lean's standard logical foundation `{propext, Classical.choice, Quot.sound}`
(zero `sorryAx`, zero `Lean.ofReduceBool` / `Lean.trustCompiler`, zero custom `axiom` or `opaque`).
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
  let mut modsSeen : NameSet := {}
  for (n, ci) in env.constants.map₁.toList do
    match env.getModuleIdxFor? n with
    | none => continue
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      unless (`UEOTPhysicsUnification).isPrefixOf m do continue
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
  logInfo m!"UNIFICATION_AXIOM_AUDIT modules={modsSeen.size} constants={total} theorems={nThm} defs={nDef} axiomDecls={nAx} opaque={nOpaque} unsafe={nUnsafe} nonstandard_users={nBad} sorryAx_users={nSorry}"
  if nBad > 0 || nAx > 0 || nOpaque > 0 || nUnsafe > 0 then
    throwError m!"UNIFICATION_AXIOM_AUDIT_FAILED: nonstandard_users={nBad} axiomDecls={nAx} opaque={nOpaque} unsafe={nUnsafe}"
