import UEOT.V3.Compression.TheoryCompletion
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let sourceModules : Array Name := #[
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteConditionalStability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteConditionalStabilityWitness,
  ]
  for sourceModule in sourceModules do
    unless env.header.moduleNames.contains sourceModule do
      throwError s!"UMC_COMPILED_SOURCE_MODULE_MISSING {sourceModule}"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let .thmInfo _ := info then
      if let some idx := env.getModuleIdxFor? name then
        let sourceModule := env.header.moduleNames[idx]!
        if sourceModules.contains sourceModule then
          let actual ← Lean.collectAxioms name
          let unexpected := actual.filter fun ax => !allowed.contains ax
          unless unexpected.isEmpty do
            throwError s!"UMC_NONSTANDARD_AXIOM {name}: {unexpected}"
          rows := rows.push <| Json.mkObj [
            ("name", toJson name.toString),
            ("source_module", toJson sourceModule.toString),
            ("is_private", toJson (Lean.privateToUserName? name).isSome),
            ("axioms", toJson (actual.map Name.toString))]
  unless rows.size > 0 do throwError "UMC_NATIVE_SCOPE_EMPTY"
  let report := Json.mkObj [
    ("schema", toJson "UMC_NATIVE_AXIOM_CENSUS_V1"),
    ("source_modules", toJson (sourceModules.map Name.toString)),
    ("theorems", toJson rows)]
  liftIO <| IO.println ("UMC_NATIVE_AUDIT_JSON " ++ report.compress)
