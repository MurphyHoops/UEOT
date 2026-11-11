import UEOTQM.OperationalEquivalence

-- Audit every exported name in the new module's namespace, including generated
-- structure constants. The model theorem is not an input axiom.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc name _ =>
    if name.toString.startsWith "UEOTQM.OperationalEquivalence." then acc.push name else acc
  let names := names.qsort (fun a b => a.toString < b.toString)
  logInfo m!"AUDITED_NAMESPACE_DECLARATIONS {names.size}"
  for name in names do
    elabCommand (← `(command| #print axioms $(mkIdent name)))
