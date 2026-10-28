#!/usr/bin/env python3
"""Emit closed Lean obligations for exact candidates; no Python verdict is trusted.

`emit()` reproduces registered witnesses. `emit({name: raw})` supports arbitrary
finite dimensions/maps and uses generated safe namespace names. All checks use
kernel `decide`, never native_decide. Optional `tail` is repository proof text,
not accepted from input JSON by the trusted runner.
"""
from fractions import Fraction
from pathlib import Path

from exact_certificates import Source, registered_cases, run

PREFIX = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."


def lean(v):
    if isinstance(v, (tuple, list)):
        return "![" + ", ".join(map(lean, v)) + "]"
    if type(v) is bool:
        return str(v).lower()
    q = Fraction(v)
    return f"({q.numerator} / {q.denominator})" if q.denominator != 1 else str(q.numerator)


def emit(cases=None, *, candidates=None, tail=""):
    registered = cases is None
    cases = registered_cases() if registered else cases
    rows = [(name if registered else f"case_{i}", Source.read(raw),
             candidates[name] if candidates is not None else run(raw))
            for i, (name, raw) in enumerate(cases.items())]
    sizes = sorted({size for _, s, _ in rows for size in (len(s.P), len(s.P[0]), len(s.base))})
    lines = [f"import {PREFIX}RationalConditionedSource",
             f"import {PREFIX}FiniteConditionalStability", "", "/-!",
             "# Computed certificates rechecked by the Lean kernel", "",
             "Generated from frozen finite input tables by emit_lean_witness.py.",
             "Targets are recomputed from their original source. Candidate weights",
             "and separators acquire a conclusion only after kernel `decide` and",
             "the same-source full-path consumer have been checked.", "-/", "",
             f"namespace {PREFIX}FiniteActionCertificateWitnessCheck", "",
             "open MeasureTheory UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl",
             "open UEOT.V3.CoreOperationalAssembly FiniteActionCertificateCheck",
             "open RationalConditionedSourceCheck ConditionedActionTransportCheck",
             "open FiniteActionRealizabilityCheck SameSourceFiniteWindowCheck",
             "open scoped BigOperators", "", "set_option maxRecDepth 16384", ""]
    lines += [f"local instance : MeasurableSpace (Fin {n}) := ⊤" for n in sizes]
    for name, s, result in rows:
        n, a, y = len(s.P), len(s.P[0]), len(s.base)
        lines += ["", f"namespace {name}", "", f"private def P : Fin {n} → Fin {a} → Fin {n} → ℚ := {lean(s.P)}",
                  f"private def base : Fin {y} → Fin {a} → ℚ := {lean(s.base)}",
                  f"private def q : Fin {n} → Fin {y} := {lean(s.q)}",
                  f"private def p0 : Fin {n} → ℚ := {lean(s.p0)}",
                  f"private def deployed : Fin {n} → ℚ := {lean(s.deployed)}",
                  f"private def safe : Fin {n} → Bool := {lean(s.safe)}",
                  f"private def T : ℕ := {s.T}",
                  "private def B := baselineRow P q base",
                  "private def mu := sourceInitial B p0 safe T",
                  "private def R := sourceTarget B safe T", "",
                  "private theorem source_rows : ∀ x a, ValidRow (P x a) := by decide +kernel",
                  "private theorem baseline_rows : ∀ y, ValidRow (base y) := by decide +kernel",
                  "private theorem initial_row : ValidRow p0 := by decide +kernel",
                  "private theorem deployed_row : ValidRow deployed := by decide +kernel", ""]
        if not result["target"]["Z"]:
            lines += ["private theorem conditioning_undefined : sourceMass B p0 safe T = 0 := by decide +kernel", "",
                      "/-- The original source's safety event has exact mass zero. -/",
                      "theorem zero_survival_event :",
                      "    actualSurvivalMass (rationalModel P source_rows) q",
                      "      (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)",
                      "      {x | safe x = true} T = 0 := by",
                      "  rw [← sourceMass_eq_actual P source_rows q base baseline_rows p0 initial_row safe T]",
                      "  exact_mod_cast conditioning_undefined", ""]
        else:
            target = ("targetPath (rowPMF mu target_initial_valid)\n"
                      "        (fun t x => rowPMF (R t x) (target_rows_valid t x)) T")
            actual = ("actualConditionedPrefix (rationalModel P source_rows) q\n"
                      "        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)\n"
                      "        {x | safe x = true} T 0\n"
                      "        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive)")
            lines += ["private theorem source_positive : 0 < sourceMass B p0 safe T := by decide +kernel",
                      "private theorem target_initial_valid : ValidRow mu :=",
                      "  sourceInitial_valid B (baselineRow_nonneg P source_rows q base baseline_rows)",
                      "    p0 initial_row.1 safe T source_positive",
                      "private theorem target_rows_valid : ∀ t x, ValidRow (R t x) :=",
                      "  sourceTarget_valid B (baselineRow_nonneg P source_rows q base baseline_rows) safe T", "",
                      f"private theorem target_is_actual :\n    {target} =\n      {actual} :=",
                      "  sourceTargetPath_eq_actual P source_rows q base baseline_rows p0 initial_row safe T source_positive", ""]
            cert = result.get("certificate")
            if cert and "weights" in cert:
                path = ("(causalLaw (rowPMF deployed deployed_row)\n"
                        "      (riskMicroControlKernel q (fun _ => (rationalModel P source_rows).transitionPMF)\n"
                        "        (timeObservationPolicy (policy weights\n"
                        "          (acceptedWeights deployed mu P R q T weights accepted) 0))) T).map\n"
                        "        (SourcePolicyPathBridgeCheck.eraseActionHistory T)")
                lines += [f"private def weights : Fin T → Fin {y} → Fin {a} → ℚ := {lean(cert['weights']) if s.T else 'Fin.elim0'}",
                          "private theorem accepted : checkPositive deployed mu P R q T weights = true := by decide +kernel", "",
                          f"private theorem output_path :\n    {path} =\n      {target} :=",
                          "  checkPositive_sound deployed mu P R q T weights deployed_row target_initial_valid",
                          "    source_rows target_rows_valid 0 (rationalModel P source_rows)",
                          "    (rationalModel_transitionPMF P source_rows) accepted", "",
                          "/-- The actual returned table implements the original conditional state path. -/",
                          f"theorem output_actual_path :\n    {path} =\n      {actual} :=",
                          "  output_path.trans target_is_actual", ""]
            elif cert:
                path = ("(causalLaw p (riskMicroControlKernel q\n"
                        "        (fun _ => (rationalModel P source_rows).transitionPMF)\n"
                        "        (timeObservationPolicy sigma)) T).map\n"
                        "        (SourcePolicyPathBridgeCheck.eraseActionHistory T)")
                lines += [f"private def separator : Separation (Fin {n}) (Fin {y}) where",
                          f"  time := {cert['time']}", f"  observation := {cert['observation']}",
                          f"  coefficient := {lean(cert['coefficient'])}",
                          f"  bound := {lean(cert['bound'])}", f"  gap := {lean(cert['gap'])}",
                          "private theorem rejected : checkNegative mu P R q T separator = true := by decide +kernel", "",
                          f"private theorem full_path_no_go (p : PMF (Fin {n})) :",
                          f"    ¬ ∃ sigma : ℕ → Fin {y} → PMF (Fin {a}),\n      {path} =\n      {target} :=",
                          "  checkNegative_path_no_go mu P R q T separator target_initial_valid source_rows",
                          "    target_rows_valid (rationalModel P source_rows)",
                          "    (rationalModel_transitionPMF P source_rows) rejected p", "",
                          "/-- The checked separator rules out the original conditional full state path. -/",
                          f"theorem conditional_path_no_go (p : PMF (Fin {n})) :",
                          f"    ¬ ∃ sigma : ℕ → Fin {y} → PMF (Fin {a}),\n      {path} =\n      {actual} := by",
                          "  rintro ⟨sigma, hpath⟩",
                          "  exact full_path_no_go p ⟨sigma, hpath.trans target_is_actual.symm⟩", ""]
            elif "initial_TV_lower_bound" in result:
                path = ("(causalLaw (rowPMF deployed deployed_row) (riskMicroControlKernel q\n"
                        "        (fun _ => (rationalModel P source_rows).transitionPMF)\n"
                        "        (timeObservationPolicy sigma)) T).map\n"
                        "        (SourcePolicyPathBridgeCheck.eraseActionHistory T)")
                lines += ["private theorem initial_mismatch : deployed ≠ mu := by decide +kernel", "",
                          "private theorem initial_pmf_mismatch : rowPMF deployed deployed_row ≠ rowPMF mu target_initial_valid := by",
                          "  intro heq",
                          "  apply initial_mismatch",
                          "  funext x",
                          f"  have h := congrArg (fun p : PMF (Fin {n}) => (p x).toReal) heq",
                          "  simp only [rowPMF_toReal] at h",
                          "  exact_mod_cast h", "",
                          "/-- Future actions cannot replace the required initial preparation. -/",
                          "theorem conditional_path_no_go :",
                          f"    ¬ ∃ sigma : ℕ → Fin {y} → PMF (Fin {a}),\n      {path} =\n      {actual} := by",
                          "  rintro ⟨sigma, hpath⟩",
                          "  have htarget := hpath.trans target_is_actual.symm",
                          "  exact initial_pmf_mismatch ((FinitePolicyPathCheck.specified_policy_path_iff",
                          "    (rationalModel P source_rows) q sigma (rowPMF deployed deployed_row)",
                          "    (rowPMF mu target_initial_valid) (fun t x => rowPMF (R t x) (target_rows_valid t x)) T).mp htarget).1", ""]
        lines += [f"end {name}", ""]
    if registered:
        lines += [Path(__file__).with_name("registered_checks.lean.txt").read_text()]
    lines += [tail, f"end {PREFIX}FiniteActionCertificateWitnessCheck", ""]
    return "\n".join(lines)


if __name__ == "__main__":
    core = Path(__file__).resolve().parents[5]
    output = core / "UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteActionCertificateWitness.lean"
    output.write_text(emit())
    print(output)
