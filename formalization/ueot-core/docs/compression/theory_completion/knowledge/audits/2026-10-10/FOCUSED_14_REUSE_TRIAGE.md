# Focused duplication follow-up: 14 independent-route theorem groups

**Scope:** read-only, compilable, non-destructive proof reuse experiment.
**Baseline:** UEOT source SHA-256 matches frozen scan on main
48b582beabec2ebae61ab0d51081b83356fcb3e1.
**Execution main:** 47c06dae07ff120cf28de1e60b59b29e759164e1.
**Result:** 14/14 direct proof replacements accepted by Lean in seven
temporary module copies; no source theorem or ledger changed.

## Method and independent repeatability

The tracked verifier VERIFY_14_REUSE_PROBES.py validates SHA-256 for all
seven original source modules, copies them to a system temporary directory,
retains the exact theorem statements and replaces selected proof bodies by
direct exact applications of already compiled base theorems. Required new
imports are inserted only in those temporary copies. Each copy is compiled
using build-aware lake lean, not a shallow source-string check. It writes
FOCUSED_14_REUSE_PROBE_RECEIPT.json with all seven results, source hashes,
and compiler return codes; no generated Lean source touches the repository.

Run from repository root:

    python3 formalization/ueot-core/docs/compression/theory_completion/knowledge/audits/2026-10-10/VERIFY_14_REUSE_PROBES.py

All seven full temporary module compilations passed. The sum of the
temporary modules' original-minus-replaced physical line counts is **237**.
This is a mechanical counterfactual, not the number of safely removable
research lines. The existing independent Lean Meta.isDefEq 40/40 type
comparison is also retained.

## Every one of the 14 formerly non-direct-reuse groups

| Terminal theorem name | Existing source theorem reused | Outcome | Scientific interpretation |
|---|---|---|---|
| StatisticalDefect.tvDist_symm | InformationPacking.tvDist_symm | PASS | LOW RISK: two separately implemented proofs of TV symmetry |
| p_goa_01_via_occupationLimit | FiniteCesaroInvariant.p_goa_01 | PASS | GENERATOR: M-OI independent finite occupation bridge |
| feller_invariant_of_occupation_tendsto | PersistenceOccupation.FellerOccupationSystem.invariant_of_occupation_tendsto | PASS | GENERATOR: generic observable residual specialization |
| p_per_02_via_occupationLimit | PersistenceOccupation.FellerOccupationSystem.p_per_02 | PASS | GENERATOR: Feller occupation-limit bridge |
| processInterface_approx_via_twoStage | ProcessInterface.p_api_01_approx | PASS | GENERATOR: M-TC approximate two-stage transport |
| processInterface_exact_source_via_twoStage | ProcessInterface.p_api_01_exact | PASS | GENERATOR: M-TC exact two-stage transport |
| dynamicsCrossScale_approx_via_twoStage | DynamicsCrossScale.p_dyn_04_cross_scale_tv | PASS | GENERATOR: M-TC common-source cross-scale TV |
| dynamicsCrossScale_exact_via_factor | DynamicsCrossScale.p_dyn_04_exact_intertwining | PASS | GENERATOR: exact commuting-factor transport |
| p_dyn_03_via_multiplicative_chain | PathError.p_dyn_03_finite_path_error | PASS | GENERATOR: multiplicative common-mass renewal |
| p_ali_02_core_via_mva | AlignmentParentValue.p_ali_02_core | PASS | GENERATOR: generic directional-score margin |
| p_ali_02_via_mva | AlignmentParentValue.p_ali_02 | PASS | GENERATOR: score and chain-rule reconstruction |
| bellman_valueError_le_residual_via_mcf | FiniteDiscountedControl.Model.valueError_le_residual | PASS | GENERATOR: ContractiveWith residual interface |
| bellman_fixedPoint_unique_via_mcf | FiniteDiscountedControl.Model.fixedPoint_unique | PASS | GENERATOR: ContractiveWith uniqueness interface |
| flip_physical_seed_cannot_select_two_programs | same_physical_seed_program_reconstruction_no_go | PASS | ALIAS: both already depend on the generic no-program-decoder theorem |

### Proper scientific judgment

Of the 37 same-type theorem clusters in the original scan, 23 already
included in-cluster direct proof reuse (26 direct edges); the remaining
14 had no in-cluster direct proof reference, and all 14 now passed
temporary direct-reuse compilation.

This does **not** make those 14 invalid mathematics. Twelve have a
research reason to preserve the alternative derivation: they are
supposed to demonstrate that the Compression generic generator
independently yields an existing frozen Core conclusion. Replacing
such a proof by the Core theorem would invalidate that scientific
evidence even though the final theorem still type-checks.

One is a small, genuinely duplicate helper implementation
(StatisticalDefect TV symmetry), appropriate for a minimally scoped
source refactor that keeps both public theorem names. One pair simply
publishes the same generic no-go under distinct domain terms and is
already an indirect reuse; keep API names if callers need them.

These 12/1/1 research categories are an expert triage judgment, **not**
a Lean proof of generator minimality, unique scientific necessity,
or safe cross-module deletion.

## Recommendation and strict gate

1. Consolidate the duplicated TV symmetry helper first, preserving
   exported names and verifying downstream builds and exact-head CI.
2. Explicitly label the twelve generative rederivations as separate
   generator witnesses, with links to source theorem and generic
   abstraction. They should not be counted as independent Core theorems.
3. Add FKRG theorem-type equivalence plus actual proof-dependency
   preflight; when a new exact-type public declaration appears, require
   an alias, generator-witness, bridge, or formally substantiated
   different-assumptions classification.
4. Audit the fifteen separate approximate-type pairs with hypothesis
   direction and semantic typing; they were not in the exact 40/40
   definitional-equality set.

No source Lean files, counted Core 106 statements, Compression generator
ledger, CI, or scientific port statuses are modified in this report.
