# Focused duplication follow-up: 14 independent-route theorem groups

**Scope:** read-only, compilable, non-destructive proof reuse experiment.
**Baseline:** immutable source SHA-256 values are independently pinned to main
48b582beabec2ebae61ab0d51081b83356fcb3e1.
**Execution main:** 47c06dae07ff120cf28de1e60b59b29e759164e1.
**Result:** 14/14 direct proof replacements accepted by Lean in seven
temporary module copies; no source theorem or ledger changed.

## Method and independent repeatability

The tracked verifier VERIFY_14_REUSE_PROBES.py validates SHA-256 for all
seven original source modules against expected digests **hard-coded from the
immutable Git commit**, not reloaded from the mutable co-located audit CSV.
It checks and caches **all seven source files before any temporary file is
created or any Lean compilation begins**, so even a mismatch in the last
source file fails immediately. It then copies sources to a system temporary
directory, retaining the exact theorem statements and replaces selected proof bodies by
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
| p_ali_02_core_via_mva | AlignmentParentValue.p_ali_02_core | PASS | RETAINED ADAPTER (P-ALI-02): experimental M-VA score-level reconstruction, not a counted generator mapping |
| p_ali_02_via_mva | AlignmentParentValue.p_ali_02 | PASS | RETAINED ADAPTER (P-ALI-02): M-VA chain-rule reconstruction only, not a counted generator mapping |
| bellman_valueError_le_residual_via_mcf | FiniteDiscountedControl.Model.valueError_le_residual | PASS | RETAINED ADAPTER (P-CTL-01): experimental M-CF residual calculus, not a counted generator mapping |
| bellman_fixedPoint_unique_via_mcf | FiniteDiscountedControl.Model.fixedPoint_unique | PASS | RETAINED ADAPTER (P-CTL-01): M-CF uniqueness experiment, not a counted generator mapping |
| flip_physical_seed_cannot_select_two_programs | same_physical_seed_program_reconstruction_no_go | PASS | ALIAS: both already depend on the generic no-program-decoder theorem |

### Proper scientific judgment

Of the 37 same-type theorem clusters in the original scan, 23 already
included in-cluster direct proof reuse (26 direct edges); the remaining
14 had no in-cluster direct proof reference, and all 14 now passed
temporary direct-reuse compilation.

This does **not** make those 14 invalid mathematics. The canonical
Compression Ledger distinguishes **eight** source-facing routes within the
counted **M-OI-01 and M-TC-01 generator families** (three M-OI module
results, including a supporting intermediate Feller lemma; five M-TC
mappings). Replacing them by the frozen terminal theorems would undermine
the registered *independent generic-to-source derivation evidence*, even
though the theorem statements still type-check.

The **other four** (two P-ALI-02/M-VA and two P-CTL-01/M-CF) belong to
**retained_adapter** source obligations and experimental abstractions,
not counted Compression generator mappings. They can still be valuable
alternative proof methods, but have no M-ID promotion by this audit.
See docs/compression/COMPRESSION_LEDGER.yaml, generator mappings M-OI-01
and M-TC-01, and retained_adapter P-ALI-02 / P-CTL-01.

One case is a separately implemented TV-symmetry helper, a viable
low-risk reuse prototype. One pair publishes a shared physical-seed
no-go under different names and is already indirect reuse.

The **8 counted-family / 4 retained-adapter / 1 low-risk helper / 1
domain-named alias** split is an audit classification grounded in the
ledger, **not** a proof of generator minimality or physical necessity.

## Recommendation and strict gate

1. Consolidate the duplicated TV symmetry helper first, preserving
   exported names and verifying downstream builds and exact-head CI.
2. Tag the eight M-OI/M-TC mapped results as counted-family witness
   derivations (including the supporting intermediate Feller lemma), and
   separately tag four P-ALI-02/P-CTL-01 M-VA/M-CF results as
   uncounted experimental retained adapters. Link both to their exact
   source theorem; neither category increments Core-106 theorem counts.
3. Add FKRG theorem-type equivalence plus actual proof-dependency
   preflight; when a new exact-type public declaration appears, require
   an alias, generator-witness, bridge, or formally substantiated
   different-assumptions classification.
4. Audit the fifteen separate approximate-type pairs with hypothesis
   direction and semantic typing; they were not in the exact 40/40
   definitional-equality set.

No source Lean files, counted Core 106 statements, Compression generator
ledger, CI, or scientific port statuses are modified in this report.
