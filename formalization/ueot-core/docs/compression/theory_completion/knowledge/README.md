# UEOT Formal Knowledge & Research Governance (FKRG) — operational v1

**Authority:** no new mathematical truth or second counted ledger. Live Lean + frozen Core source and ledger + canonical Git main remain authoritative. Mission ownership and open ports remain in the existing Track TC mission / Issue #302.

## Problem and non-duplication design

The statistical-risk source census contains **646 bundled Lean modules: 635 UEOT-maintained and 11 adapted upstream modules**. Its five added modules have passed the pinned Lean build, native export and independently executed fixed verifier against the source hashes recorded in the fifth overlay. These are source-bound local verification results, not a claim about a later canonical Git or CI state. The immutable 2026-10-10 audit remains 633 = 622 + 11; later source changes are preserved as additive pinned overlays in the [proof reuse navigator](reuse/README.md). The existing UMC V4 source DAG records *module imports*. Compiled direct theorem dependencies are a distinct evidence layer, and the Core 106 elaboration audit covers its frozen endpoint scope. SISC already has deterministic finite-probe bounds, RLSR has true program-reconstruction theorems, and P-CTL-01 has history-dependent causal optimality. Query these before proposing a missing theorem.

The [44-file reading guide](CANONICAL_READING_GUIDE_V1.md) links the existing foundations, compression generators, same-source control/viability bridges, Objecthood/TC and scientific boundaries. It retains all dependencies and includes the new calibration-to-actual-path finite-risk chain; it is a reading itinerary rather than a replacement 44-module library.

FKRG is a **disposable source-derived search cache + enforced task reuse preflight**. It borrows the existing UMC `no_lean_comments` tokenizer; it never replaces the Core ledger, Compression ledger, P12 boundaries, main Git status or any existing Issue.

## Running (repository root)

```bash
python3 formalization/ueot-core/docs/compression/theory_completion/knowledge/fkrg.py build
python3 formalization/ueot-core/docs/compression/theory_completion/knowledge/fkrg.py status
python3 formalization/ueot-core/docs/compression/theory_completion/knowledge/fkrg.py find "stochasticFuture"
python3 formalization/ueot-core/docs/compression/theory_completion/knowledge/fkrg.py find "repair program" --details
python3 formalization/ueot-core/docs/compression/theory_completion/knowledge/fkrg.py show viableSourceAction
python3 formalization/ueot-core/docs/compression/theory_completion/knowledge/fkrg.py lean-check UEOT.V3.FiniteDiscountedControl.CausalPolicy.infiniteValue_le_optimal
python3 formalization/ueot-core/docs/compression/theory_completion/knowledge/fkrg.py impact UEOT.V3.ViabilitySource.p_per_03
python3 formalization/ueot-core/docs/compression/theory_completion/knowledge/fkrg.py preflight --task UMC-R3-CAUSAL-RESTRICTION
python3 formalization/ueot-core/docs/compression/theory_completion/knowledge/test_fkrg.py
```

Default cache: `/tmp/ueot-fkrg-index.sqlite3` (override via `--db` or `UEOT_FKRG_DB`). **Never commit SQLite or treat it as a provenance record.**

## Explicit epistemic limits

- The cache records are *lexical source declaration candidates* (theorem/lemma/def/class/structure/inductive), not independently audited theorems. Rebuild and consult `status` for the current declaration count and exact source fingerprint.
- `name_candidate` is assembled using source namespace nesting; Lean `lean-check` must confirm it resolves. A syntax parser cannot establish kernel identity/typed semantic match by itself.
- `header_excerpt` is raw source context, NOT elaborated Lean type. `#check` output is the typed kernel resolution for one symbol; no equivalence inference from search scores.
- `impact` reports reverse **module import** dependencies, NOT actual per-theorem proof dependencies. Do not count module imports as proof dependence. Frozen Core 106 elaborated declaration DAG remains separate.
- Search/FTS5 similarity never proves equivalence. Preflight with all symbols found means `CANDIDATES_FOUND_KERNEL_CHECK_REQUIRED`, NOT proof complete and NOT a scientific closure claim.
- `status` is offline; its origin/main reference is cached, NOT a remote CI check. New chat must still run `git fetch` and consult live GitHub Issue/PR/CI for authoritative remote state.
- FKRG V1 does not automatically infer new mathematics or prove a theorem was absent. Human/Lean scientific review must still discharge typed hypotheses and no-go contradictions.

The scoped UMC full audit now enumerates theorem constants by the compiler's physical `source_module` and rejects nonstandard transitive axioms with `Lean.collectAxioms`. Its native scope includes private and generated theorem constants; it reports lexical public candidates separately. This improves that audit's authority without claiming a complete source-declaration parser or replacing the disposable search cache.

For the statistical-risk layer, [STATISTICAL_RISK_NATIVE_V1.json](reuse/STATISTICAL_RISK_NATIVE_V1.json) records **126 compiler-owned theorem constants: 73 confirmed public source candidates, 11 private constants and 42 other nonprivate constants**. Every one of the 126 records contains `name`, `source_module`, `is_private`, `level_parameters`, the `ppExpr` type display, `direct_constants`, `direct_theorem_constants` and transitive `axioms`. The separate 73-node public list additionally carries `source_theorem_deps`, restricted to registered public theorem targets; its **91 direct edges** do not count private helpers, definitions or unregistered Mathlib theorems. Their actual constant references remain available in the full native records. A zero registered-edge count therefore does not mean that a proof uses no helpers. All 126 pass the standard-axiom allowlist; type displays are not lossless expression encodings. The five-layer registered graph contains **3,938 public source nodes**, a different scope from lexical declaration counts reported by the disposable cache.

The new statistical endpoints discharge calibration from fixed finite row-sampling experiments with the exact source-row laws and row-wise IID samples; the generic theorem permits dependence across different rows. One measurable simultaneous event supports subsequently chosen representations and common history policies satisfying the stated deterministic checks. Tests, source law, sample size, horizon and concentration radii remain fixed before those samples. The sparse-test route compares true representative rows with a two-sided sampling contribution; the all-event route builds empirical reference PMFs and uses a one-sided true-to-empirical contribution plus a checked coarse-fit error. Microscopic failure risk additionally requires a specified failure label and conservative coarse envelope. The product-sampling witness constructs these mathematical premises and proves a nontrivial two-step bound; physical access to such source-row experiments, general joint training-and-deployment probabilities and all-time safety do not follow from the build or native census.

## Required startup/recovery protocol (every new chat/agent)

1. Inspect local `git status`, HEAD, branch and upstream; fetch/compare live `origin/main`, check Issue #302 and relevant PR/Actions; never overwrite running worktrees.
2. Read current TC mission, `FKRG_TASKS.json`, prior research results and scoped task contract.
3. `fkrg.py build` then `status`; if stale, rebuilding is required; do not trust stale caches.
4. `preflight --task ...`; inspect returned exact symbol paths and actual Lean `lean-check` for important declarations.
5. Search neighboring S/H/X/O/Core/UMC concepts and no-go examples, formulate **the smallest missing lemma or adapter**. If an existing stronger lemma resolves the obligation, reuse instead.
6. Focused compile, full package build for semantic changes, standard-only axiom audit, governance negative controls, reviewer check.
7. Write exact Git commit and task evidence, note negative/failed approaches and the exact next proof. Do not silently mark `FULL` when a tracked scientific port remains open.

## Task authority and schema

`FKRG_TASKS.json` is a **small, human-reviewed snapshot of proposed open UMC tasks**, not a live authoritative ledger. Its IDs remain subordinate to existing GitHub Issue #302. Fields: status, precise scope, `reuse_symbols`, new obligations, known boundaries, next action. The mission/Issue is always consulted before task creation, update or promotion.

`test_fkrg.py` includes source-reuse checks, mandatory task-reuse references, current-DAG freshness, native JSON scope checks and adversarial cases. A complete fast-audit integration test runs the real `audit(False)` and independently checks that historical receipts keep the same paths and bytes. Receipt-writer tests also exercise the write boundary directly. The separate current-DAG integration test retains negative fixtures for new/deleted modules, source-byte drift, incorrect counts and an import graph that is not closed.

## CI rules

For routine research PRs, run `python3 .../test_fkrg.py` and the existing reuse/preflight tests. These offline checks run from repository root, without committing SQLite artifacts. The existing Compression Guard runs its configured mandatory tests; the native full audit additionally requires the pinned Lean toolchain and a successful current-source build.

`audit_umc_local.py` requires a fetched `origin/main` and pins its resolved commit for the immutable-base scope comparison. That commit must be an ancestor of the candidate HEAD; if local `main` exists, it must be an ancestor of the selected remote commit. Missing or inconsistent refs are rejected, without falling back to local `main` or HEAD. These offline checks establish consistency of the available refs, not that the remote has not advanced since the last fetch; fetch and align the candidate before auditing. The audit never updates either branch. Its default and fast runs do not rewrite historical receipts. Use `--full --output /path/to/new-receipt.json` to request a new complete receipt; the historical receipt path is rejected. Full verification builds `UEOT` before inspecting compiled source modules, so a stale `.olean` cannot silently stand in for changed source.

**Completion claim:** search/preflight/recovery, pinned proof reuse and scoped native UMC axiom checks each retain their declared scope. Scientific completeness, empirical calibration coverage and mathematical independence are separate obligations; none is inferred from a source count, a clean build or the 44-file reading route.
