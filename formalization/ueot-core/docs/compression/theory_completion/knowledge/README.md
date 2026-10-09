# UEOT Formal Knowledge & Research Governance (FKRG) — operational v1

**Authority:** no new mathematical truth or second counted ledger. Live Lean + frozen Core source and ledger + canonical Git main remain authoritative. Mission ownership and open ports remain in the existing Track TC mission / Issue #302.

## Problem and non-duplication design

The current UEOT source tree has 633 first-party Lean modules. The existing UMC V4 source DAG contains *module imports*, not proof-level dependencies; Core 106 elaboration audit covers the frozen 106 rather than all new declarations. SISC already has deterministic finite-probe bound, RLSR already has true program-reconstruction theorems, and P-CTL-01 already has history-dependent causal optimality. New workers must query them rather than re-prove them.

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

- The 5,339+ records are *lexical source declaration candidates* (theorem/lemma/def/class/structure/inductive), not 5,339 elaborated and independently audited theorems.
- `name_candidate` is assembled using source namespace nesting; Lean `lean-check` must confirm it resolves. A syntax parser cannot establish kernel identity/typed semantic match by itself.
- `header_excerpt` is raw source context, NOT elaborated Lean type. `#check` output is the typed kernel resolution for one symbol; no equivalence inference from search scores.
- `impact` reports reverse **module import** dependencies, NOT actual per-theorem proof dependencies. Do not count module imports as proof dependence. Frozen Core 106 elaborated declaration DAG remains separate.
- Search/FTS5 similarity never proves equivalence. Preflight with all symbols found means `CANDIDATES_FOUND_KERNEL_CHECK_REQUIRED`, NOT proof complete and NOT a scientific closure claim.
- `status` is offline; its origin/main reference is cached, NOT a remote CI check. New chat must still run `git fetch` and consult live GitHub Issue/PR/CI for authoritative remote state.
- FKRG V1 does not automatically infer new mathematics or prove a theorem was absent. Human/Lean scientific review must still discharge typed hypotheses and no-go contradictions.

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

`test_fkrg.py` includes positive source-reuse checks, mandatory task-reuse references and negative tests for stale source fingerprint and unknown symbols.

## CI rules

For routine research PRs: run `python3 .../test_fkrg.py`. A separate base-authorized governance PR can make this mandatory in existing Compression Guard. The guard must run from repository-root after checkout, with no need for Lean compilation or generated SQLite artifacts committed to Git.

**Completion claim:** FKRG search/preflight/recovery foundation operational; mathematical-source semantic completeness, general Lean declaration dependency graph, remote CI enforcement and formal anti-duplication equivalence checking are distinct higher-level gates.

**Cache upgrade (FKRG V2):** old V1 SQLite caches are deliberately rejected as `STALE_INDEX`. Rebuild with `fkrg.py build`; the extractor fingerprint includes both `fkrg.py` and its imported `audit_umc_local.py` Lean comment parser. Source-private names are indexed for discovery but not advertised as public Lean constants.
