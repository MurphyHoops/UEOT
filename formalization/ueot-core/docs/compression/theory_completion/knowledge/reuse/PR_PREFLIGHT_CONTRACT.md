# FKRG PR delta preflight — non-promotional, base-versus-candidate gate

Status: uncounted research tool. This script does not authorize science
status, mutate old Core or Compression files, or replace Lean proof checking.

## Purpose

The pinned 2026-10-10 full-source audit must FAIL CLOSED if the 633 source
files, pinned Mathlib, toolchain or counting ledger change. Conversely, a
new Lean theorem PR MUST change the source set. Running the pinned snapshot
navigator as a blanket CI gate would therefore block every legitimate
future source addition. The correct execution context is the immutable
Git BASE and HEAD commit objects, not a historical fixed-source
snapshot mistaken for the new version.

pr_preflight.py reads the full Lean source collection from the two Git
commits through git archive; it does not use working-tree files for either
tree. The declaration scanner reuses the existing FKRG comment-removal,
namespace and declaration recognizers, with PR-specific handling for
noncomputable section scopes and Unicode Lean public identifier spelling.
Any theorem/lemma command outside supported lexical syntax FAILS CLOSED
instead of vanishing from the review report. It produces:

- exact base and candidate source tree commit identifiers;
- all changed UEOT Lean source paths and module/declaration counts;
- genuinely new public lexical theorem/lemma names, excluding names that
  already existed in base; private declarations are excluded;
- up to five previously existing name-similar public theorem candidates
  for each new declaration, labeled LEXICAL_ONLY;
- mandatory TYPED_REUSE_REVIEW_REQUIRED for new public names; no
  Type isDefEq or mathematical implication claim from string similarity.

The validator rejects unresolved/non-commit revisions, corrupted/missing
root UEOT sources and duplicate fully-qualified lexical theorem names.
It does not falsely treat alternate proofs or source terms with different
names as necessarily redundant.

Run from repository root:

    P=formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse
    python3 "$P/pr_preflight.py" --repo-root . \
      --baseline-ref origin/main --candidate-ref HEAD \
      --report /tmp/UEOT-FKRG-NewTheorems.json
    python3 "$P/test_pr_preflight.py"

For GitHub Actions, the base must be the precise pull_request.base.sha
or github.event.before for pushes to main. For a workflow_dispatch
without a meaningful prior ref, use HEAD as both arguments; the result
must state zero change. Never treat origin/main during a PR as stable
if the branch base has advanced.

## Strictness versus scientific freedom

CI can mandate running this inspection and publishing the per-PR
report, but should not auto-reject a proposed theorem because a heuristic
name is similar to one already compiled. A reviewer must check actual
Lean statements, hypothesis strength, import/type compatibility and,
where relevant, independence of a generic compression generator.

These checks are useful gates for discovery and traceability. They are
not a formal implementation of mathematical duplicate detection. A
separate contract to require a signed justification for every new
theorem would need governance and cross-team agreement; this stage does
not silently impose that expensive burden on unrelated Core/QM tracks.

## Independent negative tests

Fixture tests use temporary isolated Git repositories and actually commit
baseline and candidate objects. They cover fresh theorem detection,
cross-namespace same short names, unchanged public names after proof edit,
private theorem exclusion, duplicate public fully-qualified names,
deleted Lean modules, invalid revisions, nested noncomputable section
closures, Unicode and attribute-prefixed theorem identifiers, unsupported
public theorem syntax, and uncommitted worktree separation. No real UEOT Lean file is edited by the tests.

On future changes to the parser, treat all lexical results as candidates
until Lean compilation and proof/dependency inspection are complete.
