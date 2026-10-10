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
noncomputable/public/meta section scopes (including attribute-prefixed
public meta section), public/nonrec declaration modifiers, and complete
Unicode-qualified Lean theorem names including !/? suffixes, escaped-name
contents such as comment/syntax delimiters protected BEFORE applying the
historical comment and quotation masks, scoped
in-command theorem/lemma wrappers (open/include/omit)
and explicit _root_. qualification, including partial/compound
qualified namespace-end and named-section scope restoration. Escaped
namespace names containing whitespace are preserved as full Lean identifiers;
residual namespace/section/end/mutual commands after a parsed scope
fail closed rather than silently altering the next theorem FQN.
Any theorem/lemma command outside supported lexical syntax FAILS CLOSED
instead of vanishing from the review report. It produces:

- exact base and candidate source tree commit identifiers;
- all changed UEOT Lean source paths and module/declaration counts;
- genuinely new public lexical theorem/lemma names, excluding names that
  already existed in base; private declarations are excluded, including standalone modifiers separated by attribute lines;
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
closures, public/nonrec declaration modifiers, public section/attribute
section and meta section scope handling, full Unicode hierarchical
names and !/? suffixes, scoped in-command theorem wrappers,
including include/omit, mutual...end scope balancing, escaped
reserved-word identifiers, private-section visibility as defensive lexical
handling (the pinned compiler rejects a bare private section opener), explicit
_root_. qualified names, qualified end B.C consuming two namespace
components, same-line theorem/lemma commands fail closed even after a parsed
declaration or after an otherwise-unparsed prefix command, qualified
end A.B can close nested sections A and B, escaped identifiers with
whitespace and escaped dots in leaf names, same-line namespace/end commands, valid CLI root,
unsupported public theorem syntax, and uncommitted worktree separation. No real UEOT Lean file is edited by the tests.

On future changes to the parser, treat all lexical results as candidates
until Lean compilation and proof/dependency inspection are complete.


## Scope edge regressions after Codex review

Validated against pinned Lean using actual lake lean:

- namespace A; namespace _root_.B creates A._root_.B. End B leaves
  A._root_, and end _root_ restores A.
- section A; anonymous section; section B; end A.B is rejected by Lean.
  The scanner also refuses it rather than silently skipping an anonymous
  section to fabricate a valid qualified ending.
- The valid sequential closing end B; end; end A restores the namespace.

Unrecognized command syntax must fail closed rather than omitting proofs.


## Git symlinks and multiline attributes

The PR census rejects symlinks in the UEOT source archive, including
tracked Lean file aliases, so checkout-resolved modules cannot be silently
absent from the audit. Standalone privacy prefixes are retained across
multiline attribute blocks until the subsequent theorem is parsed.
Unsupported syntax on a closing attribute line fails closed.


## Attribute payload privacy and Lean command quotations

Visibility is determined from real modifier tokens outside attribute
payloads, not substring matches. Quoted Lean command syntax is source data,
not an executable theorem declaration; single- and multiline quotation
contents are masked before lexical command-token detection. Unsupported
unterminated quotations fail closed.

## Syntax quote hardening

The lexical scanner masks syntax quotations as inert source and separately
recognizes quoted string and Lean character literals, including parentheses
inside character literals. These must not affect quotation nesting depth or
create phantom public declarations. Unbalanced quotations fail closed.

## Multiline Lean escaped names

A `«... »` escaped identifier component may legally contain a physical
newline. The scanner now combines only those physical lines while retaining
the original start-line provenance; the resulting fully qualified Lean name
keeps the literal newline. A second `«` inside an escaped identifier
is literal name content, not a nested delimiter. Open escaped identifiers
fail closed. This was
confirmed with the pinned Lean compiler, not only with lexical fixtures.

Character literals containing `«` or `»` are skipped as values during
escaped-name delimiter tracking, preventing false name buffering.

## Indented multiline command headers

Lean accepts namespace/theorem/lemma names on a later properly indented
physical line. The PR scanner joins required name continuations, and
optionally named section/end continuations only when the next indented
line is an identifier rather than a command. An unindented namespace
continuation is invalid in the pinned Lean compiler and fails closed.


Attribute delimiter safety: the PR-specific attribute token matcher recognizes
closing brackets inside Lean escaped identifiers and quoted strings as payload,
not attribute endings. Standalone attributes, inline declaration modifiers,
privacy classification and multiline attribute depth use the same lexically
aware interpretation. Valid attribute cases are compiled in the pinned Lean
toolchain, with committed Git-tree regression fixtures.
