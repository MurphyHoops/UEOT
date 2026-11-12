# Contract for the independent book-3.9 verifier

Implementation owned by C: `physics/qm/book/build/verify_v3_9_increment.py`. It imports no production metadata generator and only writes its requested output report.

Invocation:

```bash
python3 physics/qm/book/build/verify_v3_9_increment.py \
  --repo-root . --output PATH_TO_REPORT.json --require-complete
```

Without `--require-complete`, missing integration metadata or evidence yields `CONTENT_PASS_METADATA_PENDING` and exit 0. With that option, the same pending state exits 3. Actual changed historical content or invalid evidence is `FAIL` and exit 2 in both modes. A completed check is `PASS` and exit 0.

## Required current publication structure

- `CHAPTER_DOSSIER.json`: edition 3.9; the prior 182 numbered result dictionaries and their order are unchanged, followed by exactly `P-MICRO-04,P-OPT-04,P-MICRO-05,C-MICRO-02,P-ROB-03,C-ROB-02`. Each new dictionary declares chapter 68, its lowercase anchor, no new formal binding or Lean class, an explicit PAPER machine status, verification scope, and an untested empirical status.
- `CLAIM_LEDGER_v31.12.json`: the old 105 dictionaries are unchanged and in order, followed by the corresponding six `book_result` values, PAPER machine scope and `new_hardware_data=false`.
- Both canonical Markdown sources: edition 3.9, chapters 0–68, six appendices, 188 actual result statements, the six reviewed titles, ten chapter-68 sections and nine literally identical display blocks. Scientific bodies 1–66 except editorial chapter 48 are preserved. Chapter 67 permits only the exact reviewed low-spectral-energy erratum. All old displayed formulas and appendix-D code blocks remain unchanged.
- `SOURCE_MANIFEST.json`: previous source-catalog entries stay intact and ordered; current Chinese/English identities have their actual hashes and 69/6/188 counts.

Four prior files and the old ledger are pinned by SHA256. The historical Git evidence tree at `aea2fceef3c62cc8dc749b6cbb1b40a7d89df80d` must be available; changed previously tracked evidence is rejected. New evidence paths are allowed. The CI checkout therefore needs the already-configured full history.

## Required scientific execution evidence

Default new receipt:
`physics/qm/kernel/evidence/v31.12/runtime/execution_receipt.json`.

It must contain exactly these four successful command labels in order:

1. `source-integration`
2. `independent-operational`
3. `independent-microscopic`
4. `independent-exact-certificate`

Inputs, outputs and command logs are checked against current bytes. The actual four JSON reports are separately read and bound to their checker/model hashes, their own successful checks, and the explicitly finite numerical domain. The executor provider, observed Git head and dirty-worktree flag are required; a GitHub execution additionally records workflow-run/job identity. This does not require falsely treating a dirty checkout SHA as the source identity.

Default reuse receipt:
`physics/qm/kernel/evidence/v31.12/proof-reuse.json`.

`--proof-reuse REPOSITORY_RELATIVE_PATH` can override it. Required fields are `status=SOURCE_IDENTITY_REUSED`, `proof_reuse_eligible=true`, proof count 158, old-runtime count 13, old-runtime identity true, no mismatches, `new_lean_execution=false`, `new_lean_theorems=0`, and no promotion of new paper claims. The verifier independently hashes the 158 proof inputs against the original source manifest; it does not rerun Lean.

## Required publication evidence

The existing builder supplies `evidence/v3.9/{zh,en}/pdf-build.json`, with actual source/TeX/PDF hashes, edition 3.9, 69 chapters/six appendices, three successful compile passes, no layout/rerun warnings and stable final auxiliary files. All three logs are bound by their actual hashes.

The actual build's `builder_sha256`, language-specific `header_sha256` and `tables_filter_sha256` must match the current files. Because this publication actually encountered stale template fields, the checker also reads the generated TeX preamble: running header and title-page edition must be 3.9, the cover must say 69 chapters/six appendices and Kernel 1.12, and the displayed cover/document date must be 12 November 2026 (2026年11月12日 / `2026-11-12`). The generated title page must match the current template's title page. Historical references to older editions in the scientific body are deliberately unaffected.

`evidence/v3.9/visual-review.json` accepts either `languages: {zh:...,en:...}` or the older `documents:[{language:...},...]` shape. It requires a PASS-prefixed status, `method` or `scope`, and per-language `source`, `tex`, `pdf` identities (`path`, `sha256`; optional `bytes`) plus nonempty positive `reviewed_pages_1based` or `new_chapter_pages_1based`.

No local-acceptance receipt is required by this verifier, avoiding a circular dependency in which that receipt includes the verifier's own output. No remote merge or empirical acceptance is inferred.

## Executed preparation check

The actual first/current invocation accepted all inherited content, the integrated chapter, the new four-command runtime and the proof-reuse identities, while returning pending for not-yet-generated dossier/ledger/manifest/PDF/visual records. A separate invocation confirmed that `--require-complete` exits 3 while these pending obligations exist. Final invocation is reserved for the actual final metadata and publication files.
