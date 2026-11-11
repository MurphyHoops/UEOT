# Recording the 3.7 publication source-PR acceptance

`build/record_remote_publication.py` records the actual completed source-PR CI observation supplied in `evidence/v3.7/remote-delivery.json`. It makes no network request and does not execute scientific tests. The change is **`PUBLICATION_PR_PENDING` → `PUBLICATION_PR_VERIFIED_UNMERGED`**; the detailed remote state is **`PR_SOURCE_VERIFIED_UNMERGED`**.

The helper is deliberately pinned to repository `MurphyHoops/UEOT`, publication PR **454**, source commit `17b8959154d0459efd44cb9d7d30233e847d4e8f`, tree `c8464ea2cd3f4f1aaca52aba97f7085ab626be53`, and source CI run **42974391710**. A different release or source head requires a separately reviewed transition. It is not a general remote-status synchronizer.

## Receipt contract

The receipt uses schema `ueot_physics.remote_delivery.v1` and the following required fields. Additional observed API fields can be retained. The repository-relative evidence paths are exact, and each identity contains `path`, `sha256`, and `bytes`.

| Field | Required value or meaning |
|---|---|
| `edition`, `repository`, `status` | `3.7`, `MurphyHoops/UEOT`, `PR_SOURCE_VERIFIED_UNMERGED` |
| `observed_at_utc` | Actual UTC observation time, no earlier than either job completion |
| `source.commit`, `source.tree` | The pinned source identities above |
| `pull_request` | `number: 454`, canonical GitHub URL, `state: open`, `merged: false`, exact source `head_sha`, `base_ref: main` |
| `source_ci` | `run_id: 42974391710`, positive `run_attempt`, `name: UEOT QM Kernel`, `workflow_path: .github/workflows/ueot-qm.yml`, canonical run URL, `event: pull_request`, exact source `head_sha`, `status: completed`, `conclusion: success` |
| `source_ci.jobs` | Exactly the `runtime` and `lean` jobs, each with distinct positive `id`, the same `run_id` and `head_sha`, `completed`/`success`, and actual `completed_at` |
| `source_ci.jobs[].steps` | Optional full API step observations; when provided, every reported step must be completed and successful or skipped, and all named essential verification steps must have succeeded. A skipped dependency-cache save is permitted; skipped proof or certificate verification is refused. |
| `evidence.git_payload_readback` | Exact identity of `physics/qm/book/evidence/v3.7/git-payload-readback.json` |
| `evidence.publication_preflight` | Exact identity of `physics/qm/book/evidence/v3.7/publication-preflight.json` |
| `scope` | The source commit and its source CI only; no merged-main acceptance, and no attribution of later metadata-commit CI to this run |

The actual receipt retains remote artifact API metadata while explicitly stating that its ZIP bytes were not independently downloaded, hashed, or inspected. The helper does not strengthen that claim. GitHub API observations are supplied by the root agent; reading and validating the supplied receipt is not an independent second remote observation.

## Installation and execution

Install the helper at `physics/qm/book/build/record_remote_publication.py`, this document at `physics/qm/book/review/REMOTE_PUBLICATION_METADATA_README.md`, and the optional guard report at `physics/qm/book/evidence/v3.7/remote-publication-guard-check.json`. The helper binds their actual installed bytes when present. It also identifies both delivery READMEs as follow-up documentation, outside the source-CI acceptance scope.

From the repository root, first run a read-only check:

```sh
python3 physics/qm/book/build/record_remote_publication.py --book-dir physics/qm/book
```

The optional `build/verify_remote_publication_guards.py` reproduces the actual-receipt positive check and 16 synthetic in-memory refusal cases. Run it **before the transition and terminal receipt refresh**, writing its result outside the book so the installed upstream guard report remains stable:

```sh
python3 physics/qm/book/build/verify_remote_publication_guards.py --book-dir physics/qm/book --output /tmp/ueot-remote-publication-guards.json
```

The committed guard report identifies the exact helper and driver hashes. It contains no resulting metadata hashes, so binding that guard report does not introduce a hash cycle.

For an isolated preview, add `--output-dir /absolute/path/outside/the/book`. Preview mode writes candidate copies and a report there. To install the reviewed transition:

```sh
python3 physics/qm/book/build/record_remote_publication.py --book-dir physics/qm/book --write
```

Only three files are written: `SOURCE_MANIFEST.json`, then `CHAPTER_DOSSIER.json`, then the new `evidence/v3.7/publication-remote-metadata-update.json`. The two metadata files are individually replaced atomically; the three-file operation is not a filesystem transaction. A partial interruption can be recovered by rerunning with unchanged inputs, before regenerating the terminal acceptance receipt.

After the transition, run the maintained `accept_publication.py` to regenerate the downstream `local-acceptance.json` against the exact new metadata. The helper intentionally checks the original pre-PR local receipt during the transition; after terminal acceptance is regenerated, do not rerun this transition helper. The current local-acceptance link remains path-only. The previous local receipt remains available by source-commit URL and hash in the historical checkpoint.

Publish one separate delivery-metadata commit. Its CI must be observed independently and recorded in the PR body. Do not issue successive receipt commits merely to record each previous metadata commit's CI. Neither the successful source run nor the later metadata run is a main-merge acceptance.

**Do not rerun `update_publication_metadata.py` for this transition.** That earlier tool describes the pre-PR local publication checkpoint and deliberately does not advance remote acceptance.

## Preservation and scope checks

The helper reads the pre-PR metadata from the immutable tested source commit and makes only the publication-status changes listed by JSON pointer in its output report. Current metadata must equal either that exact source version or the exact new candidate; an unrelated local metadata edit is refused.

The following are preserved:

- All **173 numbered-result objects**, all **12 manifest entry objects**, and the complete scientific `source_catalog`, including historical states.
- `scientific_reuse` and all research identities. v31.10 `MAIN_VERIFIED` remains distinct from this unmerged publication source acceptance.
- The separate `prior_current_fields` objects in the manifest and dossier. They intentionally differ because each preserves its own v3.6 metadata fields.
- All six frozen Markdown, TeX, and PDF files, verified against both the source Git objects and existing manifest identities.
- The original pre-PR metadata report and local receipt, retained byte-for-byte during transition and linked by immutable source-commit URLs.
- All 19 other previously bound review records. Only the authorized `review/README.md` identity is refreshed.

The helper checks the 110 source payload records against local Git source objects, including Git blob identity, SHA-256, and byte count. It validates the supplied readback and preflight identities and their source commit/tree. These checks establish local identity consistency with the recorded remote observation; they do not create a new GitHub observation.

The resulting manifest is serialized first; its exact hash is stored in the dossier. The external remote-metadata update report then binds both outputs. Neither metadata file contains that report's hash. The later terminal local receipt also stays downstream. This one-way order prevents self-reference.

The new `validation.remote_verified: true`, derivative states, and 73 chapter/appendix states refer only to the exact publication source and its completed source CI. `merged_main_commit` and `main_ci` remain `null`; `merged_main_ci` remains `PENDING_PUBLICATION_MAIN`. Remote CI success does not establish new physics, remove an OPEN scientific mechanism, or constitute external peer review.

## Review findings and remaining limits

The actual source receipt reports both source jobs completed successfully. Its `lean` job includes a legitimately skipped cache-save step; the verification steps are successful. The source workflow explicitly checks out the PR head for both jobs. The helper verifies these scope boundaries without changing workflow or scientific code.

The supplied receipt is evidence, not a cryptographic proof of GitHub service behavior. Its provenance remains the observer's responsibility. Concurrent modification of a read input is checked before installation, but the installation is not a cross-file atomic transaction. All scientific, visual, and publication reports retain their stated scopes; this metadata helper adds no further scientific or visual validation.
