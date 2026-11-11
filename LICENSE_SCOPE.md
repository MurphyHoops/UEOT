# UEOT — license scope and reader's map

**Scope reference:** original main baseline
`3776da6caf06a1c99837b15313d18857346f4baa` (2026-11-11).
This is a version boundary, not proof of sole copyright ownership or a
complete history of initial publication dates.

**Mandatory first rule:** An earlier valid CC BY 4.0 grant remains valid for
the covered expression, regardless of subsequent locations, editions or
notices. Read the original notice in
[LICENSES/LEGACY-CC-BY-4.0-NOTICE.txt](LICENSES/LEGACY-CC-BY-4.0-NOTICE.txt).

| Content | Existing/publicly released materials | Newly authored materials first published under this policy |
| --- | --- | --- |
| `UEOT_v3_top.pdf`, original manuscript and owned historical research | Historical CC BY 4.0; third-party exceptions remain | New owned research prose: CC BY 4.0 if in designated research scope |
| `core/`, `research/`, `mathematics/review/`, `philosophy/review/`, non-code `formalization/*/docs/`, and scientific `physics/` documents outside the formal physics book | Prior grants remain | Original research text/figures: CC BY 4.0, subject to explicit exceptions and rights |
| `philosophy/UEOT_PHILOSOPHY.{md,tex,pdf}` | Historical CC BY expression remains licensed | Newly authored future *edition-specific* expression: rights set in that edition; not automatically relicensed by root policy |
| `mathematics/UEOT_MATHEMATICS.{md,tex,pdf}` | Same rule | Same rule |
| `physics/qm/book/UEOT_PHYSICS.{md,tex,pdf}` | Same rule, including physics book v3.5 snapshot | Same rule |
| `formalization/ueot-core/`, `formalization/ueot-qm/` | Audit prior terms, file headers and copyright ownership; no retroactive change | Explicit software license only after review; Apache-2.0 a candidate, not currently declared |
| `physics/qm/kernel/`, `physics/qm/benchmarks/`, `tools/`, `validation/` executable scripts | Existing terms and dependencies to be audited | Software license to be explicitly selected after audit; prose reports follow their designated research license |
| `validation/` scientific reports, descriptions, original research figures | Respect historic rights and third parties | Owned research text and figures: CC BY 4.0 unless clearly excluded |
| Raw experimental data, third-party datasets, model weights, notebooks, figures sourced externally | Follow the dataset/asset provider's terms | Per-dataset declaration after provenance, consent, privacy and rights review; CC0 is an option for owned data |
| `publications/` snapshots | Version- and item-specific notice; historic licensed expression persists | Publication/edition notice; do not infer a blanket right from the folder name |
| Separate UEOT-GI product and its private implementations | Not implicitly part of this repository's grant | Separately owned/contracted product licenses |

## Official book-version rights inventories

- [Philosophy](philosophy/PUBLICATION_RIGHTS.md)
- [Mathematics](mathematics/PUBLICATION_RIGHTS.md)
- [Physics](physics/qm/book/PUBLICATION_RIGHTS.md)

**Three books means three books.** The physics book is not simply an
unlicensed appendix of the physics research directory. Its source,
typesetting source and PDF are representations of a maintained publication.

## What a new release must do

1. Assign a source commit, exact files and hashes, authorship/contributor
   status and the first-publication record.
2. Identify pre-existing CC BY material and distinguish new owned additions;
   respect third-party copyright and permissions.
3. Include a consistent rights statement in Markdown/TeX/PDF metadata or
   manifest *before* the edition is publicly released.
4. For new code, identify licenses by file/package and review Apache-2.0
   patent implications, contributor rights and imported Mathlib/other code.
5. For data, record collection authority, subject privacy, upstream terms
   and redistribution permission; avoid treating public access as CC0.
6. Notify any prospective exclusive publisher about already published CC BY
   material, prior public manuscripts and third-party inclusions.

**Avoid unauthorized assertions:** This is a scope guide, not a claim that
every commit, figure, table, result, code file or dataset is owned by one
person. For ambiguous files, consult history and legal counsel. New
rights statements cannot retrospectively narrow previously issued CC BY.
