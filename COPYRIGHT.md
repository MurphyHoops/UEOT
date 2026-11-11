# UEOT copyright, licensing and publication policy

Effective notice date: **2026-11-11**. Repository: `MurphyHoops/UEOT`.

## Principles

- Preserve and honor **previously granted CC BY 4.0** rights, including
  commercial reuse, translations and adaptations under the license conditions.
- Distinguish *copyrightable expression* from ideas, mathematical results,
  methods and independent implementations. This policy claims no monopoly on
  uncopyrightable concepts.
- Treat copyright ownership, license scope and the authority to grant a new
  license as separate factual questions.
- Avoid implying that a new file path, format change or new book cover
  extinguishes earlier licensing of underlying text.

## Scope and status

| Material | Existing / historical treatment | Future treatment |
| --- | --- | --- |
| `UEOT_v3_top.pdf`, historical manuscript sources and covered original research | Prior CC BY 4.0 grant preserved | A new edition may separately license genuinely new owned expression |
| `philosophy/UEOT_PHILOSOPHY.{md,tex,pdf}` and `mathematics/UEOT_MATHEMATICS.{md,tex,pdf}` | Previously public books: review their historical commit/version coverage under the prior broad license; do not claim exclusive control over reused CC BY text | New original edition material receives separate terms only through clear, edition-specific notices after a rights review |
| `core/`, `research/`, `validation/`, `publications/`, and research notes | Historical repository-authored materials may be covered by the prior license | New contributions require explicit project/file/publication license decision |
| `formalization/` (Lean and associated source code) | Prior license scope and contributor ownership require review; do not presume all code is Apache-2.0 | Select a suitable software license (Apache-2.0 is one candidate) **only after** source and contributor audit and explicit notices |
| `physics/`, `applications/`, tools and experiment scripts | Mixed material and code; individual provenance must be assessed | No blanket relicensing pending audit |
| Third-party templates, style files, bibliography assets, datasets, dependencies | Excluded from original CC BY grant to extent not owned; their own conditions govern | Maintain attribution and upstream license notices |
| Separately maintained `UEOT-GI` private implementation | Not licensed by a statement in this separate UEOT repository | Govern only in its own repository, contracts and distribution terms |

**Unknown does not mean proprietary:** If content was already released under
the prior broad CC BY license, an incomplete inventory does not remove that
permission. Likewise, a public repository is not a universal grant for newly
published content without a specific permission.

## Version boundaries and evidence

- The authoritative historical license text is
  [LICENSES/LEGACY-CC-BY-4.0-NOTICE.txt](LICENSES/LEGACY-CC-BY-4.0-NOTICE.txt).
- The baseline for preparing this policy was `main` commit
  `3776da6caf06a1c99837b15313d18857346f4baa` (2026-11-11), with prior
  root `LICENSE` Git blob `dfdadd423fa3bfe39c87e4ed8233c978a6ddf265`.
  These Git identifiers are **not** a complete copyright inventory or a
  substitute for dated release and contributor records.
- Authors, contributors and recipients should use the exact historical Git
  commit/tag/release and relevant notices to establish the applicable license.
- The published philosophy and mathematics book Markdown, TeX and PDF editions
  are related representations of copyrighted expression; new formats do not
  reset history.

## Future publication and licensing procedure

1. Before publishing an edition under new terms, create a content/version
   manifest identifying exact files, author ownership, dates, newly authored
   passages, and portions derived from previously CC BY materials.
2. Place the edition's specific license and copyright notice **inside the
   publication files or edition manifest**, with consistent PDF, TeX and
   Markdown metadata. Never rely on a changed root LICENSE alone.
3. Disclose earlier CC BY editions and any third-party content to a publisher.
   Negotiate only rights actually available for an exclusive grant.
4. For Lean/software licensing, inventory imported code, generated files,
   contributor agreements, third-party license and notice obligations. Do not
   change the license header or add Apache-2.0 without authority.
5. Preserve history and attribution, and seek appropriate jurisdiction-specific
   legal review before exclusive book agreements, significant relicensing, or
   patent decisions.

For licensing and publication inquiries, open a repository issue; no commercial
or exclusive license is represented as granted unless separately documented.

This is a public policy notice, not legal advice.
