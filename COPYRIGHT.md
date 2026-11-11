# UEOT copyright, research openness and publication rights

Prepared: **2026-11-11**. Repository: `MurphyHoops/UEOT`.

## Legal and scientific separation

The UEOT project has six distinct categories: (1) historical licensed
research, (2) continuing open research, (3) three formal authored books,
(4) Lean/code and executable research, (5) experiments/data/third-party
assets, and (6) commercial implementations owned separately.

**Open research and controlled book publishing are compatible**, but not
through retroactive revocation. CC BY 4.0 already permits commercial reuse
of covered expression. Prior recipients and later lawful recipients of
the already licensed versions retain these rights.

See the operative [LICENSE](LICENSE), [scope matrix](LICENSE_SCOPE.md)
and [preserved original notice](LICENSES/LEGACY-CC-BY-4.0-NOTICE.txt).

## A precise baseline, not an invented exclusive-rights ledger

Before this policy, the root LICENSE's exact Git blob was
`dfdadd423fa3bfe39c87e4ed8233c978a6ddf265`.
The main baseline was
`3776da6caf06a1c99837b15313d18857346f4baa`
(2026-11-11). The archived copy has the same exact Git blob, verifying
byte-for-byte preservation.

This snapshot does **not** prove that all files were first published on that
date, that all authors had authority to grant rights, or that every covered
piece of historical text is uniquely identifiable without further review.
Historical licensing is assessed through actual earlier notices, dates,
releases, commits and contributor ownership.

## Three independent books

- **Philosophy:** [rights inventory](philosophy/PUBLICATION_RIGHTS.md).
- **Mathematics:** [rights inventory](mathematics/PUBLICATION_RIGHTS.md).
- **Physics:** [rights inventory](physics/qm/book/PUBLICATION_RIGHTS.md).

Each book exists in Markdown, LaTeX and PDF. Its underlying expression
does not lose prior license rights by being converted between formats.

New *copyrightable expression* written for a later expressly identified
book edition can receive a different license when the author has the right
to grant it. An editor or publisher cannot lawfully treat previously
CC BY 4.0 licensed passages as newly exclusive merely by repackaging them.
A new edition must expressly and visibly distinguish old licensed material
from new additions. If a publisher wants exclusivity, disclose earlier
open versions and negotiate only rights genuinely available.

An edition-specific choice (all rights reserved, CC BY, or another license)
has not yet been made for any *future edition* of these books. The current
books are not newly designated all-rights-reserved by this policy.

## Physics-specific licenses

The physics program has **different artifacts with different responsibilities**:

- `physics/qm/book/` — the third maintained formal book, not automatically
  covered by the *prospective open research* category.
- `physics/qm/UEOT_QM_*.md`, `physics/interfaces/`, and other original
  research explanations — future owned research prose is CC BY 4.0.
- `formalization/ueot-qm/` — Lean software/proofs, requiring independent
  code licensing and provenance review.
- `physics/qm/kernel/`, `physics/qm/benchmarks/`, `validation/` code —
  scripts, dependencies and computational artifacts require explicit
  software terms; reports and prose may be CC BY 4.0.
- Raw experimental data and third-party artifacts — specific data licenses,
  attribution and conditions; neither datasets nor restricted data are
  automatically relicensed.

See [physics/LICENSING.md](physics/LICENSING.md). Scientific availability
and a reproducible result do not establish copyright ownership in its
underlying experimental dataset.

## Software and patent caution

Creative Commons explicitly recommends software-specific licenses rather
than using CC licenses as a new default for software. **Apache-2.0 is a
candidate**, particularly for open Lean and research code, but has
substantive patent-license and contributor implications. MIT and other
options also need an explicit decision. No Apache-2.0 notice is added to
existing code until a documented rights/dependency audit.

A CC BY copyright grant is not a general patent grant. Conversely, a public
paper or source release may affect patent novelty under applicable national
rules even where copyright ownership is retained. Have patent counsel review
potentially patentable inventions *before* further disclosure if protection
is contemplated.

## Contribution and release control

Before accepting external code/text, ask contributors to confirm ownership
or authorization, identify pre-existing source material and accept the
appropriate license for the target file. Preserve attribution; do not assume
a GitHub PR transfers copyright ownership.

For new scientific prose in designated research areas, follow CC BY 4.0
unless an explicit exception is properly recorded. For future formal book
material, create an edition-specific source manifest, copyright/third-party
inventory and identical Markdown/TeX/PDF notices **before publication**.
For software and datasets, release only with an audited explicit license.

Separate UEOT-GI implementations, private model configurations, credentials
and proprietary data are not distributed or licensed by this repository.
Open scientific ideas may nevertheless be independently implemented by others.

This is a project policy and a planning instrument, not jurisdiction-specific
legal advice.
