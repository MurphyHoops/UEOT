# What Prediction Leaves Out

## Relational Objecthood and the Grounds of Purpose

**Degui Qian · Version 1.0 · 11 November 2026**

A standalone philosophy research article reconstructing UEOT around a focused question: when does a successful representation justify claims about what persists and what an activity is for?

## Read the article

- [Typeset manuscript](manuscript.pdf)
- [Markdown source](manuscript.md)
- [LaTeX source](manuscript.tex)
- [Chinese abstract and extended synopsis](ABSTRACT_ZH.md)
- [Verified bibliography](references.bib)

The article is approximately 9,300 English body words, with a 223-word abstract. Exact final counts, reference resolution, and PDF page count are recorded in `VALIDATION.json`. It is an internally reviewed research manuscript for external critical assessment, not a journal-accepted or externally peer-reviewed publication.

## Argument and contribution

The article defends a selective relational realism about organized processes and a conditional account of purpose attribution. Its central argument is that exact claims about an individual's persistence or function need distinctions that a successful predictive representation can omit. Aggregate and probabilistic explanations may require different information, and the relevant target must be stated before evaluating the representation.

A finite regenerative source makes the argument concrete. Four initial configurations yield two predictive classes for first births, three for complete finite joint birth records, and four when the first repair fee is added to that complete task. The same birth process can omit whether the original body paid for recovery. The source also distinguishes executable code from decoded information and individual retention from strict reproduction.

The positive construction is a common realization: the same damaged founder can undergo paid restoration, execute its own restored programme, transmit it, and attain a specified expected-population factor under exact conditions. This is stronger than separate examples of a repairing system and an optimal system. It does not turn growth performance into an intrinsic goal. The limited functional claim about recovery has a stated design ground; biological intrinsic norms and moral reasons remain distinct questions.

The paper does not claim to originate process ontology, causal-state representation, organizational function, or regulatory teleology. It directly compares the proposed contribution with Bich (2024), Corti (2023), and Cuciniello (2026), as well as the other primary works in the bibliography. Its novelty claim is a constrained explanatory synthesis supported by exact examples, with external evaluation still required.

## Evidence and review

The source baseline is `MurphyHoops/UEOT@3d443ec29eb17af1fc00699a74e2d42d73516d81`, the actual main snapshot used when this research began. The historical original and the complete current philosophy book were read; current mathematical contracts and actual proof bodies were audited. Existing source-matched compilation receipts were reused. **No Lean build or natural experiment was run for this article.**

| Reader's question | Evidence file |
| --- | --- |
| Which article claims are arguments, formal results, or written examples? | [CLAIM_MATRIX.md](CLAIM_MATRIX.md) |
| Which original UEOT claims were retained, revised, rejected, or narrowed? | [ORIGINAL_TO_CURRENT_CLAIM_MATRIX.md](ORIGINAL_TO_CURRENT_CLAIM_MATRIX.md) |
| Which exact assumptions and Lean endpoints support the mathematics? | [FORMAL_CLAIM_EVIDENCE_MATRIX.md](FORMAL_CLAIM_EVIDENCE_MATRIX.md) |
| How was the nearest prior art checked? | [PRIOR_ART_AND_NOVELTY_REVIEW.md](PRIOR_ART_AND_NOVELTY_REVIEW.md) and [REFERENCE_VERIFICATION.md](REFERENCE_VERIFICATION.md) |
| What did the reviewers actually object to and what changed? | [REVIEW.md](REVIEW.md) and the frozen drafts/reports in `review/` |
| Which source bytes were used? | [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) |
| Was the PDF really built and visually checked? | [BUILD_RECEIPT.json](BUILD_RECEIPT.json) and [VISUAL_REVIEW.md](VISUAL_REVIEW.md) |
| What is the actual GitHub delivery state? | [DELIVERY_STATUS.md](DELIVERY_STATUS.md) |

Exactly three native agents performed the complementary research and complete-draft review. The coordinator wrote and revised the article. Initial judgments required revision; those reports are retained. Subsequent bounded sign-offs and the final editorial check are not represented as external human peer review.

The literature agent's original [verified external bibliography](review/REFERENCES_VERIFIED.bib) is retained as its research handoff. The article itself uses `references.bib`, which includes the external works and seven versioned UEOT source records.

## Rebuild

Use Python 3, Pandoc, BibTeX, Latexmk, and XeLaTeX with a normal complete TeX installation. The template uses Liberation Serif, Liberation Sans, and DejaVu Sans Mono. TeX packages include fontspec, amsmath/amssymb, geometry, microtype, setspace, longtable/booktabs/array, needspace, fancyhdr, natbib, hyperref, and xurl.

From this directory:

```bash
python3 build.py
python3 validate.py
```

`build.py` generates the LaTeX from the Markdown, formats the article, resolves BibTeX references, copies the finished PDF to this directory, and records actual tool versions, source/output hashes, page count, and warning checks. Temporary compilation files and logs are under `build/`. The small layout filter keeps the compact comparison table together. Existing scientific code is never imported or executed.

The supplied LaTeX can also be built directly:

```bash
latexmk -xelatex -interaction=nonstopmode -halt-on-error manuscript.tex
```

For visual verification:

```bash
pdftoppm -r 100 -png manuscript.pdf build/page
```

The actual preparation environment had TeX packages but lacked the normal filename database and a prepared XeLaTeX format. A temporary local XeLaTeX format was generated from the installed `xelatex.ini`, and filesystem search was enabled for that build. `build.py` accepts optional `UEOT_TEXMF` and `UEOT_TEXFORMATS` settings for this circumstance; ordinary complete TeX installations do not need them. This changed runtime caches only, not the scientific sources. Rebuilding in another TeX version can change binary PDF hashes or pagination without changing the argument; the receipt identifies this edition's actual bytes.

`validate.py` checks word range, citation keys, required files, build hashes, extracted unresolved markers, source hashes and change scope when run inside the UEOT checkout, and three printed rational examples. In a standalone extracted package, source-checkout comparisons are explicitly marked not run rather than silently passed. It is editorial validation, not a substitute for any general theorem or experiment.

## Scope, rights, and delivery

Only this publication directory is created. The original paper, original archive, three maintained books, frozen specification, Lean sources, and physics sources remain unchanged. `SHA256SUMS` identifies the included package files; the manifest identifies the separate immutable research inputs.

The manuscript's original research prose and explanatory companions are offered under CC BY 4.0, with historical and third-party rights preserved. See [COPYRIGHT_AND_LICENSE.md](COPYRIGHT_AND_LICENSE.md). No third-party full text or image is redistributed, and no repository-wide software licence is changed.

The intended branch is `pub/ueot-philosophy-foundations`. A local article, local commit, and prepared PR body are not a remote branch or PR. The actual state, any governance blocker, and the precise remaining authorization are recorded in `DELIVERY_STATUS.md`.
