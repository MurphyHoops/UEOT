# Agent B translation fidelity: Chapters 36–48

## Bound source and complete coverage

The thirteen chapter files in `chapters/ch-36.en.md` through `chapters/ch-48.en.md` translate the complete corresponding Chinese chapter files extracted from the bound v3.5 book, commit `3d443ec29eb17af1fc00699a74e2d42d73516d81`, book SHA-256 `b726e3b9033d79ef949b8e83469901fe728aa28ab204b2e4d55bf36a18b412f0`.

The scope includes every section, proof, counterexample, displayed and inline equation, numerical value inside mathematical notation, table, code block, source URL, result anchor, experimental limitation and research-package acceptance/failure condition. The English is an independent readable academic rendering, not a chapter summary. It contains approximately 15,050 English word tokens; formulas and code remain part of the complete deliverable.

## Actual checks

`B_TRANSLATION_CHECK.json` records an actual local check, with source/English SHA-256 identities for every chapter. All thirteen chapters passed:

- Equality of the mathematical-span multisets, covering 542 spans, after only the three declared translations of natural-language labels inside `\text{...}`.
- Equality in order of every display-math block under that same normalization.
- Exact preservation of all anchors and source URLs.
- Equal chapter/section heading counts and table-row counts.
- Exact fenced-code preservation apart from the declared stale-range repair below.
- Zero Chinese ideographs in the English chapter files.

Inline mathematical expressions can appear in a different grammatical order within an English sentence. No formula, constant, equation number or physical parameter was intentionally changed. A mechanical equality check supports symbol fidelity; it does not by itself certify natural-language equivalence. Every chapter was also written and reviewed against the source prose, retaining the stated conditions and limitations.

## Declared editorial changes

1. In §36.4, the formula label `或` becomes `or`, and the `b_2` table label becomes `low-energy, one doublet`. The coefficient table and all numbers are unchanged.
2. In §46.1, the displayed conditional-probability qualifier becomes `almost surely, for every`. Its quantifier, conditioning and inequality are unchanged.
3. In §48.2, `chapter_range: [0, 56]` becomes `[0, 65]`. The root editor was notified to apply the same correction to Chinese. It fixes a stale metadata example; it changes no result ID or mathematical statement.
4. Chapter 37's title is *Testable Flavor Constraints from Generation Nonuniversality*. The word “new” is not used as a claim of literature priority. The chapter retains all independent derivations and explicitly cites prior FCNC work.
5. In §§42.4, 47.14 and 48.4, historical source-review and verification work is attributed to the recorded source/kernel revision. This prevents the publication translation from implying that agent B reran old kernel, benchmark or archival-review work. The root editor was notified to align the Chinese temporal wording where needed.
6. Version 3.5 and original source paths are retained in chapter 48 for the root editor's coordinated edition update. They must not be independently revised in one language only.

## Terminology and scientific restrictions

Terminology follows the bilingual editor: **carrier**, **realization**, **actualization**, **strong record nondisturbance (SRN)**, **public record**, **predictive state**, **conditional survival**, **instrument**, and **process coarse-graining**. The distinct Object-RG and Wilsonian meanings remain explicit.

The English preserves these high-risk distinctions:

- Anomaly/beta arithmetic under a frozen representation table versus selection of nature's particle content.
- A positive FCNC bound versus a parameter-free observable discovery prediction.
- A cycle phase excluding diagonal Gaussian noise versus excluding all classical noise.
- A four-level witness excluding diagonal random phases versus excluding ordinary quantum environments.
- Asymptotic QND spectral-branch absorption versus exact finite-time projection or selection inside a degenerate subspace.
- A standard continuous-measurement SSE versus an independently motivated fundamental actualization mechanism.
- Experimental quantum simulation versus a synthetic numerical benchmark.
- A model-and-control reversal failure versus unique identification of objective collapse.
- Finite-lattice existence versus a nonperturbative continuum theory or mass-gap proof.
- A conditional per-trial null versus a marginal/time-average event bound; a valid supermartingale versus unadjusted optional stopping.
- A mathematical existence proof or Lean acceptance receipt versus a numerical synthesis algorithm or empirical confirmation.

## Internal-review status

This file records the translation author's scoped checks. It is not external peer review. Agent B remains assigned to an independent empirical/originality red-team pass after the root editor assembles the complete bilingual book. The final integrated edition's hashes, bilingual result mapping, PDF inspection and GitHub acceptance belong to the root publication receipts; these chapter hashes do not claim to bind a later edited assembly.

## Peer-editor correction incorporated

The bilingual editor reviewed Chapters 40–41 and correctly distinguished a bounded adapted **integrand** from a bounded stochastic integral. Both affected English sentences in Chapter 40 were corrected, and the root editor was notified to clarify the Chinese wording. Section-number typography was also repaired. All 542 mathematical spans remain unchanged under the declared label translations; the affected English SHA-256 was updated in the receipt.
