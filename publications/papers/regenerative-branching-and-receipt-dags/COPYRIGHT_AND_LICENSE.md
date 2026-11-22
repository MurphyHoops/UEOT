# Copyright, Licensing, and Release Provenance

## Manuscript and Vector Figures

- **Title:** *Prepayment Thresholds, Informative Zero Receipts, and Certified Polynomial Decision Diagrams in Partially Observed Regenerative Maintenance* (Version 1.0, November 2026)
- **Author & Copyright Holder:** Copyright © 2026 Degui Qian.
- **Prose & Figures License:** Creative Commons Attribution 4.0 International (**CC BY 4.0**, https://creativecommons.org/licenses/by/4.0/).

## Exported Lean 4 Proof Code & Verification Scripts

- The exported pure-kernel Lean 4 formalization archive (`publications/artifacts/lean4-core-export/`, exported from `formalization/ueot-core/`) and the standalone Python verification and figure-generation scripts (`build.py`, `validate.py`, `generate_figures.py`, `layout.lua`) accompanying this release are licensed under the **Apache License, Version 2.0 (`Apache-2.0`)** and permanently archived on Zenodo at <https://doi.org/10.5281/zenodo.24433585> (DOI: `10.5281/zenodo.24433585`; Concept DOI: `10.5281/zenodo.24433584`; see `LICENSES/Apache-2.0.txt`, `publications/artifacts/lean4-core-export/SOFTWARE_LICENSE_AUDIT.md`, and `NOTICE`). Non-code documentation under `formalization/ueot-core/docs/` remains governed by `CC BY 4.0` per root `LICENSE_SCOPE.md`.

## Author Direction and Generative AI Assistance Disclosure

This research and manuscript were directed by Degui Qian and completed with **Gemini 4 Carbon** and **ChatGPT 6 Astra** across mathematical derivation, Lean 4 formalization engineering, exact-rational solver verification, bibliographic cross-checking, and manuscript preparation. In accordance with journal authorship policies, generative AI systems are not listed as co-authors; Degui Qian defined the research program and stochastic-control architecture, audited and verified every mathematical proof, mechanized Lean 4 theorem, rational benchmark, and scholarly citation, and bears sole academic and legal responsibility for the entire work.

## Relationship to Maintained Repository Sources

This standalone article presents self-contained mathematical proofs in Sections 2–6 and Appendix A.1–A.6 with zero reliance on unpublished internal citations, corresponding to the pure-kernel verified Lean 4 (v4.33.1 / Mathlib) formalization across 30 interconnected modules in `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/` and maintained exposition in `mathematics/UEOT_MATHEMATICS.en.md` (§§39.75–39.88). Empirical applicability to natural biological or physical systems is not claimed (`UNVERIFIED`).
