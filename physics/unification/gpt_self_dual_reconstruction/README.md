# Core `QuotientDescent` → GPT Self-Dual Cone, Jordan Selection & Born Rule (`C-GPT-RECON-02`)

```text
Result ID: C-GPT-RECON-02
Core dependencies: UEOT.V3.Compression.QuotientDescent (existsUnique_twoSidedDescend); UEOTQM.CorePurificationBoundary
Bridge dependencies: Minimal separating GPT state-effect quotient; Koecher-Vinberg PSD cone self-duality; Hurwitz/Jordan composite filter
Sector inputs: Universal purification + local tomography (selecting r = 2 over r in {1, 4, 8} and classical simplex)
Standard physical inputs: None
Effective assumptions: Finite-dimensional operational subsystems (d_A, d_B >= 2)
Formal status: Pure-kernel Lean 4 theorems (GPTSelfDualConeReconstruction.lean, 0 sorryAx) + exact rational & 40-digit outward-interval certificate
Observable/benchmark: Operational quotient ranks (2, 3, 4); Hurwitz two-qubit defects (-1, 0, +8, +48) uniquely selecting r=2; qutrit Born-matrix recovery < 1e-38
Falsification condition: Violation of local tomography or non-additive frame probabilities on orthogonal effects falsifies Herm(C^d)_+ Born cone
```

Opens the machine-checked GPT reconstruction bridge from UEOT Core's `QuotientDescent` and `CorePurificationBoundary` to `Herm(ℂ^d)_+` and the Born trace rule.

Evidence: [verify_gpt_reconstruction.py](verify_gpt_reconstruction.py) · [result.json](result.json)
