# Galerkin Duhamel Telescoping & Correlated Two-Mode Gaussian Tail Bounds (`P-MICRO-06B`, `P-MICRO-11`)

```text
Result ID: P-MICRO-06B, P-MICRO-11
Core dependencies: Finite quantitative transport
Bridge dependencies: Noncommutative Duhamel boundary-flux telescoping; normal-mode Bogoliubov/orthogonal diagonalization
Sector inputs: Two-mode zero-mean gauge-invariant Gaussian bosonic environment (Chapters 69-71)
Standard physical inputs: Bose-Einstein geometric occupation distribution and Weyl displacement algebra
Effective assumptions: Per-mode normal-basis Fock truncation K on [0, n_max] x [-n_max, n_max]
Formal status: Pure-kernel Lean 4 theorems (CorrelatedGaussianTailAndGalerkin.lean, 0 sorryAx) + 40-digit outward-interval certificate
Observable/benchmark: Exact Weyl phases 0.16373162 rad vs 0.20213780 rad; K=20 witness tails < 3.6e-8; K=40 design-box worst corner < 1e-10
Falsification condition: Omitting cross-mode correlation c changes normal occupation n_+ = n + c and underestimates Fock truncation leakage
```

Extends Lean 4 and outward-interval formalization across Chapters 69–71 (`PREMISES` Rows 4–5).

Evidence: [verify_gaussian_tail.py](verify_gaussian_tail.py) · [result.json](result.json)
