# RG Typing Bridge, Mori–Zwanzig Memory & EFT Scheme Cancellation (`C-RG-01`, `P-EFT-02`)

```text
Result ID: C-RG-01, P-EFT-02
Core dependencies: UEOT.V3.Compression.QuotientDescent.fiberCompatible_iff_existsUnique_descend
Bridge dependencies: Dynkin intertwining equivalence for Markovian process coarse-graining; Schur-complement Gaussian elimination
Sector inputs: Discrete-time stochastic dynamics; 4D Euclidean two-scalar portal field theory
Standard physical inputs: One-loop Feynman parameterization, MS-bar and MOM subtraction conventions
Effective assumptions: Low-momentum expansion Q^2 << M^2 for dimension-6 EFT truncation
Formal status: Pure-kernel Lean 4 theorems (RGBridgeAndEFTMatching.lean, 0 sorryAx) + exact rational & 40-digit outward-interval certificate
Observable/benchmark: Exact 1/16 Mori-Zwanzig memory defect at t=2; <10^-35 scheme spread across MS-bar(50/150 GeV) and MOM(3 GeV) with enclosed O(Q^4/M^4) remainder
Falsification condition: Conflating Object-RG fibre compression with memoryless semigroup evolution fails at t=2 on non-lumpable fibres
```

Closes `CORE_PHYSICS_CONTRACT.md` §5 and the EFT/scale exit gate of `PREMISES_AND_RESPONSIBILITIES.md` §5 Row 9.

Evidence: [verify_rg_eft.py](verify_rg_eft.py) · [result.json](result.json)
