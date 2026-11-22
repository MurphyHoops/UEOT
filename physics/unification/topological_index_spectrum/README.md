# Topological Bundle Descent, Overlap Dirac Index & Spin Structures (`P-TOPO-01`)

```text
Result ID: P-TOPO-01
Core dependencies: None (explicit geometric/topological carrier bridge under PREMISES Row 12)
Bridge dependencies: U(1) torus cocycle transition quantization; Ginsparg-Wilson exact lattice chirality
Sector inputs: 2D spinor carrier on T^2 with periodic (+,+) and antiperiodic (-,+) spin structures
Standard physical inputs: Landau-gauge magnetic flux backgrounds m in {-2,-1,0,1,2}; Neuberger Overlap operator
Effective assumptions: Finite torus lattice L = 10 above the admissible Wilson kernel gap
Formal status: Pure-kernel Lean 4 theorems (TopologicalCarrierAndIndex.lean, 0 sorryAx) + deterministic Overlap spectral certificate
Observable/benchmark: Exact chiral index |n_+ - n_-| = |m| across m in {-2..2}; m=0 spin-structure shift from 2 zero modes to 0 zero modes (gap^2 = 0.09789)
Falsification condition: Non-integer flux violates plaque transition cocycle closure; antiperiodic spin structure eliminates m=0 harmonic zero modes despite identical Euler/Chern numbers
```

Closes `PREMISES_AND_RESPONSIBILITIES.md` §5 Row 12 and generalizes `sectors/RESULTS.md` §4.

Evidence: [verify_topo_index.py](verify_topo_index.py) · [result.json](result.json)
