# Quantum Thermodynamics, Persistent-Bath Memory & Omega-Loop No-Go (`P-THERMO-01`, `P-OMEGA-02`)

```text
Result ID: P-THERMO-01, P-OMEGA-02
Core dependencies: Finite quantitative transport
Bridge dependencies: Reeb-Wolf entropy production decomposition; Cesaro spectral diagonalization
Sector inputs: Energy-preserving two-body partial swap; Friedrichs/Lee discrete bath frequency comb
Standard physical inputs: Gibbs thermal reference state, von Neumann entropy, Rényi-2 purity
Effective assumptions: Unitary joint system-bath collision without external work during collision window
Formal status: Pure-kernel Lean 4 theorems (ThermodynamicsAndLandauerBounds.lean, 0 sorryAx) + 40-digit outward-interval certificate
Observable/benchmark: Exact 3/80 persistent-bath cycle-2 excess; finite-bath Pinsker excess 0.045 < D_KL; discrete-comb vs continuum limit-exchange progression
Falsification condition: Claiming autonomous out-of-equilibrium purity regeneration under isolated doubly-stochastic mixing violates strict Rényi-2 decrease
```

Closes `PREMISES_AND_RESPONSIBILITIES.md` §5 Row 7 and elevates `sectors/heat.py` to general theorems.

Evidence: [verify_thermo_memory.py](verify_thermo_memory.py) · [result.json](result.json)
