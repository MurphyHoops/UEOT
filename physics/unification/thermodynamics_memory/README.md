# Quantum Thermodynamics, Persistent-Bath Memory & Marginal Purity Scope (`P-THERMO-01`, `P-OMEGA-02`)

```text
Result ID: P-THERMO-01, P-OMEGA-02
Core dependencies: Finite quantitative transport
Bridge dependencies: Reeb-Wolf entropy production decomposition; Cesaro spectral diagonalization
Sector inputs: Energy-preserving two-body partial swap; quasi-degenerate doublet and Friedrichs/Lee finite-band models
Standard physical inputs: Gibbs thermal reference state, von Neumann entropy, marginal Rényi-2 purity
Effective assumptions: Uncorrelated product input (or inter-step dephasing) for irreversible marginal purity decay across cycles
Formal status: Pure-kernel Lean 4 theorems (ThermodynamicsAndLandauerBounds.lean, 0 sorryAx) + 40-digit outward-interval certificate
Observable/benchmark: Exact 3/80 persistent-bath cycle-2 excess; 3-pulse coherent revival (34/25) vs dephased decay; exact 1 vs 1/2 Cesaro limit-exchange gap + W=8 Friedrichs bound-state floor
Falsification condition: Applying single-step marginal purity drop across coherent multi-pulse evolution without inter-step decorrelation fails at 3 pulses (3 * pi/6 = pi/2 swaps populations back)
```

Closes `PREMISES_AND_RESPONSIBILITIES.md` §5 Row 7 and elevates `sectors/heat.py` with explicit coherent-vs-dephased and continuum-bound-state scope boundaries.

Evidence: [verify_thermo_memory.py](verify_thermo_memory.py) · [result.json](result.json)
