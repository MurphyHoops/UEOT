# Action-Selection (`Π/Φ`) Ostrogradsky Gate & Attractor (`GOD/GOA`) Doeblin Rates (`P-PIPHI-01`, `P-GOA-02`)

```text
Result ID: P-PIPHI-01, P-GOA-02
Core dependencies: Finite quantitative transport
Bridge dependencies: Legendre-Ostrogradsky higher-derivative phase-space reduction; Doeblin minorization contraction
Sector inputs: Pre-declared relativistic scalar/oscillator lagrangian candidate class; discrete-time CPTP/Markov maps
Standard physical inputs: Energy lower-boundedness requirement; L1 trace-distance norm
Effective assumptions: Nondegenerate highest time derivative eps != 0 for Ostrogradsky reduction
Formal status: Pure-kernel Lean 4 theorems (ActionSelectionAndAttractorRates.lean, 0 sorryAx) + exact rational & outward-interval certificate
Observable/benchmark: Pais-Uhlenbeck ghost mode drives H = -249 < 0; exact (3/4)^n Doeblin contraction vs 6-parameter collective-dephasing DFS manifold
Falsification condition: Post-hoc -||K - H||^2 fitting fails to exclude Ostrogradsky ghost Hamiltonians; reducible QND/DFS channels refute unconditional unique GOA
```

Closes the `Π/Φ` and `GOD/GOA` falsifiable obligations of `PREMISES_AND_RESPONSIBILITIES.md` §3.

Evidence: [verify_piphi_goa.py](verify_piphi_goa.py) · [result.json](result.json)
