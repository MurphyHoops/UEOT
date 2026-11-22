# Continuous Transitivity vs Superselection & Mermin–Peres Contextuality (`C-QSEL-06`, `P-QBORN-03`)

```text
Result ID: C-QSEL-06, P-QBORN-03
Core dependencies: Finite quantitative transport
Bridge dependencies: Intermediate-value topological obstruction on pure-state sector weights; parity-square algebra
Sector inputs: Continuous reversible pure-state transitivity; two-qubit Pauli tensor observables
Standard physical inputs: Standard Hilbert-space trace expectation and commuting subalgebra compatibility
Effective assumptions: Finite-dimensional operational subsystems
Formal status: Pure-kernel Lean 4 theorems (QuantumSuperselectionAndBorn.lean, 0 sorryAx) + exhaustive 512-configuration certificate
Observable/benchmark: State-independent quantum Mermin-Peres expectation 6 vs sharp non-contextual classical bound 4 (attained on 320/512 grids)
Falsification condition: Any non-contextual deterministic hidden-variable assignment violates at least one commuting row/column parity identity
```

Closes `PREMISES_AND_RESPONSIBILITIES.md` §5 Row 1 and `CORE_PHYSICS_CONTRACT.md` §4.

Evidence: [verify_superselection_born.py](verify_superselection_born.py) · [result.json](result.json)
