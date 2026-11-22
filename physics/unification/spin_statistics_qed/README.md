# Symplectic Uncertainty, Pauli Spin-Statistics & QED `g - 2` Co-Constraint (`P-QCCR-04`, `P-SPIN-01`, `P-QED-02`)

```text
Result ID: P-QCCR-04, P-SPIN-01, P-QED-02
Core dependencies: None (explicit canonical/QFT sector bridges under CORE_PHYSICS_CONTRACT §§4, 6)
Bridge dependencies: Sp(2, R) covariance determinant invariance; equal-time paired-momentum microcausality test
Sector inputs: Canonical commutation vs anticommutation algebra; 4D perturbative QED + SM loop matching
Standard physical inputs: Rb-2020 atom-recoil fine-structure constant and Fan-2023 Penning-trap electron g-2
Effective assumptions: 4-loop perturbative QED truncation plus standard hadronic/electroweak shift
Formal status: Pure-kernel Lean 4 theorems (SymplecticSpinStatisticsAndQED.lean, 0 sorryAx) + 40-digit outward-interval certificate
Observable/benchmark: Sommerfield-Petermann C_2 in [-0.32847896558, -0.32847896557]; < 10^-9 cross-sector relative agreement between Rb recoil and electron g-2
Falsification condition: Anticommuting spin-0 scalar field produces strictly positive spacelike anticommutator (> 1.0 at dx = 0.25), violating microcausality
```

Closes `PREMISES_AND_RESPONSIBILITIES.md` §5 Row 6 ("独立选择一个物理输入，或同一观测的可反驳共参数关系").

Evidence: [verify_spin_qed.py](verify_spin_qed.py) · [result.json](result.json)
