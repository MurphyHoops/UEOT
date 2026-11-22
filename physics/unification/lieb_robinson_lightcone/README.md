# Core `TransportCertificate` → Lieb-Robinson Light Cone → Minkowski Metric (`C-LR-CONE-01`)

```text
Result ID: C-LR-CONE-01
Core dependencies: UEOT.V3.Compression.TransportCertificate (weighted_chain_bound, twoStage_bound)
Bridge dependencies: Exponential spatial moment generating bound -> ballistic rescaling cone -> Minkowski null-cone uniqueness
Sector inputs: Local bounded-degree lattice couplings; asymptotic continuum isotropy
Standard physical inputs: None (emergent group velocity v_LR = 2 J (e^mu - 1) / mu)
Effective assumptions: Macroscopic ballistic scale Lambda >> 1 for sharp horizon suppression exp(-Lambda * kappa)
Formal status: Pure-kernel Lean 4 theorems (CoreTransportToLiebRobinsonCone.lean, 0 sorryAx) + 40-digit outward-interval certificate
Observable/benchmark: Brickwork outside-cone commutator < 1e-14; 7-site XX spin-chain commutator strictly bounded by Core transport exponential envelope; Lambda=100 supersonic leakage < 1e-16
Falsification condition: Instantaneous non-decaying spacelike signaling from finite-range bounded interactions falsifies local transport premise
```

Opens the theorem-bearing Lean 4 bridge from UEOT Core's `TransportCertificate` to relativistic Minkowski causal structure (`G02` upstream compression).

Evidence: [verify_lieb_robinson.py](verify_lieb_robinson.py) · [result.json](result.json)
