# Spacetime Causal Cone, Soft Spin-2 Equivalence & Multi-Scale Gravity Bounds (`B-SIG-01`, `P-EP-02`, `P-GRAV-03`, `P-HORIZON-04`)

```text
Result ID: B-SIG-01, P-EP-02, P-GRAV-03, P-HORIZON-04
Core dependencies: None (explicit sector/standard-physics bridges under CORE_PHYSICS_CONTRACT §§6-7)
Bridge dependencies: Finite-speed isotropic causal cone -> Minkowski conformal class; Fisher-Rao PSD obstruction
Sector inputs: Massless spin-2 soft gauge invariance; f(R) = R + alpha R^2 quadratic curvature; bipartite unitary evaporation
Standard physical inputs: Cassini solar-conjunction bound, Eot-Wash sub-mm Yukawa bound (Lee et al. 2020)
Effective assumptions: Linearized isotropic weak-field Yukawa metric potentials at solar/laboratory scales
Formal status: Pure-kernel Lean 4 theorems (SpacetimeEquivalenceAndGravityBounds.lean, 0 sorryAx) + 40-digit outward-interval certificate
Observable/benchmark: Finite-ray Cassini screening vs Eot-Wash m >= 5.112 meV (alpha <= 2.484e-10 m^2); post-Page k=8 correlation deficit > 4.15 nats
Falsification condition: Direct Fisher-Rao pullback fails to admit timelike vectors; unscreened long-range f(R) gives |gamma - 1| = 1/2 > 9e-5
```

Addresses `PREMISES_AND_RESPONSIBILITIES.md` Responsibilities `G02`, `G04`, `G05/G06`, and `G14`.

Evidence: [verify_spacetime_gravity.py](verify_spacetime_gravity.py) · [result.json](result.json)
