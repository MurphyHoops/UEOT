# Continuum Worldtube-Renormalized Clock Gates & Dynamical Clock-FRW Closure (`P-CLOCK-UV-03`)

```text
Result ID: P-CLOCK-UV-03
Core dependencies: None
Bridge dependencies: S^3 Laplace-Beltrami worldtube smearing; Weierstrass backward-heat gate deconvolution; Raychaudhuri-Friedmann enthalpy conservation
Sector inputs: Sub-critical worldtube aperture g^2 sigma_{eta,inf}^2 < w^2; dynamical closed-FRW geometry
Standard physical inputs: S^3 volume V_0 = 2 pi^2; Klein-Gordon clock + scalar body stress-energy
Effective assumptions: Finite physical apparatus aperture eta > 0 (or super-renormalizable polynomial portal lambda_c chi phi psi + V_stab)
Formal status: Pure-kernel Lean 4 theorems (RenormalizedClockContinuum.lean, 0 sorryAx) + 40-digit outward-interval certificate
Observable/benchmark: Bare K=256 Fourier damping < 1e-28 & WICK_CLOCK_GRAPH c_* > 6e-11 vs worldtube continuum gate recovery < 1e-36, 4-body Wick norm^2 < 0.05, and dynamical FRW Friedmann drift < 1e-13
Falsification condition: Pointlike eta -> 0 bare non-polynomial gate at fixed g != 0 collapses strongly to zero; static ESU fails Raychaudhuri enthalpy balance for xdot != 0
```

Resolves the bare-clock continuum collapse (`CLOCK_UV`), body-only Wick 4-particle graph blowup (`WICK_CLOCK_GRAPH`), and static-$\Lambda$ enthalpy obstruction (`BACKREACTION_GATE`) with explicit continuum-convergent constructions.

Evidence: [verify_clock_uv.py](verify_clock_uv.py) · [result.json](result.json)
