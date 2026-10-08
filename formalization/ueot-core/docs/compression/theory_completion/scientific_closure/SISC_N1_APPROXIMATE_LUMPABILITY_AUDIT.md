# N1.4 — quantitative non-ideal response → approximate class dynamics

Local formal status: **LEAN VERIFIED FOR FINITE CONTROLLED MODELS**.
This upgrades the N1.2 *exact* experimental identifiability theorem to a
realistic conditional error budget, without claiming a true exact quotient.

For each source-controlled action `a` and candidate partition block `[z]`,
define `P_a([z] | x) = Σ_{y∈[z]} K_a(x,y)`.

Assume a finite registered test family `f_i` and coefficients `c(z,i)` such
that for EVERY microscopic destination `y`:

`| 1_{y∈[z]} - Σ_i c(z,i) f_i(y) | ≤ δ`.

Assume states `x~x'` have for EVERY action and test:

`| E[f_i(Y)|x,a] - E[f_i(Y)|x',a] | ≤ ε`.

The Lean-checked theorem
`robust_class_mass_from_approx_observable_tests` proves the explicit bound

`|P_a([z]|x)-P_a([z]|x')| ≤ 2δ + ε Σ_i |c(z,i)|`.

Mechanism: each state incurs ≤δ weighted reconstruction error because its
finite transition mass is nonnegative and sums to 1; the cross-state test
difference is amplified by the sum of absolute reconstruction coefficients.
The final triangle inequality combines the two δ terms and one ε term.

## Why this result matters

1. `δ=ε=0` recovers the exact lumpability identification result.
2. Large coefficient norms reveal **poor observational conditioning**:
   even small response errors can result in weak bounds on transition masses.
   Counting probes, measuring pairwise separation, or reducing prediction MSE
   alone is therefore insufficient for a good Markov reduction certificate.
3. The theorem does not pretend approximate lumpability defines a canonical
   exact stochastic kernel. That step needs a separately constructed
   approximate quotient, an error propagation theorem and handling of
   action/horizon budgets.
4. `f_i` and `c(z,i)` are certificate inputs, not automatically identified
   from natural measurements. The theorem does not establish source-candidate
   completeness, experimental independence, concentration bounds or physical
   object identity.

## Next quantitative test

Develop finite-horizon error propagation, roughly a telescoping bound under
total-variation/Markov nonexpansivity, and benchmark the empirically
estimated coefficient condition number using independently predeclared
intervention tests. Preserve confidence/multiple-comparisons gates and
`UNRESOLVED` when the certificate lacks rank or external coverage.
