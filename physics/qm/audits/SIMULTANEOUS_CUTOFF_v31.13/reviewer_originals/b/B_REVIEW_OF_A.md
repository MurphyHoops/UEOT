# B → A: independent review of complete-record composition

Reviewer: current native research role B. Date: 2026-11-12 (Asia/Shanghai). This is internal AI review, not external human peer review. Reviewed A's `A_FULL_CQ_STABILITY.md` and the shared root contract for v31.13.

## Attack 1: state-dependent outcomes, zero mass, and a hidden trace mismatch

The strongest operational statement is the terminal-CQ bound using finite/comparison prefixes and exact continuation suffixes. I checked whether it silently assumes equal prefix probabilities or trace-zero local discrepancies. It assumes neither. The expansion

`Omega_E(rho)-Omega_F(rho) = sum_h,o C^E_ho[(E_ho-F_ho)(sigma_h^F)]`

uses one fixed prefix direction throughout. Each `sigma_h^F` is a positive, unnormalized state. Each exact continuation is normal CPTP to the common terminal space, because its subtree is complete and all leaves are retained. A local difference can have nonzero trace, but the Jordan decomposition proves trace-norm contraction for every Hermitian trace-class input, not only equal-trace state differences. The sum is therefore legitimate even with state-dependent event probabilities.

Action probabilities are either summed inside their visible event or retained as explicit labels according to the actual observation contract. Zero mass contributes zero without defining a conditional state. Early stops and failures are leaves, so they cannot disappear through an implicit conditionalization. Finite operations need an explicitly declared CPTP extension only outside the states actually reached by the finite process; the proof does not identify that extension with an infinite oscillator operation there.

**Verdict:** the full-CQ composition theorem and the use of B's mass-weighted boundary defect are correct on the finite-tree contract. It does not authorize unbounded stopping or equality of processes with omitted persistent environments.

## Attack 2: the finite Duhamel proof and parameter stability after compression

A's finite-remainder improvement uses the correct Duhamel orientation: true evolution remains the leftmost unitary suffix, while every right prefix contains only a finite number of B factors and G-preserving reference propagators. Each such input has finite Fock support and lies in the domains needed for the next identity. With K=N+2L, all orders through L coincide exactly with the finite compressed-Hamiltonian expansion, and each final remainder is at most `c_(L+1)`. Thus the operator error `2c_(L+1)` is justified without an infinite Dyson argument. Inserting common G-preserving phase gates does not change the norm/support estimates.

The nominal-area bound is also correctly kept on **infinite** true/nominal comparison processes. The spectral force unitary and the spin phase strongly commute with the oscillator X spectral projections, so every such prefix preserves the X form norm. The bound requires D(X), equivalently the quadratic-form domain of the positive operator X², not the stronger operator domain D(X²). Purification and record weights give the complete-output bound with `E_Q[#1]=1`.

C-MICRO-03 is an exact counterexample to moving that invariant into the compressed model. At K=1, the finite Hamiltonian exchanges e0 and g1, while the compressed full X² form is diagonal `(1,3,1)`. Its expectation from e0 becomes `1+2 sin²x`, while the exact infinite model retains one. The resulting prescribed order—true infinite, nominal infinite, nominal Galerkin—is necessary and is respected.

**Verdict:** PASS. No blocking issue found. The infinite energy-budget proof in B now uses finite-matrix differentiation, the independent finite-support Duhamel convergence, then lower semicontinuity; this avoids importing an unproved form-invariance premise into A's composition.

## Verification and limits

A's finite checker is evidence for its concrete state-dependent tree examples; the universal statements rest on the written proofs. No new Lean coverage or physical experiment follows from this review. Root should bind the final A/B source bytes and preserve the distinction between exact finite-model prediction, certified numerical output arithmetic, and a physically realizable laboratory gate.
