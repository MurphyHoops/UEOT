# A: independent precheck before source recovery

Status: mathematical attack notes only. These are not a source-level acceptance receipt.

## 1. Growing rectangular carrier

Let `G = a†a + |e><e|`, `P_m = 1_{G<=m}`, and let the blue-sideband pulse be
`U_b(beta) = exp(-i beta (a† sigma_+ + a sigma_-))`.
Its invariant doublets are `span{|g,n>, |e,n+1>}`. The two vectors have total
excitation `n` and `n+2`. Consequently `U_b P_m = P_{m+2} U_b P_m`.
The exact finite map for this pulse is rectangular, from `P_m H` to `P_{m+2} H`,
and is an isometry. This statement is stronger than an expectation-energy bound,
but is specific to a separated blue pulse. Red pulses and diagonal phase controls
preserve the total-excitation cutoff.

For a finite classical controller, a path with at most `l` blue pulses has support
in `P_{N+2l}`. The output carrier can depend on the visible history, but a comparison
of two processes needs a common carrier: either an explicit direct-sum terminal
carrier with matching record labels, or the physical Fock embedding of each
terminal block. Outcome grouping, stopping and failed branches must all be
included. A rectangular matrix alone is not evidence of a complete instrument:
the adjoint-product sum must be the identity on that node's input carrier.

### Negative controls

1. Fixed-cutoff compression loses probability. On `|g,N>`,
   `||P_N U_b(beta)|g,N>||^2 = cos^2(beta sqrt(N+1))`.
   Renormalizing this loss does not make the compression a deterministic CP map.
2. A simultaneous red-plus-blue pulse need not have finite propagation. With
   `H = g (a+a†) sigma_x` and input `|+>_x tensor |0>`, any nonzero time gives a
   coherent oscillator state with nonzero population at arbitrarily high `n`.
   Thus the finite product theorem cannot cover the simultaneous Rabi generator.

## 2. Physical filter, failure record, and reference system

For `P=P_N`, `Q=I-P`, and a fixed reset state `tau_S`, the failure branch produced
by an operation on S alone is

`F_fail(rho_SR) = tau_S tensor Tr_S[(Q tensor I) rho_SR (Q tensor I)]`.

It is not generally `q tau_S tensor rho_R`. The reference is unchanged by an
additional operation, but it is conditioned by the observed filter failure.
For `(|g,0>|0>_R + |g,N+1>|1>_R)/sqrt(2)`, the failure reference is `|1><1|`,
whereas the unconditional reference is `I/2`. Replacing the conditional reference
by the unconditional one introduces complete-output trace distance `1/4`.

When the ideal comparator is labelled always-success, the actual failure flag
must remain. For a pure input with failure mass `q`, before any later channels,

`D(|pass><pass| tensor rho, |pass><pass| tensor P rho P + |fail><fail| tensor F_fail(rho))`
`= (sqrt(4q-3q^2)+q)/2`.

The formula follows by diagonalizing `rho-P rho P` on its at-most-two-dimensional
support and adding the orthogonal failure block's trace. It supplies a sharp
control for the universal bound; it is not evidence of the exact bound used in
the recovered candidate until that source is inspected. The simpler bounds
`sqrt(q)+q/2` and `sqrt(q)+q` are sufficient but less sharp. No numerical precision
target should silently switch among them.

## 3. Visible labels and memory

Equal coarse-grained maps do not imply equal complete instruments. The two labelled
instruments `{0: I/sqrt(2), 1: X/sqrt(2)}` and
`{0: X/sqrt(2), 1: I/sqrt(2)}` have the same unlabelled map, but their CQ outputs
on `|0><0|` have trace distance 1. Each label therefore remains part of the event
identity, and controller weights can depend only on its declared visible history.

Equal single-step CP maps also do not establish an equality of non-Markovian
processes. A fixed hidden random bit selecting `I` or `Z` for both slots and an
independently refreshed bit for each slot both yield the one-slot dephasing map;
the two-slot maps are respectively identity and dephasing. This is already an
inherited boundary and only needs preservation, not a new result registration.

## 4. Cost contract

The number of observed `1` labels equals the number of physically invoked blue
pulses only in a specified measure-flag-then-act implementation. A coherent
controlled pulse may be scheduled at every slot. Both can realize the same labelled
instrument, while incurring distinct costs. A cost certificate must identify
which implementation it prices and include filtering failure and reset.

## 5. Pending evidence

- Actual candidate commit and files.
- Chapter 68 bilingual statement and complete-output embedding definitions.
- Source instrument and backward-effect calculation on matching rectangles.
- Physical filter failure branch and resource accounting.
- Exact mapping of any claims to inherited Lean declarations.
- Independent checker, execution identity and unchanged-source evidence.

No repository acceptance, machine proof, device validation or experimental result
is asserted by this precheck.
