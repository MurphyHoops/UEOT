# N1.2 — identifiable tests, Markov lumpability and a noncircular evidence bridge

This second lane isolates the missing bridge between **observable responses**
and the **strong lumpability** required for an exact controlled stochastic
quotient. The source already had the latter in P-ALG-01.

## Conditional theorem (actual new interface)

For a finite controlled stochastic model M and candidate Setoid S, suppose
there is a **registered finite family of tests** `f_i : X → ℝ` and separately
determined coefficients `c(z,i)` satisfying for every *target* microstate
z and state y:

`1_{S(y,z)} = Σ_i c(z,i) f_i(y)`.

This is **linear reconstruction of the indicator of every equivalence class**,
NOT merely nonempty tests, pairwise output separation or a rank-two bottleneck.
If equivalent *source* states x~x' have matching one-step expectations
`Σ_y K_a(x,y) f_i(y) = Σ_y K_a(x',y) f_i(y)` for every i and action a, then
one can multiply the reconstruction equation by K and sum to derive

`Σ_{y∈[z]} K_a(x,y) = Σ_{y∈[z]} K_a(x',y)`.

Therefore `Stable M S` and the **unique real quotient transition** follow
without assuming either as an input. This proof is in
`SISCObservableLumpability.lean` and directly invokes the existing stable
quotient result.

## Exact negative control

`SISCInsufficientTests.lean` uses a four-state deterministic (thus Markov)
model with microscopic state `(present,hidden)` and next output equal to
the hidden coordinate. Two source states share current output and equal
expectations of ALL registered **constant** tests, but have different masses
of the future `true` output block, so their current-output Setoid is not
strongly lumpable. The Lean no-go
`equal_observed_tests_do_not_force_stability` constructs the concrete model.

This validates why **spanning** is a genuinely necessary kind of additional
identifiability certificate for the proposed implication. The theorem does
not claim linear spanning is the only mathematically possible route to
Markov lumpability; other identification assumptions may suffice.

## Scientific interpretation

The coefficients `c(z,i)` are supplied as a separately checkable finite
linear identity; the theorem does **not** show that ordinary physical sensors
automatically span all latent candidate class indicators. A full experimental
certificate needs intervention-controlled test execution, observed noise
bounds, support/candidate coverage, well-defined action semantics, and
independent validation of class assignments. Physical object identity,
teleology and full UEOT scientific completion remain OPEN.
