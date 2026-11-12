# Operational bridge for the reconstructed v31.12 increment

Author/reviewer: native research agent A, this recovery session. This document is
a new written derivation. It does not recover, re-date, or certify the lost
uncommitted bytes from the interrupted session.

Read-only source baseline: `aea2fceef3c62cc8dc749b6cbb1b40a7d89df80d`.
Inherited source: `physics/qm/audits/OPERATIONAL_MICRO_ROBUST_v31.11/SHARED_MODEL.md`,
the actual bilingual Chapter 67, and its existing finite-complex operational
equivalence interface. No new Lean theorem is asserted here.

## 1. Frozen mathematical and operational contract

Let `H = C^2 tensor l^2(N_0)`, `G = a†a + P_e`, and
`P_m = 1_{G<=m}`. The finite carrier `H_m=P_m H` has dimension `2m+1`;
`I_m:H_m -> H` denotes its canonical isometry. R is an arbitrary positive
finite-dimensional complex reference, untouched by every operation. The joint
input is a density with `Tr(G rho_S)<=nbar<N+1`.

The original controls are `U_0=exp(-i phi P_e)` and
`U_1=exp[-i alpha (a sigma_+ + a† sigma_-)]`. The actual new control is

`V_0=U_0`, `V_1=B_beta U_1`,
`B_beta=exp[-i beta (a† sigma_+ + a sigma_-)]`.

Thus the red pulse occurs before the separated blue pulse. There are at most two
source steps, with chronological terminal records
`{f,0f,1f,00,01,10,11}`. The source events are
`K_0=sqrt(s(1-q)) V_0`, `K_1=sqrt(sq) V_1`, and
`K_f=sqrt(1-s) I`, with `s=1-q/2` and `q in [12/25,13/25]`.
Fresh flags and independent readout/reset remain explicit model assumptions.
The model does not select complex quantum mechanics from Core and does not
establish laboratory accuracy of either sideband approximation.

The target accepts exactly two successful source steps. The deployed controller
uses the inherited visible-history weights: first label-one weight `1/2`, then
`312/625` following label 0 and `313/625` following label 1. Its successful record
law is `Q00=Q11=313/1250`, `Q01=Q10=312/1250`. It knows neither true q nor a hidden
Kraus index. At each observation fibre it uses one common weight.

## 2. Exact rectangular events derived from the microscopic gate

The blue generator acts on the doublets
`span{|g,n>,|e,n+1>}` by `sqrt(n+1) X`, and annihilates `|e,0>`.
Its block direct sum is self-adjoint on its graph domain. Explicitly,

`B_beta |g,n> = cos(beta sqrt(n+1)) |g,n>`
`                  - i sin(beta sqrt(n+1)) |e,n+1>`,

`B_beta |e,n+1> = cos(beta sqrt(n+1)) |e,n+1>`
`                    - i sin(beta sqrt(n+1)) |g,n>`.

The total excitations of the vectors in a doublet are n and n+2. Hence

`B_beta P_m = P_{m+2} B_beta P_m`.

This range statement is derived from the microscopic action, not entered as a
certificate premise. Red and phase gates preserve every `P_m`. Define

`v_0^(m)=I_m† V_0 I_m : H_m -> H_m`,
`v_1^(m)=I_(m+2)† V_1 I_m : H_m -> H_(m+2)`.

Each is an isometry because the actual unitary's range on `H_m` lies entirely in
the declared output carrier. In particular `(v_j^(m))†v_j^(m)=I_(H_m)`.
The corresponding scalar-weighted events have adjoint products
`s(1-q) I`, `sq I`, and `(1-s) I`. Their sum is the input identity. They therefore
form a complete physical test even though their output types differ.

For a successful visible prefix h, let `b(h)` be its number of label-one events
and set `m(h)=N+2b(h)`. A failure event keeps the current carrier. The product of
the rectangular events along every path obeys

`I_(m(r)) k_r = K_r I_N`.

Proof is induction on path length, using the derived range identity at each step.
Tensoring with `I_R` preserves the identity on entangled input. Summing hidden
Kraus refinements, if used, is done within each visible outcome; no visible label
is summed away. Here each visible event has one displayed Kraus operator.

## 3. Complete terminal output and compositional identity

One legitimate terminal carrier is the orthogonal direct sum
`direct_sum_(r terminal) (H_(m(r)) tensor H_R)`. Equivalently, embed each block
canonically in `span{r} tensor H_(N+4) tensor H_R`, or into the physical Fock
carrier. The same record alphabet and the same embeddings must be used for the
two processes being compared.

Define the finite output as the direct sum of the unnormalized positive blocks
`(k_r tensor I_R) rho_N (k_r† tensor I_R)`. Induction over the finite stopping tree
shows that these blocks' traces sum to one. Consequently the complete-output
map is CPTP. Trace preservation includes failure leaves; it is not established
by normalizing only the four accepted leaves.

The path intertwining proves equality between this embedded finite output and
the infinite microscopic output on any input supported in `P_N tensor I_R`.
The integrated runtime instead pads every depth-j node to `H_(N+2j)`, including
zero and failure events. This is equivalent: canonical inclusion of the smaller
path-specific carrier commutes with each event and the terminal embedding. It
does not assert that a zero or failure event physically increases excitation.
For a general budget-admissible input, projection followed by normalization gives
the inherited initial error `sqrt(delta_N)`, where
`delta_N=1-Tr[(P_N tensor I_R)rho]<=nbar/(N+1)`.
Contractivity through the actual complete stopping channel yields the same error
for the full output. The finite range grows; the projection error is still paid
once at input, not once per pulse.

The old finite-complex operational equivalence theorems apply to each of these
finite rectangular actual maps. Their existing exact event/label equality may be
substituted in finite compositions. The oscillator range proof, whole variable
carrier tree, and trace-class comparison are paper proofs here. They are not
newly machine-checked simply because the inherited module compiles.

### Positive and negative controls

- The derived `v_1^(m)` is a TP isometry from dimension `2m+1` to `2m+5`.
- Fixed-window compression is not TP: on `|g,m>`, it retains only
  `cos^2(beta sqrt(m+1))`; the missing probability is
  `sin^2(beta sqrt(m+1))`. Renormalization would change the event and generally
  create a nonlinear operation.
- Swapped visible unitary labels can give the same forgotten CP map and complete
  CQ distance one. Hence a channel-level comparison cannot silently drop records.
- Single-slot map equivalence assumes memory is included in the carrier or that
  auxiliaries actually reset. It does not identify reused hidden environments.

## 4. Source effect, conditional target, and shared parameters

For a successful two-step history r, `K_r†K_r` is its scalar probability times
the input identity because the rectangular path map is an isometry. Summing the
four successful histories gives `s^2 I`. At a still-successful depth t the backward
effect is `s^(2-t) I`; the acceptance effect at every failure leaf is zero.
This directly derives the same source effect as Chapter 67, now for the actual
blue-pulse instrument.

Normalization by `s^2` is input-independent, so the conditioned target is CPTP.
It has Bernoulli(q) weights on `00,01,10,11`, zero original-failure blocks, and
the same ordered actual `V` products as the permitted blue-inclusive actions.
The old all-input/all-reference robust distance therefore still equals the
classical record TV, with worst case `1/50`. Arbitrary shared phi, alpha and beta
do not change that equality. Independent mismatch of source and action gates
would invalidate it and requires its own error certificate.

## 5. Physical filtering and reference preservation

Set `P=P_N`, `Q=I-P`, and choose the actual reset state `tau_S=|g,0><g,0|`.
The physically realizable initial filter has success map `P rho P` and failure
map

`F_fail(rho_SR) = tau_S tensor Tr_S[(Q tensor I_R)rho_SR(Q tensor I_R)]`.

It acts on S only. Countably many reset Kraus operators `|g,0><j|`, with j ranging
over the discarded orthonormal basis, give this normal CP map and total failure
effect Q. The reference is conditioned by the observed failure but never reset
by an additional operation. The common output alphabet is
`{prep_fail} union {pass} x {f,0f,1f,00,01,10,11}`.
The ideal comparator has zero prep-failure mass; the actual branch cannot be
erased from the comparison or the cost.

The existing P-MICRO-02 bound applies to these exact outputs:

`D_prep <= f(delta_N)`,
`f(d) = (sqrt(d(4-3d))+d)/2`.

For completeness, purify rho and write the pure vector as orthogonal pass/fail
parts of squared norms `1-d` and d. Ideal minus the success block has the two by
two matrix `[[0,sqrt(d(1-d))],[sqrt(d(1-d)),d]]` in the normalized pass/fail
basis. Its trace norm is `sqrt(4d-3d^2)`. Add the orthogonal physical-failure
block's trace d, divide by two, then use partial trace and subsequent common
channel contractivity. This is inheritance of an existing proof, not a new
result count. Pure inputs saturate the pre-channel bound. f is monotone on [0,1].

**Reference negative control.** For
`(|g,0>|0>_R + |g,N+1>|1>_R)/sqrt(2)`, failure leaves the normalized reference
`|1><1|`, not the unconditional `I/2`. Replacing it by the latter changes the
complete output by trace distance `1/4` even if all other branches are correct.

## 6. Narrow correction to the inherited energy statement

For the particular low spectral filter used here, the passing input retains
`Tr(G rho_N)<=Tr(G rho)<=nbar`. If both outcomes have positive mass, write

`Tr(G rho)=(1-d) mu_low + d mu_high`,
`mu_low<=N<N+1<=mu_high`.

Then `mu_low<=Tr(G rho)`. The zero-tail case gives equality. Coherences do not
contribute to these spectral traces, and entanglement with R does not change the
argument. Thus Chapter 67's broader warning that conditioning may raise energy
needs qualification: it is true for general postselection, but not for this
ideal low spectral filter. Later arbitrary accepted branches still require their
own budgets. Physical nonideal filters require an independent preparation model.

## 7. Omission of the separated blue pulses on the deployed process

Let `A_b=a† sigma_+ + a sigma_-`. Direct block calculation gives
`A_b^2=a†a+P_g=G+1-2P_e<=G+1`. For any density with finite mean G and any finite
untouched reference, purification and the spectral inequality
`|exp(-i beta x)-1|<=|beta x|` imply

`D(B_beta rho B_beta†,rho)<=|beta| sqrt(Tr(G rho)+1)`.

The bound is a paper operator estimate on the stated energy domain, not a
finite-precision Choi bound. For a fixed record path, telescope the difference
between its full blue-inclusive gate word and its red/phase-only word. Use the
blue-free word for the prefix before each local replacement; those prefixes
preserve G. The suffix uses the actual unitary and contracts distance. A path
with k ones therefore contributes at most `k |beta| sqrt(nbar+1)`.

Since complete CQ distance is the sum of each record's probability times its
conditional-state distance, the deployed law Q gives

`D(C_beta,Q(rho), C_0,Q(rho))`
`<= E_Q[b(r)] |beta| sqrt(nbar+1)`
`= |beta| sqrt(nbar+1)`.

The final equality follows from the two marginal label-one probabilities, both
`1/2`. This calculation uses the actual allowed deployed policy, not the target's
different Bernoulli(q) law. A loose target-based `2q` coefficient needlessly loses
the available certificate. The same argument applies after the low spectral
filter because the passing mean energy does not increase.

Combined with the existing robust and preparation bounds, for
`nbar=1`, `N=4095`, and an independently justified `|beta|<=1/100`,

`D_full <= 1/50 + f(1/4096) + sqrt(2)/100 < 1/20`.

This is a mathematical sufficient bound in the ideal common-gate model. Its
remaining margin is small. Flag calibration alone does not establish the beta
bound or the remaining gate/readout/filter accuracy. An actual device precision
certificate remains unavailable without those separate data or model bounds.

## 8. Two implementations with different pulse costs

The same labelled instrument admits a measure-flag-then-act implementation and
a coherent-flag-controlled implementation. In the former, one schedules a blue
pulse exactly on a readout of 1. In the latter, one may schedule the controlled
pulse in every active slot even if its control amplitude is zero in the eventual
observed branch. The maps can agree while physical costs differ.

For the original source, the expected number of visible ones per unfiltered
attempt is `sq+s^2q=sq(1+s)`; the expected number of active slots is `1+s`.
For the compiled two-step process, the corresponding values are 1 and 2.
Multiply source-run costs by the physical filter pass probability when filtering
precedes the source, and include the filter and its failed-reset branch separately.
Under an actually re-preparable independent-trial contract the total source
success is `s_N s^2`; it is this total probability that divides expected attempt
cost. Calibration is a separate one-time amortized cost. Unknown quantum inputs
are not repeatable copies supplied for free.

## 9. Status and remaining responsibility

- Written mathematics: complete on the separated finite-pulse model above.
- Lean: inherited finite operational equivalence only; no new formal theorem.
- Independent finite computations: to be attached with fresh execution identity.
- Real calibration, terminal-state data, measured costs, or empirical closure: none.
- Simultaneous Rabi dynamics, infinite adaptive horizons, infinite-dimensional R,
  coherent controllers, real pulse leakage, field/particle/gravity completion:
  not covered by this bridge.

The independent checker complements these proofs with finite controls; it cannot
replace the universal quantifiers or identify a hardware model from record counts.
