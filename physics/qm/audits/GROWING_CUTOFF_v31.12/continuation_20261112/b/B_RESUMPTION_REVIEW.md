# B — Independent resumption review of the v31.12 dynamics and certificate

Date: 2026-11-12, Asia/Shanghai. Reviewer: current native research subagent B (`/root/b_micro_dynamics`). This is internal AI review, not external human peer review.

## Disposition

**PASS for integration of the declared segmented model. No blocking scientific defect found.** This review does not claim a new numerical run, Lean proof, or hardware observation. The previous completed local computation is reused only after the current input/output/log bytes have been checked.

The remote main observed during this review was `aea2fceef3c62cc8dc749b6cbb1b40a7d89df80d`. The partial recovery branch was `physics/v31.12-growing-cutoff-recovery-20261112`, head `b793f1d45c3d9b99b6495f7f488d3a01c5b1cde6`. The complete candidate, including Chapter 68 and its publication files, was read at `/workspace/scratch/2331c99c0713/ueot-physics`. The branch is not used as evidence that the complete candidate has already been published.

## 1. Sources and retained execution identity

Reviewed the shared model, `B_MICRO_GROWTH.md`, `B_REVIEW_OF_C.md`, `C_ROBUST_CERTIFICATE_AND_DATA.md`, `growing_cutoff/model.py`, `verify_integration.py`, `check_micro_growth.py`, `exact_checker.py`, the frozen model, and Chinese Chapter 68 with its corresponding English statements and displayed formulas. The actual source-bound runtime receipt is dated `2026-11-11T17:58:06.613021+00:00`; its observed Git HEAD was the v31.11 baseline and its worktree was dirty. The receipt correctly assigns byte identity to hashes, not to that baseline HEAD alone.

`identity_review.json` is this review's independently computed hash readback. All 213 checked entries matched: 158 inherited proof/configuration inputs, 13 inherited runtime inputs, 12 new runtime inputs, 8 new runtime outputs, 4 command logs, and 18 paper/release inputs. Some paths appear in more than one evidence role, so 213 is a count of checked entries, not unique scientific results.

The retained outputs record 114 integration checks, 68 operational checks, 100 microscopic checks, and 23 exact certificate checks. Those are the earlier actual executions and retain their original identities. There is no reason from this review to rerun an unchanged heavy Lean suite. New analytic infinite-dimensional and robust statements remain paper proofs even though they consume previously machine-checked finite-dimensional interfaces.

## 2. Strongest dynamics claim: exact growing carriers

Let `G=N+P_e` on the two-level probe and Fock oscillator. The red generator `A=a sigma_+ + a† sigma_-` reduces each fixed-G block; the blue generator `B=a† sigma_+ + a sigma_-` reduces the orthogonal two-dimensional blocks spanned by `|g,n>` and `|e,n+1>`, plus the singleton `|e,0>`. On each blue block it is `sqrt(n+1) sigma_x`. The weighted square-summable graph domain in the manuscript is correct. The bounded direct-sum resolvents of `B±i` establish self-adjointness on that domain; no inference from an arbitrary formal sum of unbounded operators is used.

The two G eigenvalues of a blue block differ by two. Thus, for every real pulse area, the source operator itself implies

`B_beta Pi_M = Pi_(M+2) B_beta Pi_M`.

With `V1=B_beta U1`, red and phase operations preserving G, and at most L blue operations along a finite legal classical tree, the initial `Pi_N` support reaches no farther than `Pi_(N+2L)`. The exact rectangular restrictions `J_(M+2)† K_o J_M` inherit whole-input-carrier completeness from this source-derived intertwining, including the zero event and every failure leaf. Equivalent hidden Kraus refinements also inherit the outside-support zero property by positivity; arbitrary extra actions do not.

The finite projected-input process equals the infinite source process after the declared terminal embeddings. Initial spectral Markov and normalized projection bounds, followed by complete-channel contraction, give the manuscript's uniform full-CQ error `sqrt(nbar/(N+1))` for every declared input and finite untouched reference. No extra L factor is required on this initial-tail term. The theorem is not a fixed-window result, not an infinite-time theorem, and not a diamond-norm statement for two fixed channels.

The runtime implementation respects these distinctions. The square ambient unitary is only a completion consumed on reachable columns. Its upper boundary is not asserted to equal the infinite blue unitary. The numerical N=1 witness and the separate N=1 filter-failure witness are not presented as execution at the analytic N=4095 cutoff.

## 3. Cross-review of C: physical filtering and the omission certificate

I attacked the integrated certificate by trying four substitutions: deleting the physical filter failure branch; replacing the failure-conditioned reference by an unconditional reference; using the source's expected blue count instead of the deployed policy's count; and carrying the old looser filter bound into the new 0.05 target. The final argument makes none of these substitutions.

The failure output is `|g0><g0|_S tensor Tr_S[Q rho Q]`, with its actual subnormalized reference state. The sharp complete-output preparation bound `(delta+sqrt(4 delta-3 delta^2))/2` follows by pure-state block diagonalization and partial-trace contraction. For the actual low-spectral filter, the retained conditional G mean is no larger than the original mean: the retained spectrum lies below every rejected spectral value. This result cannot be generalized to arbitrary postselection.

The unbounded blue generator satisfies `B^2=G+I-2P_e<=G+I` as a quadratic-form statement. Finite energy places a purification in the domain needed for `||(exp(-i beta B)-I)psi||<=|beta| ||B psi||`; the proof does not require the operator domain of `B^2`. Telescoping uses no-blue reference prefixes, whose energy is conserved, and true suffixes, which contract the norm. The deployed visible-history law has expected selected-blue count exactly one. Consequently its full-record omission error is at most `|beta| sqrt(nbar+1)`.

The original seven-leaf source computes the acceptance effect `s(q)^2 I`. Thus its normalized successful target is itself a normal CPTP map, and preparation error contracts directly. No generic posterior amplification factor has been omitted. For non-scalar acceptance, the separate success-floor contract remains necessary.

The final sufficient bound at `nbar=1`, `N=4095`, and independently supplied `|beta|<=0.01` is

`1/50 + (1+sqrt(16381))/8192 + sqrt(2)/100 = 0.04988777535926672669... < 0.05`.

Only approximately `0.0001122246407332733` remains for additional actual complete-output errors. The looser inherited filter estimate would exceed the requirement. This is a distinction between adequate and inadequate sufficient bounds, not between physical possibility and impossibility. The existing rational checker encloses the analytic upper-bound formula with integer arithmetic and correctly avoids interpreting that enclosure as a confidence interval or a lower bound on actual error.

## 4. Cross-review of C: identifiability and costs

Every logical record probability is independent of beta. The beta=0 and beta=pi/2 vacuum examples have identical records, while the `01` conditional terminal states are orthogonal. The corresponding compiled CQ block alone contributes `156/625`, exceeding 0.05. Flag data therefore cannot supply the independent small-beta premise. The counterexample deliberately falls outside that premise and does not invalidate the conditional omission theorem.

The target and action gates must still be the same physical gates at the same shared parameter. A q-only confidence set certifies neither this matching nor the remaining small hardware error allowance. The full-design minimax value 1/50 is restricted to the frozen design interval and legal labelled policies; it is not a lower bound for every narrower calibration set.

The source attempt success probability is `s_N s^2`, including filter failure. In a measured-flag/feed-forward implementation the mean blue count is `s_N s q(1+s)`; the matched compiler's mean is `s_N`. In a specified coherent scheduling implementation these can instead be `s_N(1+s)` and `2 s_N` scheduled slots. The manuscript now explicitly distinguishes selected branch count, scheduled hardware calls, and mathematical error weights.

The cost identity `mu/(s_N s^2)` requires fresh independent repeated preparations. Costs and success inside one attempt may be correlated; independence is needed between attempts. One-time calibration is amortized over deliveries separately. Unknown inputs and reference entanglement are not free reproducible resources. No measured cost advantage follows from a reduced pulse count.

## 5. Counterexample and next responsibility

The simultaneous interaction counterexample uses the specified self-adjoint quadrature realization `sigma_x tensor (a+a†)`. From `|+_x,0>` it produces a coherent oscillator state of amplitude `-it`; every Fock probability is strictly positive for nonzero t. This rigorously disproves transplanting the hard N+2L support statement to simultaneous dynamics. It does not disprove controlled approximation of such dynamics.

The next useful precise responsibility remains an approximate full-CQ bridge for one specified simultaneous Hamiltonian with the same classical interventions, reference, and terminal records. The admissible estimate must derive a per-prefix leakage or Duhamel boundary defect from that generator and control energy/tail growth. An exact Weyl-displacement subcase may be used to test those estimates, but generic Rabi dynamics cannot be identified with that solvable subcase. Completing this next theorem is not a prerequisite for honestly integrating the current segmented-family result.

## 6. Final scope

The four axes remain separate: analytic proofs and counterexamples are established in the declared ideal model; finite computation and exact arithmetic have source-bound retained PASS evidence; machine proof covers only inherited actual finite APIs; device membership, complete-CQ empirical precision, and resource advantage remain unverified. No Core edits, new hardware data, universal physics closure, or external human peer-review claim is supported by this review.
