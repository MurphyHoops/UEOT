# A independent review of B and the actual integration

Review type: internal native-AI cross-review, not external human peer review.
Recovery baseline: `aea2fceef3c62cc8dc749b6cbb1b40a7d89df80d`.
This review is newly performed in the recovery session. The missing unpublished
v31.12 workspace and its past execution outputs are not claimed recovered.

## Reviewed material

- B's complete reconstructed `B_MICRO_GROWTH.md`, especially (B.9), (B.23),
  (B.24), the failure-reference formula and source acceptance calculation.
- The actual new `audits/GROWING_CUTOFF_v31.12/SHARED_MODEL.md` and
  `growing_cutoff/frozen_model.json`.
- The actual new `growing_cutoff/model.py` and `verify_integration.py`.
- The inherited v31.11 shared model and Chapter 67 for prior source, labels,
  robust weights, sharp physical-filter bound and formalization boundaries.

## Attack 1: Is the full adaptive-CQ truncation bound obtained from the source?

The strongest claim is B.9's uniform bound for every admitted finite classical
tree and finite untouched reference. The attack was to look for a hidden assumption
of the requested intertwining, a fixed-cutoff compression, missing stopping mass,
or an equality only on final marginals.

**Finding: the written proof is valid in its declared separated-pulse family.**
The block formula derives blue propagation `P_M -> P_(M+2)` for all real beta.
Red and phase controls preserve the cutoff. Rectangular branch completeness
follows from that range identity and the original instrument's identity effect.
The tree induction retains every stopped record, and terminal blocks are compared
after a common embedding. The initial projection estimate is paid once before a
normal CPTP map; no unproved repeated-tail or average-energy replacement is used.
Tensoring the actual intertwining with identity keeps initial entanglement with R.

The integrated model uses uniform depth windows `N+2j`. A's independent proof
uses the smaller windows `N+2 count_1(h)`. Canonical padding makes these equivalent;
neither proof claims that zero/failure events inject excitation. The seven-leaf
runtime uses actual embedded states on every leaf. Its square ambient interpreter
is a completion valid on the reached columns, and the implementation expressly
does not claim it equals the oscillator unitary on every boundary vector.

Fixed-cutoff compression is defeated by the explicit `sin^2(beta sqrt(N+1))`
lost probability. The simultaneous Rabi example supplies an actual infinite-tail
counterexample. These negative results correctly restrict, rather than certify,
the corresponding positive extensions.

**Clarifications requested and resolved in B:** hidden refinements must mean Kraus refinements of
admitted events, or independently source-derived range-preserving refinements;
they do not license adding arbitrary hidden operations. Define the normalized
finite `rho_N` with its isometric coordinates before using it in both finite and
physical formulas. These are quantifier/type clarifications, not a counterexample
to the actual two-step source. A read back B's corrections: the allowed refinement
now has an explicit source/equivalent-event condition and a positivity argument;
the finite normalized input is explicitly defined and its energy convention
states restriction or embedding.

## Attack 2: Does the small final error secretly omit failures, energy growth,
or a postselection denominator?

The attack was directed at B.23/B.24: compare the real filtered reduced compiler
with the unfiltered conditioned target, keeping the same parameter and reference.

**Finding: the composed bound is valid as a conditional mathematical certificate.**
The preparation failure state is the correct local-reset output
`tau_S tensor Tr_S(Q rho Q)`, with its unnormalized conditional R state. Replacing
it by the unconditional reference gives the independently checked `1/4` error
counterexample. The preparation failure remains a separate complete-output block.

The inherited sharp filter bound applies. The low spectral filter preserves the
mean-excitation upper bound; the overbroad Chapter 67 warning is explicitly
corrected. Telescoping the blue-pulse omissions uses **no-blue** prefixes, whose
energy is preserved; actual growing-energy prefixes are not incorrectly reused
as low-energy inputs. The identity `B^2<=G+I` then gives the local error. The
deployed path law's expected label-one count is exactly one, so the complete
record-weighted coefficient is one. This is not an unweighted two-slot norm
claim or a replacement of the deployed law by the target's `2q` count.

The original acceptance effect is independently derived as `s^2 I`; target
normalization is input-independent and hence CPTP. Therefore the absence of an
extra `1/s^2` factor is justified for this example. State-dependent accepted
processes retain the positive-success and conditioning-amplification obligations.

Numerically the sufficient bound is `0.04988777535926673`, below the frozen
`0.05` threshold, with about `0.00011222464073327` margin. The old loose filter
bound would fail the same threshold. Independent pulse-area, gate matching,
filtering, readout and effective-Hamiltonian error controls remain required for
any real apparatus claim; flag data do not establish them.

## Additional implementation checks

The root recursion applies `V1=B_beta U1` in the declared order, keeps all seven
raw and conditional record slots, and handles original failures with identity
at the correct reached carrier. The finite conditioning consumer derives the
backward effect from the actual instrument. The filter integration embeds both
the ideal and actual outputs into the same carrier and explicitly checks total
trace. The wrong-reference and same-flags/different-beta controls target genuine
semantic errors.

Two nonblocking wording corrections were requested and read back as resolved:
observation weights are
equal **within** each fibre, not necessarily across distinguishable histories;
the separately implemented ambient completion is a closed-form block unitary,
not a call to a matrix-exponential numerical routine. A's independent checker
does use an exponential of the explicit Hermitian generator as a different
construction.

## Independent evidence and verdict

A separately authored `check_operational_growth.py`, importing no project runtime,
and actually executed 68 checks. The checks include exact rational policy counts
and floating diagnostics for rectangular isometries, explicit-generator
exponentials, seven-leaf completeness, acceptance effect, terminal embeddings,
an entangled reference, complete record distance, filtering controls and the
precision threshold. `A_INDEPENDENT_CHECK.json` records this new execution and
its script hash. B also supplies its own independently executed finite checks;
the written universal conclusions do not depend on treating either numerical
sample as a proof over all states.

**Verdict:** PASS for the stated paper-level separated finite-pulse bridge and
the inspected root operational composition, with the minor clarifications above
resolved. No new Lean coverage, hardware calibration,
empirical closure, generic simultaneous-Rabi closure or whole-physics completion
is inferred. The review does not certify files changed after this inspection;
the root source manifest and final readback must bind the delivered version.
