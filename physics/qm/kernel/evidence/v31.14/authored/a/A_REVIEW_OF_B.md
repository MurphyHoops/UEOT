# A's independent cross-review of B: persistent dynamics and physical numerics

Review date: 2026-11-14 (Asia/Shanghai). Reviewer: native agent A; B is the
author of the reviewed dynamics. This is internal AI cross-review, not
external human peer review. Source identities and the eight actual reviewed
certificate hashes are in `A_REVIEW_B_CHECK.json`.

## Verdict

**PASS for the declared source-model, all-input analytic and stored-map
certificate scopes after one execution-metadata correction.** The evidence
does not certify hardware, a full experimental process tensor, general
Gaussian numerical accuracy, or independent selection of quantum dynamics
by Core.

The inspected sources are B's `B_DYNAMICS_PROOF.md`, `dynamics.py`,
`interval_certificate.py`, eight files named by
`interval_certificate_index.json`, and the strict fixed-source memory
event witness and its source. The review read the actual formulas and code
and independently parsed the exported exact arithmetic; it did not merely
accept B's status field.

## 1. Actual cross-questioning and resolved issue

The master agent and A asked for the direction of the unbounded Duhamel
expansion, the retained reference and stop-record quantifiers, and a physical
interpretation of rounded Choi outputs. The reviewed proof uses the true
unitary on the left of the finite remainder, with coupling factors acting
from the right on finite-support states. The numerical deliverable was
upgraded from an approximate matrix to an exactly specified repaired CP/TP
instrument, with its repair cost included.

A found a specific execution-identity bug: the `certificate` function's
`cutoff=20` argument was shadowed by a later loop ending at 24. The actual
Galerkin run used 20, but the returned metadata would have said 24. A sent
the finding to B and the master. B changed the loop variable to
`cutoff_probe`, preserved the original artifacts, added an explicit K20
assertion and regenerated all eight certificates. A's independent read-back
confirms K20 and current source hashes in every corrected Galerkin record.
No mathematical source, nominal parameter or predicted channel was changed
by this correction.

## 2. Microscopic and operational proof audit

* **Self-adjoint source:** the finite linear field has relative bound zero
  against the positive-frequency bath energy; the explicit displacement
  representation agrees with the stated domain. Infinite-mode and IR/UV
  extensions are separately open.
* **Persistent history formula:** the factor is
  `Tr(W_s sigma W_r^dagger)`, including the Weyl exchange phase and the
  rotated Gaussian mean/covariance. The off-diagonal history pairs are
  retained. Full covariance prevents an implicit product-state replacement
  of correlated modes. A conditional bath is not assumed Gaussian.
* **Reference and causality:** each history coefficient multiplies the
  actual system operator tensor identity_R. Positivity follows from the
  microscopic dilation/positive history Gram matrix; summing the complete
  F/P test establishes the prefix normalization. The actual accepted effect
  is nonscalar, while its uniform probability bounds follow from operator
  inequalities, not from an assumed scalar effect.
* **Energy:** the complete-record dilation commutes with bath number during
  system-only controls. Its unconditional bound does not apply unchanged to
  every normalized rare branch. Free evolution padding of stopped branches
  preserves their terminal SR output.
* **Finite Duhamel:** the first K interaction terms from vacuum remain in
  total occupation at most K, inside the product cutoff. The true-left
  remainder has K+1 finite-support coupling factors, so the successive
  square-root norm factors and the time-simplex volume are justified.
  The compressed remainder has the same bound. Adding them gives `2 c_(K+1)`.
  No uncontrolled right action on a true infinite-tail state or infinite
  Dyson-series convergence assumption is needed.
* **All-input quantifier:** purification of arbitrary SR, together with a
  complete finite record dilation, permits the vector bound to pass to the
  full terminal CQ trace distance. Ancillary dimension does not enter the
  coupling norm. This establishes the analytic half-diamond scope for a
  fixed policy, with the separately stated control-budget extension.
* **Actual boundary residual:** the two outgoing rectangular faces are
  orthogonal, which yields the diagonal `R_K^dagger R_K` expression. The
  branch-weighted bound uses finite-reference prefix mass and occupation.
  It is not evaluated by claiming ordinary quadrature to be rigorous.
* **Parameter stability:** the field norm is controlled on the infinite
  source before the truncation term is added. The conservative 51/10
  constant is above the displayed 4.233642... bracket and below no required
  threshold. Swapped durations share the same total exposure.

These are reviewed mathematical arguments. The finite computation is not
presented as a replacement proof of their universal quantifiers.

## 3. Independent exact read-back of eight numerical certificates

`review_b.py` does the following without calling B's certificate builder:

1. Reads exact dyadic interval endpoints and exact stored binary64 values.
2. Computes an upper bound for each squared-entry error using `Fraction`.
3. Bounds its square root upward by an integer-square-root rational
   construction, giving an independent bound on `2 sum ||Delta J||_F`.
4. Confirms the bound is below `10^-12` and reconstructs the declared
   rational Hermitianization, delta addition, scaling and failure-block
   residual.
5. Checks exact Hermiticity and the partial-trace identity `I/2`.
6. Checks **all 504 principal minors** of the 32 repaired 4-by-4 blocks and
   eight 2-by-2 residuals in exact rational complex arithmetic. Every minor
   is nonnegative. This supplies an additional exact physicality check of
   the actual exported maps.

The stated physical-repair inequality `a(40 delta+2 e)` is correct for this
four-label normalized qubit Choi convention. Since input dimension is two,
the sum-of-Choi-trace-norm bound is also a half-diamond upper bound. It is
not missing a factor of two. Exact arithmetic defines the exported
predictor; subsequent floating application has its own rounding scope.

## 4. A/B interface gate: tensor order and normalization are explicit

B stores normalized Choi blocks in **output S tensor input/reference**
order. A's `FiniteTest.choi_blocks` uses unnormalized Choi blocks in
**input tensor output** order. The independently tested conversion is

\[
C_A=2\,\mathrm{SWAP}\,J_B\,\mathrm{SWAP},
\qquad\text{permutation }(0,2,1,3).
\]

For the nominal lambda=3/10 original-source rational repair, numerical
spectral extraction supplies a finite Kraus representation only as a guard;
the exact physicality checks above retain the proof responsibility. A's
four preparations and four binary effects reproduce B's directly contracted
probabilities to `3.34e-16`. Reconstructing the complete output for an
independently chosen mixed state with reference dimension three differs
from B's direct Choi action by `3.57e-16` in full CQ trace distance.

The interface negative controls are effective: omitting the normalization
factor gives completeness error 0.5; omitting SWAP changes a test probability
by about 0.360069. Thus the passing interface is not an accidental agreement
on a maximally mixed or purely classical input.

The repaired-vs-infinite-source distance on this additional input is about
`9.33e-10`; it is reported as a finite supplementary check. The universal
bound continues to come from the exact Choi certificate.

## 5. Memory claims remain separated

B's strict fixed-source event is `ppp AND X_S tensor X_R=+1`, using the
original three-slot controls and a Bell input. A reads the two probability
enclosures and independently subtracts their rational endpoints. The reset
competitor's event probability exceeds the persistent source's by more
than `3/100` (display: 0.03164037538529124). This gives a strict lower bound
on the full output trace distance. It does not rely on treating the
floating trace distance 0.101251856... as a rigorous interval result.

A's P-QMEM-02 causal-break experiment is a different, explicitly declared
diagnostic. It supplies a rank/memory-dimension lower bound. It is not used
to replace B's fixed-source event or silently change the calibration source.

## 6. Remaining scope limits

The exact rational repair is one fixed-policy terminal CQ instrument. It
does not repair or certify all counterfactual multi-time interventions.
General Gaussian history formulas are analytic; all frozen numerical and
calibration evidence uses vacuum. The preparation, Hamiltonian, allowed
controls, readout model and external dimension remain independent physical
premises. Real-device status therefore remains untested/not certified.

No unresolved mathematical obstruction to integration was found in this
reviewed scope. All review evidence is bound to the source hashes in
`A_REVIEW_B_CHECK.json`; a later source change requires an appropriately
scoped re-review rather than reuse of this statement without checking.
