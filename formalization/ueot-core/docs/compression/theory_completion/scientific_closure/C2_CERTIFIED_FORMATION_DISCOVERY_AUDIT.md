# C2 — Certified Formation Discovery Audit

Package status: **LOCAL COMPLETE / PORT OPEN**
Conclusion classes: **THEOREM + CONDITIONAL_THEOREM + METHOD + EXPLICIT BOUNDARY**
Real-world support: **UNVERIFIED**

## 1. What is machine-checked

### Ternary certification

`C2IntervalDecision.lean` defines an `IntervalCertificate` with separate
statistical and drift radii and the three-way verdict
`certified / rejected / ambiguous`.

On the declared good event:

- `decideAt_certified_sound`: certified ⇒ true value ≤ threshold;
- `decideAt_rejected_sound`: rejected ⇒ threshold < true value;
- `decideAt_ambiguous_bounds`: ambiguous means the threshold remains inside the
  unresolved interval.

No theorem converts ambiguity into a binary answer.

### Registered protocol coverage

`C2ProtocolCoverage.lean` defines `ProtocolSetSeparates`.  If every distinct
registered candidate pair has a selected protocol with true margin `γ` and all
registered response laws have TV error at most `η`, then the same selected
protocols retain empirical separation at least `γ - 2η`.

`DiscoveryCertificationSplit.not_mem_both` machine-checks the basic no-data-
reuse invariant for explicitly registered run IDs.

### Formation recovery

`C2FormationRecovery.lean` composes the existing P-STAT-02 defect stability with
an explicit drift allowance.  For every registered carrier the defect truth is
inside radius `2η + drift`.

`formedFamily_exact_of_registeredGap` exposes the existing exact finite endpoint
only when the registered predictive and carrier gaps and threshold inequalities
are actually supplied.  Unknown gap is handled by `carrierDecision`, not by an
invented finite stopping theorem.

### Correlated-sampling budget

`C2SamplingBudget.lean` deliberately proves only the arithmetic adapter:
external sampling theorem failure + `(m-1)β(b)`-shaped dependence budget can be
checked against global alpha.  It does **not** claim to derive β-mixing or a
concentration inequality from raw trajectories.

## 2. Operational data contract

`C2_DATA_DICTIONARY.md` freezes run IDs, protocol/action metadata, assignment
probability, raw observation, candidate version, declared future, cost/fault
labels, discovery/certification/holdout split and missingness reason.

The package only claims discovery inside a finite registered candidate/protocol
universe.

## 3. Executable stress evidence

`evidence/c2_stress.py` / `c2_stress.json` are **method stress tests**, not real
system evidence.  They verify the local decision implementation returns the
predeclared non-success states for:

- small gap;
- large drift;
- low protocol coverage;
- discovery/certification reuse;
- slow mixing/dependence inflation.

The test also records raw time points separately from effective blocks.

## 4. What C2 does not prove

- no general β-mixing concentration theorem is newly proved here;
- no online adaptive-intervention validity theorem is claimed;
- no unknown positive gap is magically made known to an algorithm;
- no search over all possible object encodings is claimed;
- no natural-system object has been empirically discovered;
- exact formed-family recovery remains conditional on explicit finite margins.

## 5. Package verdict

C2 closes the local **certificate logic and finite registered formation-recovery
package** required by Roadmap v2.  The broader Core §31.2 C2 port remains open
for correlated-data probability theory, adaptive designs and independent real
system certification.
