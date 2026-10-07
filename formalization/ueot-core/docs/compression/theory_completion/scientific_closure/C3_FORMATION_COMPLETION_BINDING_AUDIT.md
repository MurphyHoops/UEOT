# C3 — Scalable Formation / Completion Geometry Audit

Package status: **LOCAL COMPLETE / PORT OPEN**
Conclusion classes: **THEOREM + FINITE STRUCTURED INSTANCE + CONDITIONAL THEOREM + METHOD**

## 1. Restricted search, not a universal algorithm

`C3NestedSearch.lean` formalizes one registered nested candidate family with
`n+1` candidates. `firstGoodIndex_good` and
`firstGoodIndex_no_earlier_good` prove that the returned candidate satisfies the
oracle and no earlier registered candidate does.

This is a real structural reduction relative to powerset enumeration, but only
inside the supplied nested family. It is not a polynomial-output theorem for
arbitrary minimal carriers/blockers.

The executable method benchmark compares `n+1` nested candidates with `2^n`
powerset candidates and records a frame/noise example where the selected index
changes. The benchmark is not a general complexity proof.

## 2. Parent-completion geometry / binding calibration

The current repository already contains a stronger positive mechanism than the
v2 planning documents made explicit: `CommonMarkovParentRealization`.

If parent rows are realized by applying, statewise, one common Markov channel to
assembly-level probability laws and the assembly metric dominates base-law TV,
data processing proves

`crossRowTV(K p, K q) ≤ dist(repr p, repr q)`.

`CommonMarkovParentRealization.toParentBinding` therefore derives
`ParentBindingLipschitz` with **L = 1**.

`C3BindingCalibration.commonMarkov_calibrates_parentBinding` exposes both the
calibrated constant and rowwise inequality as the C3-04 positive benchmark.

## 3. Why this does not universalize binding

The realization identity, common channel, probability laws and metric-TV
comparison are independent domain hypotheses. Generic UEOT does not prove that
an arbitrary parent completion has this factorization. Existing ParentBinding
no-go results remain active.

Hence the calibrated outcomes are:

- `DERIVED_L1` for a verified common-Markov realization;
- supplied/empirical `L_bind` for other domains, with provenance;
- `UNIDENTIFIED` or `NONREGULAR` when no valid bound is available.

## 4. Noise / physical frame boundary

Pure hypergraph/blocker algebra acts on declared finite components. A physical
frame must separately map real perturbations/failures to those components.
The local stress benchmark demonstrates that perturbing the measured defect
profile can change the selected nested candidate. It does not establish a
universal noise model.

## 5. Verdict

C3 closes one structured algorithmic special case and one nontrivial binding-
calibration mechanism. The general Core §31.2 C3 port remains OPEN for
output-sensitive arbitrary hypergraph dualization, noisy oracle complexity and
domain-specific physical-frame certification.
