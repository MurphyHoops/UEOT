# SISC v2 — mechanism→candidate distinction→formed finite paths

Status: **LOCAL LEAN-CHECKED UNDER DECLARED PREMISES**. Not an independent
physical identity discovery. This follow-up addresses A-01, A-02 and A-03 of
`SISC_INDEPENDENT_REAUDIT_V2.md` without rewriting any earlier stage commit.

## 1. From mechanistic formation to operational successor identification

`SISCFormationIdentityBridge.lean` connects original SI-3 directly to the
uniqueness question. `finite_mechanism_unique_formed_successor` requires:

- normalized finite response channel (unchanged SI-3 infrastructure);
- source formation and quantitative lower-world and model-parent prediction
  evolution bounds; SI-3 **constructs** the target `tp p` as formed;
- an independently measured causal predecessor/target edge `edge p (tp p)`;
- a *registered local response gap*: every distinct competitor `q` differs
  from `tp p` by more than twice the target formation tolerance at **some**
  observed coordinate.

It proves that the transported formed causal target is unique among **all
declared P1 completions** satisfying formation at the target lower state.
The theorem's `hgap` is not `SameObject`, a global selector or a definition of
uniqueness; it is a discriminating independent measurement hypothesis whose
violations can be observed (e.g. copy with the same responses). The strict
threshold `2*tau_target` is required by the triangle inequality and cannot
be omitted. `zero_formation_error_does_not_identify_parent` retains a finite
clone counterexample even at zero formation mismatch.

The present result does **not** derive the causal edge from lower dynamics,
does not calibrate parent candidate coverage from nature, and cannot promote
an operational unique match to ontological identity.

## 2. From SI-3 directly to n-step formation/realization continuity

`SISCMechanisticPaths.lean` closes the previous missing composition point.
For a homogeneous finite response channel, deterministic lower-state and
parent transports `tx,tp`, uniform world/parent response-evolution error
budgets, and an independent binding-transport/Lipschitz certificate, it
constructs the **pair-valued** path `(x_t,p_t)` for every finite horizon n.

The two conclusions are simultaneously derived:

`FormedByResponse actual predict tau_n x_n p_n`, where
`tau_(n+1) = deltaWorld + tau_n + deltaParent`;

`dist (B p_n) (T^[n] (B p_0)) ≤ D_n`, where
`D_0=0; D_(n+1) = deltaBind + M*D_n`.

The theorem does **not** use an assumed global `∀p,∃q hStep` from SI-4;
the path's next formation witness is **proved using SI-3 at each step**. It
reuses SI-4's `DirectedFinitePath`, `iterateResponse` and error recurrence.
There is still a fixed, supplied `tp`, and the binding defect is an external
calibration obligation. The theorem does not assume structural split/merge,
nor claim unbounded horizon control of the growing `tau_n`.

## 3. Remaining decisive open problems

1. Derive a nontrivial parent candidate set and its transport (or show
   impossibility) from independently intervened stochastic lower dynamics;
   `tp` must no longer simply be the *chosen* matching representation.
2. Estimate a credible high-probability simultaneous response error and
   registration coverage under dependent/noisy data, with predeclared
   multiplicity and possible abstention.
3. Extend compatible histories to changing response-protocol spaces and
   branching/merging with lineage graph witnesses rather than forcing one
   object identity.
4. Independently test the sequence of premises and outputs on a separately
   administered system. Existing SQLite self-method pilot does not suffice.

This is a **post-Core conditional scientific bridge**, not an additional
counted generator or a closure of Core §31.2 C4.
