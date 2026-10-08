# N6-D — high-probability interventional parent-model identification

Source: SISCInterventionSamplingPower.lean. Status: local Lean verified; finite-sample conditional statistical theorem, not an external experiment.

## What is reused
- Prior UEOT/V3/BoundedLossTwoSided.measure_exists_candidate_bad_le: a frozen two-sided Hoeffding / finite union bound, not re-proven in N6.
- SI-2 unique_formed_target_of_local_gap, composed through the N6-B audited finite candidate set.
- P4 inverse candidate evidence semantics, already established in the project.

## Precisely what has been proved
For N independent experimental units with a jointly registered vector of outcomes indexed by a finite intervention set I, define the measured response to probe i as the empirical mean of the [0,1]-bounded outcome function over the N unit records. The operational candidate source set is computed using those means, independently registered transfer records and the existing response-matching condition.

Suppose an actual source model p is registered and independently transfer-attested to the relevant child, and the expected outcome of every registered intervention i under the measurement law equals the reference model response of p. Also suppose every alternative registered parent model is separated from p by more than 2u on at least one intervention coordinate (SI-2 LocalResponseGap).

The new machine-checked theorem yields:

P( auditedSourceCandidates(sampled records) != singleton {p} )
    <= 2 |I| exp(-2 N u^2).

The intermediate theorem proves exact singleton recovery on the simultaneous coordinate-mean good event; the final inequality is obtained by directly applying the existing P-STAT uniform deviation theorem. No guessed P8 identity or selected parent transporter is an argument to the *candidate construction*.

The bound depends on the number of registered intervention coordinates, not the number of candidate parent labels. Responses at different intervention coordinates inside one unit may be correlated; **independence of replicated experimental units** is required.

## Strong empirical caveat
The theorem's data type assumes an experimental unit record exposes the registered outcomes for all probes as measurable functions of that unit's record. This can be achieved in faithful paired/repeated experimental settings or simulated potential-outcome worlds, but ordinary single-treatment data generally do not reveal all counterfactual responses for one unit. Interventions must be actually implemented and calibrated; simply tagging passive observations with action labels does not satisfy the scientific premise.

Data-law matching, transport-record authenticity, causal intervention validity, candidate registry completeness and P8 parent/offspring physical semantics remain open external conditions. An inferred model fitted on the same held-out validation data is not automatically covered by the fixed-model theorem.

This is a theorem about operational *source-model* identification under complete declared experimental protocols, not universal physical genealogy.
