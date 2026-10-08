# N6-A — passive parent ambiguity, active intervention identification

Source: SISCInterventionParentIdentification.lean. Status: locally Lean-checked conditional finite demonstration. No real-world intervention is claimed.

Reused exact existing P4 InverseObjecthood declarations (ObjectClassIdentifiedByEvidenceAmongValid, equalitySetoid, literalCandidate_not_identified_of_valid_sameEvidence). We did not reprove abstract identifiability from scratch.

The two Bool parent hypotheses have a registered real-valued probe response:
- passive probe (false): response 0 for either parent;
- active probe (true): response 0 for parent false and 1 for parent true.

Lean proves passive equality, active inequality, P4 non-identification by passive-only evidence, and P4 identification of literal labels when the active probe is added. Thus interventions can change the identifiability of a declared parent-model class, but nothing in these proofs establishes that the active label corresponds to an experimentally valid, causally isolated manipulation. Such fidelity and genealogy/identity contracts remain separate empirical gates.

Next stage: combine externally registered and authenticated transfer evidence with intervention fingerprint separation. Existing SI-2 local response gap theorem will be reused to force uniqueness instead of rebuilding the response-triangle lemma.

No mutation of the frozen Core/Compression baseline, no cloud push.
