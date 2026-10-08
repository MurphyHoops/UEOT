# N3 — verified three-way candidate resolver: concrete finite examples

**Source:** `SISCRegisteredCandidateExamples.lean`. Local Lean 4 kernel compilation under the already proven N3 resolver; no real physical data.

All three systems share a **real normalized finite Markov kernel** on one lower-state token and one action. Post-action expected response is 0 on the single registered measurement coordinate. Two Boolean candidate tokens are registered; both are admitted by the separately declared causal predicate. The decision threshold is 1.

1. **Unique**: candidate false predicts response 0 (true risk 0, exact interval 0), candidate true predicts response 3 (true risk 3, exact interval 3). The C2 risk intervals certify false and reject true. The resolver returns `unique(false)`. The proof constructs the resulting candidate from a singleton *possible* class rather than assuming a chosen transporter.
2. **Ambiguous**: false remains certified, but the other candidate's interval is centered at true risk 3 with radius 3. Its interval crosses threshold 1, so candidate true cannot be safely rejected. With two statistically possible candidates, the resolver **must** return `ambiguous` despite the one already certified false candidate.
3. **Uncovered**: both candidates predict response 3 against a true response 0 and have exact risk interval 3. Both are rejected at tolerance 1, so the result is `uncovered` with respect to the registered model, not a declaration that no physical object exists.

All three protocols satisfy `RegisteredCausalCandidateProtocol.Calibrated` **as Lean theorems**, rather than injecting a bogus simultaneous-good-event witness. The new examples exercise exact unique selection, evidence uncertainty and true model noncoverage.

The examples do not independently establish that the declared causal predicate is a true experimental provenance relation or that there are no unregistered physical successors. Thus the result is **operational** and finite, not ontic.

This is intentionally separate from prior `InverseObjecthood.FiniteCandidateRecovery` (unique ERM minimizer under risk gap) and `C3NestedSearch` (least good member of a nested chain). The new contribution is the C2 abstention discipline under a fully registered causal candidate universe, connected to the concrete N1 source stochastic response.
