# RLSR-T5 — recovered joint path-law audit

Status: **LOCAL PASS**

## Result

The strengthened RLSR no longer stops at one-step correspondence between the
mode-free organizational kernel and the reconstructed program's physical kernel.
For each fixed reconstructed program `r`, the canonical recovered organizational
manifold is defined and proved canonically equivalent to the physical state space.

A Markov kernel `recoveredSafeKernel` is constructed on that manifold.  Lean proves:

1. its PMF transition, after forgetting the manifold proof, is exactly the existing
   `safeRepairKernel` transition on the underlying canonical organization state;
2. physical projection is a strong lumping to `stationaryKernel P (T.execute r)`;
3. by the repository's existing Ionescu--Tulcea path naturality theorem, the complete
   recovered organizational path law projects exactly to the reconstructed program's
   physical Markov path law.

Thus the post-reconstruction infinite stochastic process is one joint process, not
merely a sequence of separately composed one-step/physical statements.

## Boundary

The path theorem starts on the canonical recovered manifold.  A damaged one-replica
state is related to this manifold by the already machine-checked T2 theorem: the first
`safeRepairKernel` step masks the program/controller fault before selecting its physical
action and returns a canonical organizational state.  A separate stochastic process
of exogenous recurrent faults is still outside this theorem; T2 only proves stepwise
masking whenever the current representation is within the one-replica correction class.
