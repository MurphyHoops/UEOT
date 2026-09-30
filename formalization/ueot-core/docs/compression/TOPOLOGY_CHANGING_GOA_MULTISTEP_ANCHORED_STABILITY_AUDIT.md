# Topology-Changing GOA Multi-Step Anchored Stability Audit

Status: **LOCAL LEAN PASS / STRICTLY WEAKER MULTI-STEP BRANCH CERTIFICATE / UNCOUNTED**

Module:

`UEOT/V3/Compression/TopologyChangingGoaMultiStepAnchoredStability.lean`

## 1. Why move beyond one-step anchored contraction

The previous lane replaced global pairwise Dobrushin contraction by a weaker
one-sided condition around one selected invariant law `muStar`:

\[
D_{TV}(P\mu_*,P\nu)
\le
\alpha D_{TV}(\mu_*,\nu),
\qquad \alpha<1.
\]

That condition is already strictly weaker than global Dobrushin contraction,
but it is still a **one-step** requirement.  Some finite systems do not contract
the selected branch after one step even though a fixed iterate does.

The present lane isolates exactly that possibility.

## 2. Markov TV nonexpansiveness and finite-horizon kernel transport

`dobrushinAlpha_le_one` proves for every finite stochastic kernel

\[
\alpha_{Dob}(P)\le1.
\]

Combining this with the existing Dobrushin one-step inequality gives
`tv_step_nonexpansive`:

\[
\boxed{
D_{TV}(P\mu,P\nu)\le D_{TV}(\mu,\nu).
}
\]

This does not require strict contraction.

`iterate_cross_le_nat_mul` then compares two stochastic kernels `P,Q` started
from the same law under a uniform row-TV defect

\[
\sup_x D_{TV}(P_x,Q_x)\le\varepsilon.
\]

By induction using TV nonexpansiveness, triangle inequality, and the existing
same-input cross-kernel one-step theorem,

\[
\boxed{
D_{TV}(P^n\mu,Q^n\mu)
\le n\varepsilon.
}
\]

This is the finite-horizon bridge needed to use an iterate-level contraction
certificate against an ordinary one-step kernel perturbation bound.

## 3. Multi-step anchored contraction

`MultiStepAnchoredLawContraction P hP muStar steps alpha` records:

- `steps > 0`;
- `0 <= alpha < 1`;
- for every probability law `nu`,

\[
D_{TV}(P^{m}\mu_*,P^{m}\nu)
\le
\alpha D_{TV}(\mu_*,\nu),
\qquad m=\texttt{steps}.
\]

No one-step anchored inequality is assumed.

`multistep_one_of_anchored` proves the previous one-step interface embeds at
`steps = 1`, so this is a genuine extension of the prior branch-stability API.

## 4. Multi-step stationary tracking

`multistep_anchored_stationary_tracking` assumes:

- finite stochastic source `P`;
- selected source invariant law `muStar`;
- an `m`-step anchored contraction factor `alpha < 1`;
- finite stochastic target `Q`;
- uniform one-step row-TV defect `epsilon`.

Frozen P-GOA-01 supplies a target invariant law `muhat`.  Since both source and
target invariant laws are fixed by every iterate, the proof compares

\[
\mu_*
\to
P^m\hat\mu
\to
Q^m\hat\mu=\hat\mu.
\]

The first leg is controlled by the multi-step anchored certificate, while the
second leg is bounded by `m epsilon` from `iterate_cross_le_nat_mul`.

Solving the scalar inequality gives

\[
\boxed{
D_{TV}(\mu_*,\hat\mu)
\le
\frac{m\varepsilon}{1-\alpha}.
}
\]

As before, the target need not be contractive and need not preserve the source
recurrent partition.

## 5. Strictness witness

To show the multi-step certificate is substantively weaker than one-step
anchored contraction, the module constructs a three-state kernel:

\[
0\to0,\qquad
1\to2,\qquad
2\to0.
\]

The selected stationary branch is the point mass `delta_0`.

`multiStepWitnessLaw_invariant` proves `delta_0` is invariant.

For an arbitrary law `nu`, the first step has coordinates

\[
(\nu_0+\nu_2,\;0,\;\nu_1),
\]

and `multiStepWitness_twoStep_collapse` proves

\[
\boxed{P^2\nu=\delta_0\quad\text{for every }\nu.}
\]

Therefore `multiStepWitness_twoStep_anchored_zero` proves an exact two-step
anchored factor

\[
\boxed{\alpha_2=0.}
\]

## 6. One-step anchored contraction genuinely fails

Take the comparison law `delta_1`.  One step sends it to `delta_2`, while the
selected branch remains `delta_0`.

The module proves

\[
D_{TV}(\delta_0,\delta_1)=1,
\qquad
D_{TV}(\delta_0,\delta_2)=1.
\]

Hence any one-step anchored inequality would force

\[
1\le\alpha,
\]

contradicting `alpha < 1`.

`multiStepWitness_no_oneStep_anchored` therefore proves that **no strict
one-step anchored certificate exists for any factor**.

Finally `multistep_strictly_weaker_witness` machine-checks the conjunction

\[
\boxed{
\text{two-step anchored factor }0
\quad\land\quad
\text{no strict one-step anchored factor exists}.
}
\]

This is the decisive strictness result for the lane.

## 7. Architectural interpretation

The stability hierarchy is now

\[
\text{global Dobrushin contraction}
\Longrightarrow
\text{one-step anchored contraction}
\Longrightarrow
\text{multi-step anchored contraction}
\Longrightarrow
\text{prescribed stationary-law tracking}.
\]

Both weakenings are machine-checked as strict by explicit finite witnesses.

The new lane also reconnects two existing compression themes:

- M-CF contributes the fixed-point perturbation logic;
- M-TC-style finite transport accumulation appears in the `m epsilon` iterate
  defect bound.

No fifth counted generator is introduced.

## 8. Boundaries retained

- The multi-step certificate is sufficient, not claimed necessary.
- The linear `m epsilon` accumulation is safe and general; no optimality claim
  is made for that constant.
- The theorem tracks one selected invariant branch, not the full invariant-law
  correspondence in Hausdorff distance.
- The target invariant law supplied by finite existence need not be unique.
- No frozen source theorem, counted generator, P-ID disposition, or ledger count
  changes.

## 9. Next pressure test

The next weakening should no longer be obtained merely by increasing a fixed
iterate horizon.  The natural candidates are:

1. a quantitative residual/fixed-point inverse certificate local to the
   selected branch;
2. a spectral/isolation certificate for one stationary branch;
3. a variable-horizon or eventual anchored contraction condition, provided it
   yields a genuinely new theorem and not just a restatement of the fixed-
   horizon case.

Before opening any of these lanes, the current multi-step result should be
audited as a complete checkpoint and its strictness witness reviewed
independently.
