# Topology-Changing GOA Anchored Stability Audit

Status: **LOCAL LEAN PASS / STRICTLY WEAKER BRANCH STABILITY CERTIFICATE / UNCOUNTED**

Module:

`UEOT/V3/Compression/TopologyChangingGoaAnchoredStability.lean`

## 1. Why weaken global Dobrushin contraction

The previous topology-changing GOA stability lane proved a clean sufficient
certificate:

\[
\alpha(P)<1
\Longrightarrow
D_{TV}(\mu,\hat\mu)
\le
\frac{\varepsilon}{1-\alpha(P)}.
\]

That certificate is global: every pair of probability laws is contracted by
the source Markov operator.

The actual stationary perturbation proof uses less.  To track one selected
source stationary branch `muStar`, it is enough to contract distances **from
that branch** to arbitrary comparison laws.  Pairwise contraction between two
unrelated laws is not used.

## 2. Anchored contraction

`AnchoredLawContraction P hP muStar alpha` records:

- `0 <= alpha`;
- `alpha < 1`;
- for every law `nu`,

\[
D_{TV}(P\mu_*,P\nu)
\le
\alpha D_{TV}(\mu_*,\nu).
\]

When `muStar` is invariant, `P muStar = muStar`, so this is a radial/anchored
contraction toward the selected stationary branch.

It makes no claim that

\[
D_{TV}(P\mu,P\nu)
\le
\alpha D_{TV}(\mu,\nu)
\]

holds for arbitrary `mu,nu`.

## 3. Anchored stationary tracking

`anchored_stationary_tracking` assumes:

- finite stochastic source `P`;
- selected source invariant law `muStar`;
- anchored factor `alpha < 1` around `muStar`;
- finite stochastic target `Q`;
- uniform row-TV defect at most `epsilon`.

It proves there exists a target invariant law `muhat` with

\[
\boxed{
D_{TV}(\mu_*,\hat\mu)
\le
\frac{\varepsilon}{1-\alpha}.
}
\]

The target may change recurrent topology and need not be contractive.  Target
invariant-law existence still comes from frozen P-GOA-01.

The proof is the exact fixed-point perturbation inequality specialized only to
the selected branch:

1. triangle through `P muhat`;
2. anchored source contraction controls the first leg;
3. row-TV kernel defect controls `P muhat` versus `Q muhat`;
4. target invariance closes the second leg;
5. solve the scalar inequality with `alpha < 1`.

## 4. Relation to the global certificate

`anchored_of_dobrushin` proves

\[
\alpha_{Dob}(P)<1
\Longrightarrow
\operatorname{AnchoredLawContraction}
(P,\mu_*,\alpha_{Dob}(P))
\]

for every selected law `muStar`.

`prescribedInvariant_tracked_via_anchored_of_dobrushin` then reconstructs the
previous global-Dobrushin tracking theorem through the anchored interface.

Therefore the new interface is compatible with, rather than parallel to, the
existing M-CF/Dobrushin route.

## 5. Strict weakening witness

To show the new condition is not merely a renamed global certificate, the
module constructs an explicit four-state kernel.

The selected stationary branch is

\[
\mu_*=(1/2,1/2,0,0).
\]

The kernel rows are

\[
P_0=P_1=(1/2,1/2,0,0),
\qquad
P_2=(1,0,0,0),
\qquad
P_3=(0,1,0,0).
\]

`strictWitnessLaw_invariant` proves `muStar` is invariant.

The exact one-step radial distance is derived in
`strictWitness_lawTV_step`:

\[
D_{TV}(\mu_*,P\nu)
=
\frac12|\nu_2-\nu_3|.
\]

The initial TV distance satisfies

\[
\nu_2+\nu_3
\le
D_{TV}(\mu_*,\nu),
\]

and

\[
|\nu_2-\nu_3|
\le
\nu_2+\nu_3.
\]

Hence `strictWitness_anchored_half` proves

\[
\boxed{
D_{TV}(\mu_*,P\nu)
\le
\frac12D_{TV}(\mu_*,\nu)
}
\]

for every law `nu`.

## 6. Global Dobrushin still fails

The same kernel has

\[
D_{TV}(P_2,P_3)=1.
\]

`strictWitness_rowTV_two_three` proves that equality exactly, and
`strictWitness_dobrushinAlpha_eq_one` proves

\[
\boxed{\alpha_{Dob}(P)=1.}
\]

Therefore `anchored_strictly_weaker_witness` machine-checks the conjunction

\[
\boxed{
\text{anchored factor }1/2
\quad\land\quad
\neg(\alpha_{Dob}(P)<1).
}
\]

This is the key scientific result of the lane: anchored stationary-branch
stability genuinely covers finite kernels excluded by global Dobrushin
contraction.

## 7. Interpretation

The stability boundary is now more refined than

`global contraction / no contraction`.

The formal hierarchy is

\[
\text{global Dobrushin contraction}
\Longrightarrow
\text{anchored branch contraction}
\Longrightarrow
\text{prescribed stationary-law tracking}.
\]

The first implication is strict by the four-state witness.

This is important for topology-changing GOA semantics: bad transient or remote
rows can make the global Dobrushin coefficient equal to one even while one
selected long-run branch remains robustly attracting in exactly the direction
needed for perturbative tracking.

## 8. Boundaries retained

- Anchored contraction is **sufficient**, not claimed necessary.
- No claim is made that factor `1/2` in the witness is optimal.
- The theorem tracks one selected stationary branch; it does not imply full
  Hausdorff continuity of the entire invariant-law correspondence.
- The target still only needs existence of an invariant law; uniqueness is not
  concluded without additional assumptions.
- No frozen source theorem, counted generator, P-ID disposition, or ledger
  count changes.

## 9. Next pressure test

The next possible weakening should target the anchored condition itself rather
than retreat to a carrier-label argument.  Candidate routes include:

1. a quantitative fixed-point inverse/residual bound local to `muStar`;
2. a spectral/isolation certificate for one stationary branch;
3. multi-step anchored contraction, where one-step contraction fails but a
   fixed iterate contracts around the selected branch.

The multi-step route is especially natural in periodic or slowly mixing finite
systems and can reuse M-CF after passing to an iterate.  Any such weakening
must again include a strictness witness before being treated as a substantive
new layer.
