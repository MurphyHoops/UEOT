# Topology-Changing GOA Residual-Inverse Stability Audit

Status: **LOCAL LEAN PASS / STRICT RESIDUAL-INVERSE WEAKENING / UNCOUNTED**

Module:

`UEOT/V3/Compression/TopologyChangingGoaResidualInverseStability.lean`

## 1. Motivation

The stationary-branch stability hierarchy had already been weakened twice:

\[
\text{global Dobrushin}
\Longrightarrow
\text{one-step anchored}
\Longrightarrow
\text{fixed-horizon multi-step anchored}.
\]

Even the multi-step condition still asks a source iterate to contract every law
toward one selected stationary branch.  That dynamical contraction can fail in
periodic or isometric systems even when the stationary branch remains
quantitatively isolated as a solution of the fixed-point equation.

This lane therefore replaces contraction by an a-posteriori residual inverse.

## 2. Branch residual inverse

`BranchResidualInverse P hP muStar C` records:

1. `muStar` is stationary for the source kernel;
2. `C >= 0`;
3. for every law `nu`,

\[
\boxed{
D_{TV}(\mu_*,\nu)
\le
C\,D_{TV}(P\nu,\nu).
}
\]

The right side is the one-step fixed-point residual of `nu` under the source
operator.  No contraction inequality between two propagated laws is assumed.

## 3. Residual-inverse stationary tracking

`residual_stationary_tracking` combines this certificate with target invariant
existence.

Let `muhat` be any target invariant law supplied by frozen P-GOA-01.  Under a
uniform source/target row-TV defect

\[
\sup_x D_{TV}(P_x,Q_x)\le\varepsilon,
\]

the existing cross-kernel one-step theorem gives

\[
D_{TV}(P\hat\mu,Q\hat\mu)\le\varepsilon.
\]

Since `Q muhat = muhat`, this is exactly

\[
D_{TV}(P\hat\mu,\hat\mu)\le\varepsilon.
\]

Applying the residual inverse at `muhat` yields

\[
\boxed{
D_{TV}(\mu_*,\hat\mu)
\le
C\varepsilon.
}
\]

Thus the target need not share the source recurrent partition and need not be
contractive.

## 4. Multi-step anchored contraction implies a residual inverse

The module proves two auxiliary transport facts.

`iterate_nonexpansive` lifts ordinary Markov TV nonexpansiveness to every fixed
iterate:

\[
D_{TV}(P^n\mu,P^n\nu)\le D_{TV}(\mu,\nu).
\]

`iterate_increment_le_residual` then proves

\[
D_{TV}(P^{n+1}\nu,P^n\nu)
\le
D_{TV}(P\nu,\nu).
\]

Telescoping gives `iterate_to_start_le_nat_mul_residual`:

\[
\boxed{
D_{TV}(P^n\nu,\nu)
\le
n\,D_{TV}(P\nu,\nu).
}
\]

Suppose now an `m`-step anchored certificate holds:

\[
D_{TV}(P^m\mu_*,P^m\nu)
\le
\alpha D_{TV}(\mu_*,\nu),
\qquad \alpha<1,
\]

and `muStar` is stationary.  Triangle inequality plus the telescoping residual
bound gives

\[
D_{TV}(\mu_*,\nu)
\le
\alpha D_{TV}(\mu_*,\nu)
+mD_{TV}(P\nu,\nu).
\]

Therefore `residualInverse_of_multistep` proves

\[
\boxed{
D_{TV}(\mu_*,\nu)
\le
\frac{m}{1-\alpha}D_{TV}(P\nu,\nu).
}
\]

So every fixed-horizon anchored certificate induces a branch residual inverse.

## 5. Strictness witness: deterministic flip

To show the implication is strict, the module constructs the two-state
deterministic flip

\[
P=
\begin{pmatrix}
0&1\\
1&0
\end{pmatrix}.
\]

Its selected stationary branch is the uniform law

\[
\mu_*=(1/2,1/2).
\]

`residualWitnessLaw_invariant` proves exact stationarity.

For an arbitrary law `nu=(p,1-p)`, one step swaps the coordinates.  The module
proves the exact identities

\[
D_{TV}(\mu_*,\nu)=|p-1/2|,
\]

and

\[
D_{TV}(P\nu,\nu)=2|p-1/2|.
\]

Hence `residualWitness_residualInverse` proves the exact residual-inverse
constant

\[
\boxed{C=1/2.}
\]

## 6. Every fixed iterate is still an isometry

The same deterministic flip preserves distance from the uniform branch after
one step.  `residualWitness_step_isometry_from_stationary` proves

\[
D_{TV}(\mu_*,P\nu)=D_{TV}(\mu_*,\nu).
\]

By induction, `residualWitness_iterate_distance_preserved` proves

\[
\boxed{
D_{TV}(\mu_*,P^n\nu)=D_{TV}(\mu_*,\nu)
\quad\forall n.
}
\]

Taking `nu=delta_0`, whose distance from the uniform branch is exactly `1/2`,
shows that any fixed-horizon anchored inequality would require

\[
1/2\le\alpha/2,
\]

contradicting `alpha<1`.

`residualWitness_no_multistep_anchored` therefore proves that **no strict
multi-step anchored contraction exists for any horizon or factor**.

Finally `residualInverse_strictly_weaker_witness` machine-checks

\[
\boxed{
\text{residual inverse with }C=1/2
\quad\land\quad
\text{no fixed-horizon strict anchored contraction exists}.
}
\]

This is the decisive strictness result for the lane.

## 7. Updated stability hierarchy

The machine-checked hierarchy is now

\[
\text{global Dobrushin}
\Longrightarrow
\text{one-step anchored}
\Longrightarrow
\text{multi-step anchored}
\Longrightarrow
\text{branch residual inverse}
\Longrightarrow
\text{prescribed stationary-law tracking}.
\]

The last three implication boundaries have explicit finite strictness witnesses
where applicable; in particular residual inverse is strictly weaker than the
entire fixed-horizon anchored hierarchy.

## 8. Architectural interpretation

This result makes the role of M-CF more transparent.  Contraction is one way to
derive a fixed-point error bound, but the perturbation application only needs
the error bound itself.  Once that bound is abstracted as a residual inverse,
periodic/isometric dynamics can still support robust stationary-branch
semantics.

This is a bridge-level generalization.  It does not alter the frozen four-
generator core or turn the residual inverse into a counted generator.

## 9. Boundaries retained

- The residual inverse is sufficient, not claimed necessary or weakest.
- The theorem tracks one selected stationary branch, not the full invariant-law
  set in Hausdorff distance.
- The constant `C` is assumed as a certificate; this module does not derive it
  from a spectral gap or resolvent norm in general.
- The target invariant law need not be unique.
- No frozen source theorem, counted generator, P-ID disposition, or ledger count
  changes.

## 10. Next pressure test

The next scientifically meaningful step is to explain **where a residual-
inverse constant comes from** rather than weakening the abstract certificate
again by definition.

Two candidate lanes are now sharply separated:

1. derive `C` from an explicit finite-state spectral / linear-algebraic
   isolation certificate for the eigenvalue `1` on the zero-sum subspace;
2. derive a carrier-local residual inverse from a closed recurrent carrier and
   a local invertibility certificate.

Either lane should first be audited against existing finite Markov / linear
algebra infrastructure.  No claim that such a spectral certificate is
necessary or minimal should be made without a separate strictness analysis.
