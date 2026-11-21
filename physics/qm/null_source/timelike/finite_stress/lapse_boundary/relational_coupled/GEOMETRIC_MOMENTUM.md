# The original geometric momentum, its transported domain and recovery gate

This closes a distinction left open by the preceding P_u resource test.
P_u in the q=a phi bulk coordinates contains a source-coordinate contribution.
Matching its mean alone is not matching the pure geometric canonical momentum
of the original chosen action representative. No new physical action is added.

## G1. Canonical and quantum identification

In the original phi coordinates, call the geometric Ostrogradsky momentum
Pi_g. With q=a phi and p_raw=p-kappa q, the source one-form is
p_phi dphi=(p-kappa q)dq-(p-kappa q)q du.
Adding the known endpoint d(kappa Q) to obtain the bulk representative gives
\[
 \boxed{\Pi_g=P_u+{\cal D}-2\kappa Q}.                       \tag{G1}
\]
Equivalently, the bulk source Lagrangian contains (chi+kappa²)Q, so its
P_u contribution is 2kappa Q-D.

The finite-mode coordinate map has the unitary Jacobian:
chi(u,q)=a^(-n/2) Psi(u,q/a). It transports the old fixed-phi P_u to
P_u+D_raw, with D_raw=-i(q·partial_q+n/2), the symmetric dilation.
The endpoint phase then gives D_raw=D-2kappa Q. Thus G1 has no omitted
imaginary constant. The slice weight kappa^(1/2) commutes with this
source-coordinate change. This is finite K; no infinite-dimensional
Jacobian or fixed-Fock unitary is inferred.

On the common core and physical constraint, P_u=-H_rel. The exact identity is
\[
 -\Pi_g=\frac{A_{\eta,\mathrm{cov}}}{2g}
 +\frac{\sum_r[(p_r-\kappa q_r)^2+\omega_r^2q_r^2]}{2\kappa}
 +d_0/\kappa+d_1\kappa+d_3\kappa^3
 =:G_\eta.                                                 \tag{G2}
\]
The square term is the finite-K positive **unsubtracted** source form.
All fixed AE subtractions, vacuum constants and nonzero U0 remain in
d0,d1,d3. G2 does not claim a positive renormalized continuum stress tensor.

Since W†(D-2kappa Q)W=D, G2 is also
\[
 G_\eta=W\,[A_\eta/(2g)+H_0/\kappa+d_0/\kappa+
                               d_1\kappa+d_3\kappa^3]W^\dagger.       \tag{G3}
\]
This form defines the selected slice realization; we do not define it as
an arbitrary sum of three unbounded operators on an unspecified domain.

## G2. A strong transported geometric domain in the positive confining patch

In 0<g<59/360, the expression in G3 is a closed semibounded form, including
every eta>=-1/4 with its own Friedrichs endpoint. It has the common
source/geometry form domain of ORDERING_DOMAIN.
For the full-source dilation R used in COUPLED_FORMS,
\[
 G_\eta(u)=W R(u)\widetilde H_\eta(u)R(u)^\dagger W^\dagger.
\]
Therefore the already verified C2 form theorem gives the **actual**
transport
\[
 U_{\rm bulk}(u,v)D(G_\eta(v))=D(G_\eta(u)).                 \tag{G4}
\]
The strong clock derivative here is covariant:
\[
 \nabla_u\chi=W R(u)\partial_u[(W R(u))^\dagger\chi],\quad
 -i\nabla_u\chi=\Pi_g\chi=-G_\eta\chi.
\]
This definition is meaningful even when P_u,D,kappa Q separately have no
strong value. It closes the geometric momentum domain, not the distinct
original H_rel snapshot-domain problem. G4 is not automatically extended
to the lens-only or negative-g cases.

Normal states of finite G_eta+Lambda form expectation have legitimate
geometric energy means. Infinite expectation cannot match a finite target.
The common-core canonical identification is exact; we do not assert a
global kinematic Pi_g self-adjointness or a group-averaging equivalence.

## G3. Source-independent obstruction to the old geometric budget

Let m=<kappa> and a=1/(2g). Positivity of the source square and the
ORDERING_DOMAIN resource bound imply, when m²<=2a alpha_eta²/|d0|,
\[
 \boxed{-\langle\Pi_g\rangle=\langle G_\eta\rangle
 \ge\frac{a\alpha_\eta^2}{m^3}-\frac{|d_0|}{m}
                         +d_1m+d_3\langle\kappa^3\rangle.} \tag{G5}
\]
For positive d3 its last term may be dropped.
There is no assumption on the bare source marginal, its Q² budget,
source-geometry independence or a particular pointer. Mixed and entangled
normal states in the specified form class are included.

The reference momentum from the same old action is purely geometric:
Pi_g,ref=-3V0 A²h_i+P_u,ct. SOURCE_BUDGETS' actual derivative estimates give
\[
 |\Pi_{g,\mathrm{ref}}|<6.3\,10^{11}e^{-1158}<e^{-1130}<1.
\]
At K=65536 the corrected d0 satisfies |d0|<5e18, g<.05, d1,d3>0.
For every eta>=-1/4 and m<=1e-9, G5 gives
\[
 \langle G_\eta\rangle\ge5/m^3\ge5\,10^{27}>1.               \tag{G6}
\]
The old h_i<exp(-19980) is far inside the excluded budget region; its
stronger log bound is <G_eta> >exp(59000).

This rejects recovery of **both** the old expansion mean and the original
pure geometric momentum budget in this selected finite-K quantum branch.
It does not exclude matching a,h means alone, every quantization/boundary,
the negative-g branch, or the classical mean-SCE solution.
The model value 1e-9 is not a universal minimum expansion rate or an
experimental number. The principal quantum term carries hbar².

The shift/tail example in SHIFTED_STATE only matches P_u and kappa.
It does not evade G5; its true geometric momentum remains outside the
reference budget. A source-coordinate contribution must not be used as
a substitute for this geometric check.

## G4. A necessary third-moment frontier on the negative-g branch

For completeness the same action also yields a useful different gate.
Let g<0, b=1/(2|g|), T3=<kappa³>, and use the W-frame.
For lambda=H0+|d0|, define L3=<lambda³>. Source spectral resolution and
the critical-safe inverse-moment inequality give, for any eps,delta>0,
\[
 \langle\lambda/\kappa\rangle
 \le\epsilon q_\eta+\delta T_3+
 \frac{L_3}{12\sqrt{3\delta}\epsilon^{3/2}\alpha_\eta^3}.     \tag{G7}
\]
Take epsilon=b/2,delta=1. If the selected G expectation obeys G>=-E_Pi,
\[
 \boxed{(d_3+1)T_3+
 \frac{2|g|^{3/2}}{3\sqrt3\alpha_\eta^3}L_3
 \ge\frac{\alpha_\eta^2}{4|g|m^3}-d_1m-E_\Pi.}             \tag{G8}
\]
When d0<=0, its negative term may be dropped in the required upper bound
and lambda=H0 suffices. In original variables H0 is transported to
H_raw,conf=W H0 W†=sum[(p-kappa q)²+omega²q²]/2.
One must use that joint raw-source third moment, not the unchanged
marginal of the bulk H0 and not the Q² budget from SOURCE_BUDGETS.

At the actual K=131072, g<0, |g|<.136, d3+1<1.15,
d0<0 and the L3 coefficient is <.02.
For old m=h and E_Pi<=1, G8 implies
\[
 1.15 T_3+.02 L_3>1/m^3.
\]
If additionally T3<=2m³, then L3>40/m³ is necessary.
This is a finite-cutoff resource frontier, not an all-state rejection.
H_raw includes the finite-K vacuum energy; L3 is not a renormalized
continuum stress cumulant or a calibrated apparatus energy.

The negative-g inequality first holds on the common core and extends in
the combined positive budget norms. Its use as a spectral mean requires
the declared selected realization/graph-domain identification, as in
MEAN_RECOVERY; weak propagation alone does not supply arbitrary moments.
A fixed-snapshot realization can be obtained by the autonomous diagonal
special case of ALL_SIGN_EVOLUTION. No strong actual-clock G-domain
transport is claimed here.
