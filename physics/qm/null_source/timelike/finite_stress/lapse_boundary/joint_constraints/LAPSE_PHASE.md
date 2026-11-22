# JC15 — The complete finite phase on the restricted lapse history

## Scope and datum

Keep the unit S^3 spatial metric, zero shift, constant paired mass squares +r,-r with r=1/5, the same AP incoming state, and \(N=1+f(t)Z(x)\). Here |f|<.05 and f is smooth with compact time support. The canonical operator and common domain are those of LAPSE_HISTORY. The covariant datum is exactly GROUND_DATUM: local zeta subtraction, the stated finite \(\alpha\int\sqrt{-g}R^2\), \(\alpha=1/(4320V_0)=1/(8640\pi^2)\), the already fixed source-square term, and no additional finite curvature terms.

This entry closes the scalar phase on this family. It does not construct a functional on arbitrary metrics or permit differentiating this one-dimensional answer in omitted spatial-metric directions.

## 1. The massless normalization, including the base anomaly

Write \(q=fZ/(1+fZ)\). With the Lorentzian conventions of METRIC_RESPONSE,

\[
 R=6(1+q),\quad R_{nn}=-3q,\quad R_{ij}=(2+q)\gamma_{ij}.
\]

Define
\[
 H^{(1)}_{\mu\nu}=2g_{\mu\nu}\Box R-2\nabla_\mu\nabla_\nu R
 -\tfrac12g_{\mu\nu}R^2+2RR_{\mu\nu},
\]
\[
 H^{(3)}_{\mu\nu}=R_\mu{}^\rho R_{\rho\nu}
 -\tfrac23RR_{\mu\nu}-\tfrac12g_{\mu\nu}R_{\rho\sigma}R^{\rho\sigma}
 +\tfrac14g_{\mu\nu}R^2 .
\]

Direct contraction gives
\[
 H^{(1)}_{nn}=18(1-q^2)-12\Delta_\gamma q,\qquad H^{(3)}_{nn}=-3.
\]

For two massless conformal scalars the local-zeta conformal-vacuum stress is
\(T_\zeta=\alpha H^{(1)}-6\alpha H^{(3)}\).
This is calibrated by its trace
\(\Box R/(1440\pi^2)-E_4/(2880\pi^2)\) and by the ESU energy density
\(1/(120V_0)\). These checks fix both the factor of two and the Lorentzian sign. The Brown--Cassidy relation and its tensor conventions may be checked in Barvinsky--Wachowski, PRD 108, 045014 (2023), equations (4.17), (4.32), (4.34), (5.21), https://doi.org/10.1103/PhysRevD.108.045014 . We use that result only for this conformal-vacuum normalization.

The existing finite R^2 datum contributes \(-2\alpha H^{(1)}\). Thus the total stress for this calculation is
\[
 T_{\rm cov}=-\alpha H^{(1)}-6\alpha H^{(3)}.
\]
The incoming massless AP vacuum is the ESU conformal vacuum. At r=0 the canonical dipole generator has no pair part; its evolution leaves that vacuum invariant. Conformal covariance of the hyperbolic equation and uniqueness with the incoming Cauchy data identify the actual evolved state with the conformal vacuum on the present conformally flat metric. An instantaneous vacuum reset is not used.

Let
\[
 J(f)=\int_{S^3}{dV\over1+fZ}={2V_0\over1+\sqrt{1-f^2}}.
\]
Using \(\Delta Z=-3Z\), integration by parts yields
\[
 \int ZT_{nn}\,dV=18\alpha\int{Z\over(1+fZ)^2}\,dV
 =-18\alpha J'(f).
\]
For example \(q^2-2q=(1+fZ)^{-2}-1\), which displays the cancellation of the other terms.

## 2. Why the same dipole correction applies to the paired massive theory

This step compares actual operator subtractions; vanishing of integrated ultraviolet poles alone would not prove it.

1. The slices have K_ij=0, the same induced metric gamma, and G_nn=3. Write the complete improved energy bilocal in Cauchy variables with the momentum equal to the unit-normal derivative before introducing a regulator. Its quadratic form on each slice is
\[
 T_{nn}^{\rm quad}=\tfrac12[\pi^2+|\nabla\Phi|^2+(1+\mu)\Phi^2]
                         -\tfrac16\Delta_\gamma(\Phi^2),
\]
for each constant mass square mu. It is independent of the lapse. Apply the same SO(4)-invariant spatial heat regulator \(e^{-\epsilon(-\Delta+1)}\) to both Cauchy variables. No regulator is commuted through N. The dipole operator converges on D(H_0) to the canonical A of LAPSE_HISTORY; its expectation in the static AP vacuum is zero at every regulator. The ESU subtraction is spatially constant and also has zero Z projection.

For the conserving point-splitting prescription and its local equation-of-motion
correction, see Moretti, arXiv:gr-qc/0109048, section 2.2 equation (7),
section 2.3 equations (9)--(11), Lemma 2.1, and Appendix A equations
(55)--(62), https://arxiv.org/abs/gr-qc/0109048 . The full bidifferential
operator, including that correction, is used before coincidence.

2. Compare the actual metric Hadamard subtraction with the ESU subtraction using this same point split and regulator. Spatial geodesics in a totally geodesic slice are spacetime geodesics, so the equal-time world function is the same sigma_gamma. The unit-normal inner product on the diagonal is also the same. The scalar mass commutes with the kinetic operator, and the heat coefficients satisfy the exact recursion
\[
 a_j^\mu=\sum_{\ell=0}^j{(-\mu)^\ell\over\ell!}a_{j-\ell}^{0}.
\]
This identity controls the mass-dependent singular coefficients, not just their engineering dimensions.

3. Summing mu=+r and mu=-r cancels all odd powers. For an energy bilocal with at most two derivatives, the only even mass terms that survive coincidence are the universal r^2 U sigma log(sigma) coefficient in the Hadamard series and the r^2 log(sigma) term obtained by the explicit mass factor multiplying the lower coefficient. Their leading U on the diagonal is one. Because sigma_gamma and the unit-normal normalization agree, the difference between the actual and reference expressions has at least the additional O(sigma) factor. After two split derivatives it is O(sigma log sigma), or vanishes by coincidence in the explicit-mass term. Higher mass powers vanish at coincidence. Thus the paired actual-minus-reference energy subtraction has no r-dependent dipole correction.

4. The conserving Moretti local term and the already fixed source-square finite term have, in this paired difference, only a spatially constant r^2 part in this projection. It is killed by integral Z=0. The common geometric term remains exactly the massless term in section 1. First take the paired actual-minus-reference subtraction, then its common heat-regulator limit.

Consequently, on the common domain,
\[
 A_{\rm cov}(f)=A_{\rm can}-18\alpha J'(f)\mathbf1 .
\]
This argument is specific to constant paired masses, fixed totally geodesic spatial slices, and the dipole projection. It does not assert that the full massive stress is mass-independent. State-dependent massive polarization remains in A_can and in its actual evolution.

## 3. The actual phase and its contact

Normalize the extra Hamiltonian scalar to zero at f=0. The preceding derivative identity integrates to
\[
 c_{\rm geom}(f)=-18\alpha[J(f)-V_0]
 =-{1\over240}{1-\sqrt{1-f^2}\over1+\sqrt{1-f^2}},
\]
\[
 S_{\rm geom}[f]=-\int c_{\rm geom}(f)\,dt,\qquad
 U_{\rm cov}[f]=e^{iS_{\rm geom}[f]}U_{\rm can}[f].
\]

For two actual branches and a fixed normal initial density,
\[
 Z[f_+,f_-]=e^{iS_{\rm geom}[f_+]-iS_{\rm geom}[f_-]}
 \operatorname{Tr}(U_{{\rm can},+}\rho_{\rm in}U_{{\rm can},-}^\dagger).
\]
All finite mode cutoffs receive this same restricted, analytically determined finite correction. Strong convergence of the canonical unitaries and their adjoints therefore gives the actual phased CTP limit. This statement does not equate the uncorrected canonical phase with the covariant one.

The Hamiltonian contact is
\[
 c_{\rm geom}''(0)\delta(t-s)=-{\delta(t-s)\over480}.
\]
LAPSE_CURVATURE isolated the explicit finite R^2 contribution, whose contact is -delta/240. The base-zeta anomaly supplies the opposite half. Keeping only the explicit finite term would double the answer. The scalar correction changes the mean response and the contact, but not centered matter noise. It must be retained on each CTP branch before variation.

For f=epsilon b_delta from LAPSE_HISTORY, int b_delta=1 and ||b_delta||infinity<500 give
\[
 0\le S_{\rm geom}<.53\epsilon^2,\qquad
 S_{\rm geom}<5.3\,10^{-17}\quad(\epsilon=10^{-8}).
\]
Both endpoints have f=0. The integral of dot c_geom is zero, so this correction does not alter the net work or the previously certified terminal dipole signal. That particular metric history still fails the mean Einstein scalar constraint.

## 4. One graph convergence and its exact boundary

For the actual finite-cutoff Hamiltonians h_K=H_0+fA_K, uniform relative bounds give a common D(H_0) domain. Choose a fixed nonzero resolvent parameter i lambda. Set
\(Y_K=(h_K+i\lambda)U_K\Omega\).
Differentiation gives
\[
 \dot Y_K=(-ih_K+\dot h_K(h_K+i\lambda)^{-1})Y_K.
\]
The resolvents converge strongly into the H_0 graph by the uniform relative bound and resolvent identity. The second term is uniformly bounded and strongly convergent. The bounded Volterra equation, with the already established strong propagators, therefore gives strong Y_K convergence; applying the resolvent gives convergence of U_K Omega in one H_0 graph. In particular A_K U_K Omega converges, so the actual sharp dipole second moment has the corresponding cutoff limit. This is not an all-order graph theorem for metric histories.
Physical cutoff graphs are the same diagonal reference/recovery graphs
specified in LAPSE_HISTORY; an untransported finite-K state is not
silently put into the final fixed bare massive representation.

The argument is uniform on a sufficiently small smooth-profile parameter
ball. For t>=s the actual inserted kernel is
\[
 \langle A_K\psi_K(t),U_K(t,s)A_K\psi_K(s)\rangle .
\]
Its strong-vector factors converge and are uniformly bounded. Dominated
integration therefore gives the actual time-ordered and two-branch
second-order AA kernels, including the finite equal-time dipole variance.
The explicit first and second derivatives of c_geom supply their local
mean/contact terms. This proves a restricted lapse Hessian, not arbitrary
metric tensor components or all higher functional derivatives.

## Remaining gate

The restricted phase, its contact and the same-state mixed-branch kernel are now fixed. The complete metric functional, its other lapse/shift/spatial columns, renormalized general tensor Hessian, an autonomous preparation source, and a joint Einstein solution remain open.
