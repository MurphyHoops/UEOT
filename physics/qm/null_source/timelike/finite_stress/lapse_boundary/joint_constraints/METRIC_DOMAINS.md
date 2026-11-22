# JC4 — Continuum response, gauge null directions, and representation limits

## 1. A full-field first tangent on the actual prepared history

Take the inherited actual AQ homogeneous smooth source history and its
incoming vacuum, or the explicitly distinguished AP stationary ground.
Let \(a=(n,b,k,\delta r)\) denote a real, smooth, compact spacetime metric
and source variation, with every endpoint jet zero. At the common
constituent cutoff define
\[
 G_{a,K}=\int U_{0,K}(t)^\dagger\,\delta_aH_K(t)\,U_{0,K}(t)\,dt,
 \qquad v_{a,K}=(G_{a,K}-\langle G_{a,K}\rangle)\Omega_{\rm in}.
                                                                    \tag{1}
\]
The baseline mode equations and their incoming data agree exactly with
the full constituents. The full \(P_\tau\)-Hadamard Wick construction
therefore defines a two-particle vector \(v_a\), and
\[
 v_{a,K}=(P_K\otimes_{\rm sym}P_K)v_a\longrightarrow v_a .           \tag{2}
\]
This is an actual cutoff identity, not an extrapolation of a numerical
noise integral. For spacetime-smeared Wick polynomials and their
derivatives the relevant common domain is supplied by the microlocal
construction of Brunetti, Fredenhagen and Köhler,
[gr-qc/9510056](https://arxiv.org/abs/gr-qc/9510056), §5, especially
Proposition 5.3, Theorems 5.4/5.7, the derivative extension and
Corollary 5.9. The same wave-front argument applies to the finite
doublet and its smooth external matrix potential.

For a coherent code, the pair part still has (2), but its additional
one-particle part has the form \(P_KM_aP_Km\), not necessarily
\(P_KM_am\). Smooth Cauchy data and the continuity of the tested Wick
map give convergence of this extra term. The strict projection identity
must not be extended to that term without this argument.

Using the inherited baseline implementer identification, the actual
finite-cutoff density derivatives converge in trace norm:
\[
 \delta_a\varrho_K=-iU_{0,K}
 \bigl(|v_{a,K}\rangle\langle\Omega|-
       |\Omega\rangle\langle v_{a,K}|\bigr)U_{0,K}^\dagger
 \ \longrightarrow\ \delta_a\varrho,\qquad
 \|\delta_a\varrho\|_1\leq2\|v_a\| .                               \tag{3}
\]
Likewise the connected two-branch Gram matrix
\[
 N_{ab}=\operatorname{Re}\langle v_a,v_b\rangle
\]
exists and is positive semidefinite. Centering removes a scalar only
from this tangent/noise statement. The removed mean and the local
counterterm remain part of the absolute CTP phase and mean source.
Raw mixed kernels also contain the mean-times-mean term.

Equation (3) proves a limit of the actual cutoff derivatives. It does
not, for arbitrary finite-amplitude metric histories, prove an exchange
of differentiation and the full cutoff limit, convergence of the
unadjusted implementer phase, or the full CTP Hessian.

## 2. The first-order gauge test is exact before the limit

Let \(\xi=(\xi^0,\xi^i)\) be smooth and compact in time. On the round
baseline the active diffeomorphism variation is
\[
 n=\dot\xi^0,\quad b_i=\dot\xi_i-\nabla_i\xi^0,\quad
 k_{ij}=2\nabla_{(i}\xi_{j)},\quad
 \delta r=\xi^0\dot r,\quad \delta R={\cal L}_\xi6=0 .
\]
The source variation is indispensable during the actual ramp.
At finite cutoff use the Weyl quadratic
\[
 F_{\xi,K}=P_K\left[\int \xi^0{\cal H}_{\rm can}
       +\xi^i\sum_A\pi_A\nabla_i\Phi_A\,dV\right]P_K ,
\]
where
\[
 {\cal H}_{\rm can}=\tfrac12\sum_A
  (\pi_A^2+|\nabla\Phi_A|^2+\Phi_A^2)+r\phi\psi .
\]
The canonical generator is not obtained by silently replacing this
density with the improved sharp stress density.

The local canonical energy equation
\(\partial_t{\cal H}_{\rm can}=
 \nabla^i\sum_A\pi_A\nabla_i\Phi_A+\dot r\,\phi\psi\)
and spatial integration by parts give
\[
 \delta_\xi H_K=\partial_tF_{\xi,K}+i[H_{0,K},F_{\xi,K}] .          \tag{4}
\]
All \(n,k,b,\delta r\) coefficients reproduce METRIC_RESPONSE.md.
Projection is legitimate at this order because the homogeneous
unperturbed generator commutes with \(P_K\). Compact endpoint data make
the integrated centered generator exactly zero at every \(K\).
Thus the gauge direction is a true null of (2) and the connected Gram.

No isolated continuum sharp-time \(F_\xi\) is assumed to act on the
vacuum. The cancellation takes place at finite \(K\), followed by the
zero-vector limit. Nor does (4) prove all-orders cutoff covariance or
the scalar counterterm Ward matching.

## 3. Retarded contacts remain a separate gate

For causally time-separated compact insertions the corresponding
commutator response is defined on the same Wick domain. For overlapping
supports, multiplication of a singular stress product by a step
function requires the appropriate local extension and contact terms.
Hollands and Wald,
[gr-qc/0404074](https://arxiv.org/abs/gr-qc/0404074), §4.3 condition T11b,
§4.4 external-potential variation and Theorem 6.1, provide the
perturbative-agreement framework in dimension greater than two.
They do not identify our canonical spectral-cutoff phase and contact
terms automatically. That matching remains required.

## 4. A static mean family is not a differentiable bare Fock family

Compare radii using the **fixed physical** harmonic coordinate
\(\phi_k\) and density momentum \(p_k\), with lapse one. For
\(\mu=\sigma r\),
\[
 H_{\mu k}(a)=\tfrac12[a^{-3}p_k^2+
                  (ak^2+a^3\mu)\phi_k^2].
\]
Its ground-state width is
\(Z_{a,k}=a^2\sqrt{k^2+a^2\mu}\). Relative to radius one the squeeze is
\[
 \theta_{a,k}=\tfrac12\log(Z_{a,k}/Z_{1,k})
 =\log a+\tfrac14\log\frac{k^2+a^2\mu}{k^2+\mu}
 \longrightarrow\log a .
\]
Therefore, for \(a\ne1\),
\[
 K^{-3}\sum_{\sigma,k\leq K}k^2|\beta_{a,\sigma k}|^2
 \longrightarrow \tfrac23\sinh^2(\log a)>0 .                     \tag{5}
\]
The squared vacuum overlap (fidelity, not amplitude) satisfies
\[
 K^{-3}\log|\langle\Omega_1,\Omega_a\rangle_K|^2
 \longrightarrow-\tfrac23\log\cosh(\log a)<0 .
\]
At \(a=1\) the squared norm of the phase-fixed vacuum tangent is
\[
 \tfrac12\sum_{\sigma,k\leq K}k^2
 \left[1+\frac{\sigma r}{2(k^2+\sigma r)}\right]^2
 \sim K^3/3 .                                                    \tag{6}
\]
Thus this fixed bare canonical representation does not support a normal
differentiable vacuum family. The Hilbert–Schmidt implementability
criterion is standard; see §2 of Torre and Varadarajan,
[hep-th/9811222](https://arxiv.org/abs/hep-th/9811222).
Their separate flat-torus functional-evolution theorem is not invoked
as a theorem about this round \(S^3\) model.

The conformal identification \(\widetilde q=a\phi,\ \widetilde p=p/a\)
removes the constant high-frequency squeeze. That is a changed
canonical identification, and its uniform infinite squeeze is not
implemented as a unitary in the original bare representation.
A covariant mean can nevertheless be differentiable, as in
GROUND_DATUM.md; the two assertions concern different objects.

For a smooth **homogeneous** conformal metric history
\(g=a(\eta)^2(-d\eta^2+\gamma)\), with \(a=1,a'=0\) at both ends,
the actual cutoff transformation \(q=a\Phi\) is exact and commutes with
\(P_K\). It gives the fixed-ESU source \(r_{\rm eff}=a^2r\) and the
endpoint term \(-[hQ/2]\). The smooth-potential endpoint construction
can therefore be used for this subfamily. For spatially varying
conformal factors \(P_K\) does not commute with the rescaling, so this
argument does not establish the same actual-cutoff result.
