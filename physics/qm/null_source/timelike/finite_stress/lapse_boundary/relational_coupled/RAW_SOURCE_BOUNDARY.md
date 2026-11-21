# Source energy and all finite-mode raw stress covariances at the clock boundary

G_ZERO_BOUNDARY shows that the joint geometry has no normal boundary
limit. BOUNDARY_MATCHING nevertheless gives a raw-phi source marginal
limit. This entry supplies the extra moment control needed to pass from
bounded source observables to raw finite-K stress means and same-slice
covariances. It does not take a continuum or two-time feedback limit.

## R1. Uniform source-energy control for every fixed positive power

In the zero-dilation-removed frame of G_ZERO_BOUNDARY set
lambda0=1+Hosc+P0²/2 and S_p=lambda0^p, for any fixed p>=1.
Hdiag,tau strongly commutes with S_p. In the occupation basis the only
off-diagonal term is epsilon exp(tau)Dosc.
For neighboring occupations, delta|D_mn|<=lambda_max and
lambda_max/lambda_min<=5. The mean-value inequality therefore gives
\[
 { |[D_{\rm osc},S_p]_{mn}|\over
                \lambda_m^{p/2}\lambda_n^{p/2}}
 \le p\,5^{p/2},\qquad
 |i[D_{\rm osc},S_p]|\le C_p S_p,\quad C_p=2d p\,5^{p/2}.    \tag{R1}
\]
There are at most 2d neighbors per row/column. The bound includes the
continuous zero-mode momentum fibers and is finite for each K,p.

This is an operator-domain statement after regularization. First use
the occupation cutoff D_M from ALL_SIGN_EVOLUTION and
S_p,R=S_p/(1+S_p/R). Its matrix commutator has the same bound relative
to S_p,R: the additional denominators only reduce the normalized
matrix entries. S_p,R strongly commutes with the diagonal generator.
The weak energy identity and Gronwall give, uniformly in M,R,
\[
 e^{-C_p|e^\tau-e^{\tau_0}|}\langle S_p\rangle_{\tau_0}
 \le\langle S_p\rangle_\tau
 \le e^{C_p|e^\tau-e^{\tau_0}|}\langle S_p\rangle_{\tau_0}.   \tag{R2}
\]
Pass M to infinity by the already established strong propagator
convergence, then R to infinity by monotone convergence/Fatou.
The reverse bound uses the inverse propagator. Dense approximation
extends the evolution as a bounded strongly continuous family on
H_p=D(S_p^(1/2)), with a uniform bound as tau tends to minus infinity.
There is no additional geometry moment assumption in this source-only
bound, and no requirement that p>=3.

## R2. The scattering maps also converge in the source-energy norm

On the dense Hankel/finite-occupation/compact-zero-momentum packets,
the Cook residual is bounded in H_p by C_psi exp(tau)(1+tau²).
R2 makes the forward Cook operators uniformly bounded on H_p, so
they converge strongly there. The reverse H-space limit and Fatou
place its image in H_p. The H-space inverse identities, together with
W_tau-W=W_tau(I-Omega_tau W), then prove the reverse strong limit in
H_p and surjectivity on H_p. No claim of surjectivity on the complete
geometry comparison domain is needed.

For every normal initial density with finite S_p expectation, finite-rank
approximation in the S_p-weighted Hilbert--Schmidt norm yields
\[
 \|S_p^{1/2}[\rho_z(\tau)-Z(\tau-\tau_0)\rho_{\rm as}
                   Z(\tau-\tau_0)^\dagger]S_p^{1/2}\|_1\to0.        \tag{R3}
\]
The finite-u zero-mode dilation preserves H_p and tends strongly to
identity in that norm, so R3 transports to the W frame.
Because S_p acts only on source, partial trace gives the analogous
weighted source trace-norm limit sigma(u)->sigma_as.

For the original raw variables define the natural moving weight
S_raw,p(u)=T_a(u)^\dagger S_p T_a(u). Then
\[
 S_{\rm raw,p}(u)^{1/2}\rho_{\phi,\rm raw}(u)S_{\rm raw,p}(u)^{1/2}
 =T_a(u)^\dagger[S_p^{1/2}\sigma(u)S_p^{1/2}]T_a(u)
 \longrightarrow
 T_{a_c}^\dagger[S_p^{1/2}\sigma_{\rm as}S_p^{1/2}]T_{a_c}           \tag{R4}
\]
in trace norm. Only the strong continuity of T_a on H and trace-class
continuity are needed here. Thus the actual moving raw conformal
source-energy moments have finite limiting values when they were
finite initially. Arbitrary fixed unbounded raw observables have not
been smuggled into R4.

## R3. A common operator realization for finite-K raw stresses

After the same T_a identification, the original minimally coupled
massless raw source stress at any point of S3 is a real Weyl quadratic
in
R_i={P_0,j, p_osc,j, omega_j q_osc,j}.
Zero-mode Q does not occur: its time derivative is zero and its spatial
harmonic is constant. For example, in an orthonormal frame
T_nn=a^-4[p_raw(x)²+|grad q(x)|²]/2. The momentum and spatial stress
components have the analogous symmetrized derivative products.

Thus each component or spatially tested component has the form
\[
 T_\alpha(a)=c_{\alpha0}(a)+
       \sum_{ij}c_{\alpha ij}(a)(R_iR_j+R_jR_i)/2,\qquad
 \lambda_0=1+\tfrac12\sum_iR_i^2.                           \tag{R5}
\]
For fixed K and a in a compact positive interval the coefficients are
bounded and continuous, uniformly on compact S3. They need not be
bounded uniformly as K tends to infinity.

On zero-momentum compact smooth functions tensor finite occupation
vectors,
||R_i lambda0^-1/2||<=sqrt(2).
Creation and annihilation shift lambda0 by omega. The two ladder
pieces give ||lambda0^1/2 R_i lambda0^-1||<3 (the zero-mode momentum
bound is smaller). Hence
\[
 \|T_\alpha(a)\lambda_0^{-1}\|
 \le C_\alpha(a):=|c_{\alpha0}|+5\sum_{ij}|c_{\alpha ij}|,\qquad
 \|\lambda_0^{-1/2}T_\alpha(a)\lambda_0^{-1/2}\|
 \le|c_{\alpha0}|+2\sum_{ij}|c_{\alpha ij}|.                 \tag{R6}
\]
Both bounded operators vary continuously in a.

The real quadratics have a definite self-adjoint closure. One may use
the standard Nelson commutator criterion with comparison lambda0:
the displayed test space is a lambda0 operator core, T_alpha is
lambda0-bounded, and i[T_alpha,lambda0] is another quadratic of the
same type with form bound C'_alpha lambda0.
The exact standard theorem used is Ammari--Breteaux, Appendix B,
Theorem B.2. Occupation and zero-momentum spectral cutoffs extend the
quadratic commutator bound to D(lambda0^(3/2)), its required domain.
The cutoffs commute with lambda0 and converge in the necessary graph
norms; no formal-core substitution is used.
Equivalently, on each compact zero-momentum support, T_alpha raises
occupation by at most two and has norm <=C(n+1) on occupation <=n;
its iterates give a dense set of analytic vectors.
Neither method assumes self-adjointness from a sum of formal terms.
Graph approximation gives D(lambda0) subset D(T_alpha).
The bound T_alpha²<=C_alpha² lambda0² as positive forms and square-root
monotonicity imply |T_alpha|<=C_alpha lambda0.
Thus a finite first energy moment gives a genuine finite absolute
spectral first stress moment, not an undefined infinity minus infinity.

## R4. Mean and same-slice covariance limits

For p=1, R3--R6 give
Tr sigma(u)T_alpha(a(u)) -> Tr sigma_as T_alpha(a_c).
For p=2 use the bounded form extension
\[
 K_{\alpha\beta}(a)=
 (T_\alpha(a)\lambda_0^{-1})^\dagger
                         (T_\beta(a)\lambda_0^{-1}),\qquad
 \|K_{\alpha\beta}\|\le C_\alpha C_\beta .
\]
The legitimate symmetrized second moment is
Re Tr[(lambda0 sigma lambda0)K_alpha,beta].
It is defined by the inner products
Re <T_alpha psi_j,T_beta psi_j> of a density purification.
Finite second energy moment suffices. It is not a claim that every
such state belongs to the literal product domain D(T_alpha T_beta).

The weighted trace limit and continuity in a therefore give the
limits of all finite-K raw source means and all same-slice connected
symmetrized stress covariances. The mean products converge as well.
No independent-noise replacement has been made.

These are raw finite-cutoff source operators in the homogeneous
geometry sector. AE geometric subtraction terms, the K limit,
two-time tensor CTP response, general spatial gravitational constraints,
the old quiet-history recovery and a calibrated device are still
separate tasks. The absence of a joint normal geometric boundary state
is fully compatible with these finite source limits.
