# The original CTP constraint: the spatial singlet and boundary data

This entry returns to the original two free minimal massless fields and the
frozen AE mean prescription. It does not use the dust/lattice Hamiltonian.
It proves a conditional obstruction and a necessary boundary-data contract,
not a constructed full tensor CTP functional or a quantum-gravity theory.

## 1. What the frozen homogeneous result actually says

Write the complete covariant mean residual as
F_ab[g,rho]=G_ab[g]/2-<T_ab[g]>_rho, with the fixed local terms assigned
exactly as in the original AE prescription. Let
L_rho h = delta(F_ab n^a n^b)
be its linear density row around the on-shell static background
g0=A^2(-d eta^2+d Omega_3^2).
The normal here is the background unit normal. Variations of the normal
or of the integration measure multiplying F[g0]=0 do not alter this
first-order definition.

The frozen total_source/CONSTRAINTS.md proves, within its fixed incoming
state/occupation transport, that the matter density variation is
delta rho_geom=-3u/A^2 and the gravitational density side has the same
variation. Thus L_rho h_u=0 for its allowed homogeneous conformal
tangent h_u=2u g0. The matter density variation itself is NOT zero.
Both static Einstein equations and the full AE dynamic logarithm are
used. We read that proof and its frozen certificate; we do not rerun it.

## 2. The actual state has invariant W2

For each full real harmonic multiplet on S3 put
Pi_k(x,x')=sum_m Y_km(x)Y_km(x').
The frozen preparation has the same occupation n in every k=2
oscillator, static vacuum in all other nonzero shells, and spatially
constant zero modes. Therefore, writing omega_k=sqrt(k^2-1),
\[
 W_2^{ij}(\eta,x;\eta',x')
 =W_z^{ij}(\eta,\eta')/V_0+
 {\delta^{ij}\over A^2}\sum_{k\ge2}
 { (1+n_k)e^{-i\omega_k(\eta-\eta')}
       +n_ke^{i\omega_k(\eta-\eta')}\over2\omega_k}
 \Pi_k(x,x'),\qquad n_k=n\,1_{k=2}.
\tag{55}
\]
The harmonic projectors are invariant under simultaneous SO(4) rotations.
Arbitrary species correlations in W_z do not change spatial invariance.

The two NOON density operators in total_source/COHERENCE.md preserve
this whole W2, not just a homogeneous mean stress. Their full-shell
pair vectors are themselves spatial singlets. Their non-Gaussian
four-point data and stress noise need not be inferred from Wick's theorem.

For smeared free linear fields A,B,C,D the exact identity
\[
 [AB,CD]=A[B,C]D+AC[B,D]+[A,C]DB+C[A,D]B
\tag{56}
\]
reduces the quadratic stress commutator to two-point data because the
field commutators are central. Equivalently, for S(A,B)={A,B}/2,
\[
 [S(A,B),S(C,D)]=[A,C]S(B,D)+[A,D]S(B,C)
              +[B,C]S(A,D)+[B,D]S(A,C).
\]
Thus the free retarded mean-response commutator uses W2 and the CCR,
without a Gaussian assumption on W4. Renormalized coincident products,
local contact terms, metric variations of the stress operator and
boundary terms still have to be defined in one covariant prescription.
A Gaussian log-determinant is not asserted to be the exact CTP functional
of these non-Gaussian initial states.

The following theorem requires a covariant extension of the frozen
mean prescription; (55)-(56) explain its compatibility with the actual
free-field state, but do not by themselves construct that extension.

## 3. What nonzero spatial harmonics can and cannot do at linear order

Let D be the declared space of allowed metric histories and transported
state data. Assume:

1. SO(4) acts by tensor pullback on D, and Haar averaging P_met preserves
   D. The response is continuous on this space, or closed with a
   group-invariant graph domain on which the averaging is legitimate.
2. The FULL mean-response row, including local contacts and initial
   terms, is equivariant: L_rho U_R=U_R L_rho.
3. To conclude a zero row for every h in D, additionally require that
   P_met h is a sum of an allowed frozen incoming conformal tangent and
   an allowed anchored homogeneous time diffeomorphism. State transport
   and boundary terms must satisfy the corresponding diffeomorphism Ward
   identity. This third assumption is unnecessary for the weaker result
   about a pure nonzero-harmonic perturbation.

Let P_rho be spatial averaging of the output scalar. Haar integration
of assumption 2 gives
\[
                 P_\rho L_\rho=L_\rho P_{\rm met}.
\tag{57}
\]
In particular P_met h_perp=0 implies P_rho L_rho h_perp=0.
Adding such linear inhomogeneous metric perturbations to an already
specified homogeneous history cannot provide a missing singlet
constraint component. This conclusion does not require a mode cutoff.

For the stronger statement, S3 isotropy has no invariant spatial
one-form and has only gamma_ij as an invariant symmetric spatial tensor.
Hence a tensor Haar average has
h00=-2A^2 nu(eta), h0i=0, hij=2A^2 u(eta) gamma_ij.
Its difference from h_u=2u g0 is the homogeneous time gauge generated
by f(eta) partial_eta, with f'=nu-u, when that anchored f is allowed.
On shell the covariant Ward identity gives
L_rho Lie_(f partial_eta) g0=Lie_(f partial_eta) F[g0]=0.
Together with the frozen homogeneous result this proves
\[
                    P_\rho L_\rho h=0\quad(h\in D).
\tag{58}
\]

The domain and Ward conditions are essential. The map
L0(nu,u)=nu-u is SO(4)-equivariant and vanishes on the conformal
nu=u direction, but not on an independent lapse direction. It violates
the required time-gauge Ward condition. Endpoint conditions that exclude
f, independent boundary matter data, or a changed transport cannot be
silently included in (58). A clock or controller held fixed independently
can make relative lapse a physical variable; that changes this metric-only
transport contract. A mere isotropic value of <T> would also not
have established the W2/response premise.

Equations (57)-(58) are linear statements. Products of nonzero harmonics
can have a singlet at second order; nonlinear compensation is not excluded.

## 4. A finite positive-time-window absolute residual

Take any nonempty finite open time interval I and real
f in C_c^infinity(I), with integral f=1. For a scalar source define
\[
 \Lambda_f X=\int f(\eta)\,{1\over V_0}
                    \int_{S^3}X(\eta,\Omega)\,d\Omega\,d\eta .
\]
This is a smooth spacetime test on the compact spatial section.
On the static background the spatially averaged density is the
conserved total energy divided by V0 A^3. Its centered fluctuation is
time independent; its background normal time derivatives vanish.
The function f is normalized using d eta, not proper time, in this display.
Consequently its symmetrized smeared variance is
\[
 N_{00}={M_2^2\over4A^{12}}\operatorname{Var}(S_0)
              +{6n(n+1)\over\pi^4A^8}>0.
\tag{59}
\]
Here S0 is the original dimensionless radial momentum variable.
The vacuum and constant counterterms have no global energy variance.
The zero/high product state and either NOON sign have the same (59).
No actual apparatus energy has yet been added to this baseline.
A real localized carrier/controller can also change the mean response and
spatial symmetry; the old A, L and N00 cannot then be reused automatically.

The frozen certificate encloses
N00 in [5.11712000935814e-22,5.117168428991371e-22].
The certificate also divides its RMS by the SAME unfiltered static mean
rho0=3/(2A^2). That dimensionless ratio is a density-fluctuation ratio,
not a metric error or an instrument sensitivity.
These are physical density squared in the original model units, not a
difference of noise kernels. A conserved global observable and a smooth
time test are being used; no pointwise stress-noise value is assumed.

Consider a proposed linear stochastic extension L_rho h=xi_rho with
this same absolute density covariance. Under all assumptions of (58),
\[
 \Lambda_f(L_\rho h-\xi_\rho)=-\Lambda_f\xi_\rho,\qquad
 \operatorname{Var}\Lambda_f(L_\rho h-\xi_\rho)=N_{00}.
\tag{60}
\]
For centered noise its RMS is sqrt(N00)>0 on every such finite window.
Arbitrary correlations between h and xi do not remove an identically
zero response row. Gaussianity or independent metric noise is not used.

This excludes that specified linear extension with only the inherited
state/geometry directions, even after arbitrary allowed nonzero spatial
harmonics are added. It does not invalidate the deterministic mean
solution, which contains no xi term. It also does not supply a controlled
Einstein-Langevin approximation for exactly two fields.

## 5. The finite-slice boundary column is a real change of contract

Homogeneous covariant conservation on the static background gives
\[
 (\delta\rho)'+3(\rho_0+p_0)u'=0,\qquad
 \delta\rho=-3u/A^2+C_\partial .
\tag{61}
\]
The constant C_partial is fixed by the state/boundary data; the frozen
incoming contract sets it to zero. A finite initial slice with an
independent density or occupation variation may supply it. Then the
linear mean density residual is -C_partial. Equation (61) identifies a
missing physical direction; it does not realize that direction by a
normal joint quantum state or permit an arbitrary change in an actual
measurement record.

Use the explicit sign convention
\[
 L_\rho h=\xi_\rho+B Y,\qquad
 R_\rho=L_\rho h-\xi_\rho-BY,\qquad
 Z=\Lambda_f BY,\quad \xi_0=\Lambda_f\xi_\rho.
\]
Here BY is an additional density-source column, such as C_partial,
not a relabeling of the inherited noise. Under (58),
Lambda_f R_rho=-(Z+xi0).
For classical/central finite-second-moment variables, exact cancellation
requires centered means and
\[
 \operatorname{Var}Z=N_{00},\qquad
 \operatorname{Cov}(Z,\xi_0)=-N_{00}.
\tag{62}
\]
In matrix notation, B0 C_Y B0*=N00 and B0 K0=-N00, where
B0=Lambda_f B, C_Y=Cov Y, K0=Cov(Y,xi0).
All other constraint rows and their cross covariances remain to be solved.

More generally, the reverse triangle inequality in the space of centered
square-integrable variables gives
\[
 \sigma_R\ge|\sigma_Z-\sqrt{N_{00}}|,\qquad
 \operatorname{Var}Z\le V
 \ \Longrightarrow\
 \sigma_R\ge(\sqrt{N_{00}}-\sqrt V)_+ .
\tag{63}
\]
Thus RMS tolerance epsilon<sqrt(N00) requires
Var Z >= (sqrt(N00)-epsilon)^2 and a sufficiently negative cross block.
The conditions refer to the absolute baseline, not merely Delta N.

The rank-one classical block N00 [[1,-1],[-1,1]] is positive and
saturates (62), but that algebraic fact is not a normal quantum state,
a CP preparation, a local instrument, or an all-order influence law.
The same original fluctuation cannot be counted again under the name BY
and then subtracted; the actual joint action and state must supply a new
column with its own physical meaning.
For quantum carriers, the full commutators, uncertainty relations,
domain conditions and actual source operators must also be respected;
total_source/INITIAL_CORRELATIONS.md already exhibits a pressure
quadrature obstruction to an analogous naive classical cancellation.

A more direct test applies if a proposed quantum boundary realization
keeps the complete original matter marginal. On its de-sheared canonical
zero-mode frame define D0=sum_j {Q_j,P_j}/2. If the additional boundary
operator Z commutes with this matter dilation, then, on the common
finite-moment form domain,
\[
 [Z+\delta\bar\rho,D_0]
       =-i\,{P_1^2+P_2^2\over V_0 A^6}.
\]
The high-shell energy commutes with D0. Robertson therefore gives
\[
 \operatorname{Var}(Z+\delta\bar\rho)
 \ge {\langle P_1^2+P_2^2\rangle^2
          \over4V_0^2A^{12}\operatorname{Var}D_0}>0.
\tag{64}
\]
The original marginal has finite Var D0 and positive <P^2>. Exact
classical anticorrelation cannot then be implemented by such a finite
normal quantum carrier while preserving that marginal. This is a
necessary quantum check, not an identification of the stochastic
auxiliary with a quantum observable. A changed matter marginal or a
new boundary operator that does not commute with D0 is outside this
particular bound and requires its own construction and constraint test.

## 6. The next acceptance test

The next construction must explicitly release the old zero boundary
energy constant or another stated assumption. It must then provide:

- One normal geometry-matter-device boundary state, its actual density
  and momentum constraints, and the full initial blocks C_Y, K and N.
- One covariant mean/retarded/noise prescription, including boundary
  Ward terms and the original AE contact terms. In particular a
  non-Gaussian initial state requires its actual boundary functional.
- A causal positive-time evolution with finite smeared absolute
  baseline covariance and an error bound for the stated approximation.
  A leading large-N correspondence is not an exact two-field theorem.
- A common preparation past and an actual instrument response before
  the existing NOON pressure difference is promoted to a calibrated
  gravitational record.

The exact first-order conservation and Haar arguments close the question
of adding only nonzero spatial harmonics within the stated contract.
Construction and quantum realizability of the new boundary state remain
OPEN. The full inhomogeneous CTP Hessian has not been computed here.

Primary context: Anderson, Molina-Paris and Mottola, gr-qc/0209075,
equations (3.4)-(3.9), for retarded response plus local contact terms;
Hollands and Wald, gr-qc/0404074, for covariant metric variation and Ward
normalization; Hu, Roura and Verdaguer, gr-qc/0402029, Appendix D, for
finite-initial-time noise and initial correlations. These papers do not
prove this UEOT-specific theorem or construct its missing boundary state.
