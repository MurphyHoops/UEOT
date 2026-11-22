# A symmetry-preserving two-zero-mode Dirac sector and the old-source spectral gate

This continues MATTER_CLOCK with an explicitly narrower extension family.
It restores both original zero-mode translation symmetries and their O(2)
rotation symmetry, constructs new normal Dirac states, and maps directed
angular states into the positive scalar-clock sector. It does not claim
that the old complete thin source or old geometry has thereby been recovered.

## S1. Choose the extension before separating a scalar clock

Remove both massless zero modes from C_rest and put
Rbar0=-2a(C_geom+H_osc,phi)a on geometry plus nonzero source modes.
It has the same compact-u-patch, whole-real-kappa, eta=0 test domain as
MATTER_CLOCK. The same conjugation/reflection and endpoint-boundary
arguments give deficiency indices (infinity,infinity).
Choose a self-adjoint extension Rbar on H_gosc and then define
\[
 R_T=\overline R\otimes I-I\otimes P_2^2,\qquad
 K=P_1^2+P_2^2-\overline R,\qquad
 C={1\over2}a^{-1}K a^{-1}.                                \tag{S1}
\]
The differences use the tensor joint spectral domain, including possible
cancellations. Bounded invertibility of a on the chosen u patch gives
a self-adjoint C as in MATTER_CLOCK. This choice avoids an arbitrary
R_T extension that could break the original second zero-mode translation.

The operator and its resolvent strongly commute with both zero-mode
translations and O(2) rotations. In momentum polar coordinates,
K=r²-Rbar and a do not act on theta. In fact every unitary on L²(S1)
commutes strongly with C. Such additional nonlocal angular symmetries
are mathematical symmetries of this homogeneous-mode operator; they
are not automatically local apparatus operations.

These symmetry requirements still do not select the geometric boundary.
Even imposing conjugation invariance leaves infinitely many extensions:
if e_j is a basis of N_+, the linear maps
U_theta e_j=exp(i theta)J e_j have J-invariant extension domains for
every theta. The boundary datum and its spectrum must still be specified.


## S1a. The single-clock radicand has a complete absolutely continuous spectrum

This is a result for the symmetry-preserving extension family in S1,
not for every extension R_U allowed in MATTER_CLOCK.
Let nu_bar be a faithful finite maximal spectral measure of the selected
Rbar. In the joint spectral representation of Rbar and P2,
R_T acts by E=lambda-p2^2. For every Lebesgue-null set Z, the set
{p2:lambda-p2^2 in Z} has Lebesgue measure zero for every lambda:
split p2 into intervals bounded away from zero and use the inverse
change of variables there; the point p2=0 has zero measure.
Fubini proves that every spectral measure of R_T is absolutely continuous.

To determine the maximal measure class, take the faithful auxiliary
probability nu_bar(dlambda) pi^-1/2 exp(-p2^2) dp2. Its pushforward has density
\[
 w(E)=\pi^{-1/2}\int_{\lambda>E}
       {e^{-(\lambda-E)}\over\sqrt{\lambda-E}}\,d\nu_{\rm bar}(\lambda).
                                                               \tag{S1a}
\]
Tonelli and the Gamma(1/2) integral give integral w(E)dE=1, so w is finite
almost everywhere. The common-core phase argument of MATTER_CLOCK shows
Rbar is unbounded above for every selected extension. Therefore
nu_bar((E,infinity))>0 for every finite E and w(E)>0 wherever finite.
The Gaussian here constructs a faithful measure class; it does not
replace the physical P2 input by a Gaussian state.

Consequently R_T is purely absolutely continuous, its maximal spectral
measure is equivalent to Lebesgue measure, and its spectrum is all R.
Every nonempty open positive clock-energy band has a nonzero projection.
The normal-state spectral-law construction of S8 then realizes any
specified absolutely continuous probability law of P1^2 on the positive
half-line (and any such law supported in a chosen finite positive band).

This does not settle the old source's total radial law:
P1^2+P2^2=Rbar can still have singular or atomic spectrum even while R_T
is purely absolutely continuous. The distinct radial acceptance
condition S8 remains open.

## S2. Exact group-averaged angular factor without an assumed spectral density

Let nu be any spectral measure representation of the chosen Rbar,
including its possible multiplicity. Do not assume that nu is absolutely
continuous. Choose a bounded open positive interval J with nonzero
E_J=1_J(Rbar). On annular smooth Fourier tests with r² in J, use the
same bounded-congruence Abel proof as MATTER_CLOCK.

With the two-dimensional unitary Fourier convention
fhat(p)=(2pi)^-1 integral exp(-ip·phi)f(phi)d²phi, the normalization
(1/2) integral ds exp(-epsilon|s|)<f,exp(isC)g> gives
\[
 \eta_C(f,g)=2\pi\int d\nu(\lambda)\int d^2p\,
       \delta(p^2-\lambda)\,
       \langle\widehat{af}(p;\lambda),\widehat{ag}(p;\lambda)\rangle
\]
\[
 =\pi\int_J d\nu(\lambda)\int_{S^1}d\theta\,
       \langle\widehat{af}(\sqrt\lambda e_\theta;\lambda),
                         \widehat{ag}(\sqrt\lambda e_\theta;\lambda)\rangle.
                                                                  \tag{S2}
\]
The radial identity is r dr delta(r²-lambda)=1/2.
Thus the rigging map is
T_C^(2)f(lambda,theta)=sqrt(pi) fhat_a(sqrt(lambda)e_theta;lambda).
The completion is
\[
 H_{\rm phys}^{(2)}=E_J H_{\rm gosc}\ \widehat\otimes\ L^2(S^1,d\theta).
                                                                  \tag{S3}
\]
Density follows from annular radial tests, smooth angular tests and
E_J(a D0) dense in E_J H_gosc, first on compact subbands and then by
exhaustion. Atoms at the open endpoints are excluded explicitly.
The angular Householder map of ANGULAR_CLOCK_INPUT preserves these
smooth annular tests and intertwines the rigging. Gauge-orbit completion
is available as in MATTER_CLOCK.

In this physical space the original conserved momenta are
\[
 P_1=\sqrt{\overline R}\cos\theta,\qquad
 P_2=\sqrt{\overline R}\sin\theta,\qquad P_1^2+P_2^2=\overline R.
                                                                  \tag{S4}
\]
For any normal trace-one tau on E_J H_gosc and normalized angular g,
tau tensor |g><g| is an actual normal Dirac density.
This tau is a geometry/nonzero-mode physical density; it is not the
incoming radial/shell density called tau in the source-level construction.

The original-variable distributional solution map has the exact constant
\[
 (S\xi)(\phi_1,\phi_2)
 ={a\over2\sqrt\pi}\int_{S^1}
 e^{\,i\sqrt{\overline R}(\phi_1\cos\theta+\phi_2\sin\theta)}
                         \xi(\theta)\,d\theta.             \tag{S5}
\]
It is the distributional adjoint of T_C^(2).

## S3. A genuine directed normal state in the positive scalar-clock space

The full circle in S3 contains both signs of P1. Its positive group-
averaged norm is the direct sum of the two oriented sectors; the raw
Klein--Gordon current in phi1 has the opposite sign in the negative sector.

On the right half-circle set p2=sqrt(lambda)sin(theta), so
dp2=P1 dtheta. The exact physical unitary to the positive R_T sector is
\[
 ({\cal V}\xi)(\lambda,p_2)
   =(\lambda-p_2^2)^{-1/4}
       \xi\!\left(\lambda,\arcsin{p_2\over\sqrt\lambda}\right).
                                                                  \tag{S6}
\]
It preserves norm for any spectral type nu. Fourier transforming S5
in phi2 gives exactly the positive-clock solution
a exp(+i phi1 Omega)(2Omega)^-1/2 Vxi of MATTER_CLOCK.

If tau is supported on a closed positive subband [lambda0,lambda1]
and g is supported in |theta|<pi/4, then
P1²=lambda cos²theta lies between lambda0/2 and lambda1.
The resulting new normal Dirac density therefore maps into a bounded
positive R_T band with all clock weights boundedly invertible.
This is an explicit Dirac-to-Klein--Gordon bridge for these new states.

The full-circle Householder u0->g is a unitary on S3, but it is not a
unitary within a preselected single positive-P1 sector: its inverse sends
g back to u0, which has negative-P1 probability 1/2. A gate wholly inside
the positive sector requires different initial and final angular
vectors both supported there. The uniform full-circle state is normal
in S3; because it reaches cos(theta)=0, a flat single-clock slice norm
need not be finite. The directed output avoids that endpoint.

The source-level and physical-level angular transformations have the
same pure-factor trace-distance formula, but their non-angular factors
are different. Neither their common formula nor S6 identifies the
physical tau with the old complete source preparation.

## S4. A necessary and sufficient radial recovery criterion

The original two zero-mode Noether momenta are the same P_j in S4:
pi_j=a²D phi_j=P_j under the fixed Cauchy transport. The old target
radial probability measure is therefore fixed once, with
\[
 {d\mu_{\rm old}\over d\lambda}
 ={(1-p)w^2((\lambda/(2A^3)-e_0)/\sigma)
          +p\,w^2((\lambda/(2A^3)-e_2)/\sigma)
    \over2A^3\sigma}.                                     \tag{S7}
\]
All A,e_N,sigma,p are the frozen incoming constants. They are not
replaced by a(u) while a state evolves. S7 is only the radial marginal:
it does not include the original conditional correlations with N2.

Fix the actual Rbar extension. For a dense orthonormal basis e_j, choose
a maximal finite spectral measure
nu(Delta)=sum_(j>=1) 2^-j <e_j,E_Rbar(Delta)e_j>.
Then a specified probability law mu is realizable by a normal physical
density tau precisely when
\[
                         \boxed{\mu\ll\nu.}               \tag{S8}
\]
Necessity follows from spectral projections: nu(Delta)=0 iff
E_Rbar(Delta)=0. For sufficiency let w_mu=dmu/dnu and
psi_j=sqrt(w_mu)(Rbar)e_j. Tonelli gives
sum 2^-j||psi_j||²=1, so each psi_j is well defined and
tau=sum 2^-j|psi_j><psi_j| is positive trace class of trace one,
with spectral law mu. This explicit construction is mixed; no invalid
pure superposition of a general orthonormal basis is used.

There is also an exact approximation frontier. Decompose
mu=mu_ac+mu_s relative to nu and let q=mu_s(R).
Every normal physical radial law eta has
TV(mu,eta)>=q. If q<1, eta=mu_ac/(1-q) attains q; if q=1 every normal
physical law is at total-variation distance one. In particular a
purely singular nu cannot reproduce the absolutely continuous thin
law S7. Weak or coarse-bin approximation is not full-law convergence.

Positive spectrum being unbounded, or merely having some absolutely
continuous component, is insufficient. Its maximal spectral measure
must dominate the specific old measure on its support.
No spectral type of the selected Rbar has been calculated here, so
S8 is an exact acceptance gate, not a claim that it has passed.

There is a separate bare-matter normality condition. On the original
L2(R²_P) zero-mode Hilbert space, every normal P² law is absolutely
continuous relative to Lebesgue d lambda, by polar coordinates.
Thus a common radial record realizable by both a normal Dirac state and
a normal bare zero-mode state exists on a region precisely when the
selected Rbar has a nonzero absolutely continuous component there.
This weaker intersection still does not match a prescribed thin law.
If a physical Rbar state has an atomic radial law, its Dirac normality
does not turn it into a normal bare matter energy eigenstate and does
not contradict the older bare-state zero-variance exclusion.
An arbitrary absolutely continuous law also need not have the smooth
Q moments required of the current thin source.


## S4a. An exact resolvent gate for the old continuous radial law

The next object can be specified without guessing the spectral type.
Fix the actual self-adjoint Rbar and a faithful trace-one density
tau_* = sum 2^-j |e_j><e_j|. Let nu_*(B)=Tr(tau_* E_Rbar(B)) and
\[
 p_\epsilon(\lambda)={1\over\pi}\operatorname{Im}
     \operatorname{Tr}\big[\tau_*(\overline R-\lambda-i\epsilon)^{-1}\big]
   =\int{\epsilon\over\pi[(x-\lambda)^2+\epsilon^2]}\,d\nu_*(x).
                                                               \tag{S9}
\]
The Poisson/Herglotz boundary theorem gives, for Lebesgue-almost every
lambda, p(lambda)=lim_(epsilon down 0)p_epsilon(lambda)
=d(nu_*)_ac/dlambda. See Gesztesy--Tsekanovskii, Theorem 2.2(v), Eq.(2.17),
https://arxiv.org/pdf/funct-an/9712004. For the old smooth density
mu_old=f_old dlambda, S8 is exactly
\[
 f_{\rm old}=0\quad\hbox{a.e. on }\{p=0\},\qquad
 q_{\rm TV,min}=\int_{\{p=0\}} f_{\rm old}(\lambda)\,d\lambda .
                                                               \tag{S10}
\]
The singular part of nu_* is supported on a Lebesgue-null set and cannot
carry a nonzero part of this absolutely continuous target. On {p>0},
f_old/p is the Radon--Nikodym density, which proves both assertions
using S8 and its total-variation frontier.

Every finite epsilon gives p_epsilon>0 everywhere. This is not the
acceptance test: a single point mass at lambda0 gives that positivity
for every epsilon while its limiting p vanishes almost everywhere.
A finite mesh or finite broadening by itself cannot certify S10.

One concrete sufficient construction is available if an actual vector
psi has a boundary density p_psi>0 mu_old-almost everywhere. Put
F(lambda)=sqrt(f_old(lambda)/p_psi(lambda)) on that support and zero
elsewhere. Then
\[
                  \xi=F(\overline R)P_{\rm ac}\psi
\]
is well defined with norm squared integral f_old=1 and has the exact
radial law mu_old. The potentially unbounded functional calculus is
legitimate on this vector by that same norm integral. This does not
assume an arbitrary psi covers the faithful spectrum; psi and its
boundary density must actually be supplied. The mixed construction in
S8 remains valid without choosing a cyclic vector. Neither construction
automatically gives raw-stress/Q domains, the old N2 conditional
coherence, a Hadamard joint state or acceptable geometric moments.

## S4b. Why existing extension freedom does not pass the gate

Infinite deficiency indices, two-sided unbounded spectrum and a
conjugation symmetry do not fix a spectral measure. An explicit
diagnostic is S=-i partial_t on
L2((0,2pi)_t) tensor L2((0,1)_y), with H0^1 in t as its domain.
Both deficiency spaces are infinite. The compact core has arbitrarily
positive and negative expectations, and
(Jf)(t,y)=overline(f(2pi-t,y)) commutes with S.

The periodic extension f(2pi,y)=f(0,y) has pure point spectrum Z with
infinite multiplicity. The equally self-adjoint extension
f(2pi,y)=exp(2pi i y)f(0,y), after f=exp(i y t)g, becomes
-i partial_t+y on the periodic domain. Its spectral representation is
the direct sum of multiplication by n+y, n in Z; it has purely
absolutely continuous spectrum all R. Both domains are J invariant.
This example is a diagnostic, not a replacement operator for Rbar.

General results constructing chosen spectra by extension also require
a gap/regularity hypothesis on the underlying symmetric operator.
The required lower norm bound on the current target intervals has not
been proved for Rbar0. See Michelangeli, Section 1 Eq.(1.1),
https://arxiv.org/pdf/2304.02579, and Albeverio et al., Section 1,
https://web.ma.utexas.edu/mp_arc/c/04/04-177.pdf.
Their hypotheses cannot be supplied solely by n_+=n_-=infinity.

The next admissible construction must therefore specify a genuine
self-adjoint domain containing the original whole-kappa smooth core,
then compute S9 on the two fixed old radial intervals. Its full
adjoint boundary form must be controlled, including any kappa/source
infinity contributions. Imposing a kappa=0 hard wall and taking a
half-line Friedrichs domain generally removes original core functions
crossing zero; that solves a different minimal operator and cannot
silently select this Rbar extension. The physical CTP/initial-density
rule choosing the domain still remains to be constructed.


For a direct rejection of the simplest attempted shortcut, the raw
whole-kappa principal part is (a²/g)(partial_kappa-i A_K)².
Kappa=0 is an interior point with nonzero second-order coefficient.
A smooth positive-half-line function with value zero but nonzero
derivative at zero, extended by zero, produces
(a²/g)phi_+'(0) delta(kappa) under this operator.
It is not in the original whole-line adjoint L2 graph domain.
For piecewise smooth candidates, continuity of the function and its
covariant derivative removes the delta-prime and delta terms.
This is a concrete rejection of zero extension, not a complete trace
classification of the maximal adjoint domain.

## S5. The next physical recovery object

Choose an extension from an actual boundary/CTP preparation rule and
determine its spectral measure on the two old thin radial intervals.
Then verify the N2-conditional law, full bare-state coherences and
actual finite-u observables, followed by the original pure geometric
moments and common positive-time history.

A bounded Rbar band does not bound kappa moments or raw stress: its
operator is indefinite and cancellations are possible. No Hadamard
statement on quantum geometry, old-geometry recovery, full-field limit
or local autonomous preparation follows from S3 or S6 alone.
