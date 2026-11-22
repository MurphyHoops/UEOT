# Mean-history recovery: geometric resource and tail gates

## M1. The exact original-frame quantity and its domain contract

For the ordering family in ORDERING_DOMAIN, the complete original bulk
snapshot has the core expression
\[
 H_\eta=\frac{A_{\eta,\mathrm{cov}}}{2g}
 +\frac{H_{0,K}}{\kappa}-\kappa Q_K
 +\frac{d_0}{\kappa}+d_1\kappa+d_3\kappa^3.                 \tag{M1}
\]
Here A_eta,cov=W A_eta W† and Q_K>=0. Neither the source connection nor
the negative source-coordinate term is deleted.

The following inequalities concern normal joint states with legitimate
finite canonical budgets. A sufficient precise class is: purification in
D(H_eta) with finite covariant principal form, <H0/Kappa>, <kappa³>,
and source <Q_K²>. For mixtures use the corresponding trace budgets and
finite Tr(rho H_eta²). These conditions make every term below well-defined.
Compact-kappa, joint-Schwartz approximations are dense in the positive
sum of these form norms. Source and kappa cutoffs commute with the
multiplication connection; the Friedrichs endpoint approximation uses
the closed ground-state form. Testing H_eta on this common core and
passing in the positive-form norm identifies its spectral expectation
with M1. No operator-core assertion for the bare common core is required:
the vector is already in D(H_eta), and <test,H_eta psi> passes in L2.

The same estimates apply to any broader state class where that core/form
expectation identity is proved. They are not claims about all normal states
with undefined separate moments or a cancellation of infinity minus infinity.

Let m=<kappa>, I=<1/kappa>, q2=sqrt(Tr sigma Q_K²),
a=1/(2g)>0, M=|d0|. ORDERING_DOMAIN gives q_cov>=alpha² I²/m.
If m²<=2a alpha²/M (automatic if M=0), minimization over I>=1/m gives
\[
 a q_{\rm cov}-M I
 \ge \frac{a\alpha^2}{m^3}-\frac{M}{m}.                    \tag{M2}
\]
This argument allows entanglement and arbitrary kappa tails.

## M2. Positive cubic coefficient: a source-resource obstruction

When d3>0, kappa and Q_K strongly commute. Scalar minimization yields
\[
 d_3\kappa^3-\kappa Q_K
 \ge-\frac{2Q_K^{3/2}}{3\sqrt{3d_3}},\qquad
 \langle Q_K^{3/2}\rangle\le q_2^{3/2}.
\]
Since H0/Kappa>=0,
\[
 \boxed{\langle H_\eta\rangle\ge
 \frac{a\alpha^2}{m^3}-\frac{M}{m}
 -\frac{2q_2^{3/2}}{3\sqrt{3d_3}}+d_1m.}                  \tag{M3}
\]
For K=65536 on the actual patch, g<.05, d3>.01, d1>0 and M<exp(50).
At the same old initial mean m=h_i<exp(-19980), either the original
source (q2<exp(50)) or the predecessor incoming preparation at delta=1e-6
(q2<exp(60)) gives, for every eta>=-1/4,
\[
 \langle H_\eta\rangle>\exp(59000).                         \tag{M4}
\]
In contrast the old original bulk canonical target has
|P_u,ref|<exp(60). On physical solutions P_u=-H_eta wherever this
moment is defined. These particular normal finite-budget states cannot
recover that initial canonical mean budget. Arbitrary correlations do
not change M3 if the same source marginal/budget is kept.

Conversely, demanding m=h_i and |<P_u>|<=exp(60) in this coefficient
branch forces the deliberately loose necessary condition
\[
 \boxed{q_2\ge\frac1{100h_i^2}.}                            \tag{M5}
\]
The script checks the inequalities with log-domain margins. No experimental
energy or metric fluctuation is inferred. The kinetic resource is in
hbar=1 units; restoring hbar restores its square in the principal term.
This rejects a proposed quantum recovery of the old history; it does not
invalidate the already established classical mean-SCE solution.

## M3. All positive-g cutoffs: a third-moment frontier

A negative d3 cannot use M3. The exact uniform replacement is
\[
 \kappa Q_K\le\kappa^3+\frac{2}{3\sqrt3}Q_K^{3/2},
\]
\[
 \langle H_\eta\rangle\ge\frac{a\alpha^2}{m^3}-\frac{M}{m}
 -(|d_3|+1)\langle\kappa^3\rangle
 -\frac{2q_2^{3/2}}{3\sqrt3}+d_1m.                         \tag{M6}
\]
For every K>=2 that has g>0 on the declared patch, the actual coefficients
obey g<3, K<1e5, |d3|<2, d1>0, M<exp(50).
Thus a alpha²>=1/6. With the old m, q2<=exp(60) and
|<H_eta>|<=exp(60), M6 requires
\[
 \boxed{\langle\kappa^3\rangle>\frac1{36m^3},\qquad
 \frac{\langle\kappa^3\rangle}{m^3}>\frac1{36m^6}.}           \tag{M7}
\]
This is a condition on the third moment itself. A bounded relative second
moment alone does not control it.

## M4. A real escape from the positive-potential argument, and its price

For g>0,d3<0, keep the original finite-K source marginal exactly fixed.
Use compact smooth geometric packs in the original bulk frame, with the
scalar phase exp i(B_K kappa-H_K kappa³/12) that removes A_K.
Their covariant kinetic expectation contains the positive
<Q_K²><1/kappa> contribution; it is finite for each pack.

Take a base pack of mean m0<m, and a distant pack of fixed width and mean L.
Mix with weight (m-m0)/(L-m0). The exact geometry mean is m, every member
is normal with finite moments, and the source marginal is unchanged.
The negative cubic contribution grows as d3(m-m0)L², so the complete
snapshot mean tends to minus infinity while all other terms grow more
slowly. A positive high-gradient base pack permits interpolation through
a prescribed finite snapshot energy. This recovers only two initial
means, not all canonical jets or the later mean history.

Balancing a typical m^-3 principal cost by this construction uses
L of order m^-2 and probability of order m^3, producing
<kappa²> of order m^-1 and <kappa³> of order m^-3.
Even a separate bounded-relative-second-moment condition is insufficient
in general: weights of order L^-2 and a base-mean adjustment preserve it
while the cubic moment diverges. M7 states the relevant tail cost directly.

Hence the lens extension is a real dynamics result, but small K and an
inverted cubic coefficient do not supply controlled semiclassical recovery.
Nothing here excludes other branches, measures, physical boundary choices,
source preparations, or a properly renormalized combined continuum theory.
