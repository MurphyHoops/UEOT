# JC23 — Initial total enthalpy and a retained free-controller spatial row

## Why continue after the inverse

TOTAL_COLUMNS closes eight total-source means at the encoding slice of a finite-K actual autonomous model. It does not close its spatial Einstein equations or its fluctuation constraints. This entry identifies the initial total-enthalpy obstruction and a retained free-controller spatial row on the same model and gives an independent clock--energy uncertainty check. All claims use the declared positive/raw finite-K Hamiltonian and the stated initial preparation; a new covariant continuum subtraction is not supplied.

## 1. The initial complete enthalpy cannot be hidden in a constant

Use the complete Hilbert tensor on fixed unit ESU. For each conformal body species of constant mass square mu, spatially integrating the field equation gives
\[
 \int(\rho+p)
 =\int\left[{2\over3}\pi^2+{2\over3}|\nabla\Phi|^2
                  +{2+\mu\over3}\Phi^2\right]
       +{1\over3}\int\Phi_+\,\partial_{\Phi_+}V_{\rm int}
\]
after summing the body species and assigning the interaction consistently.
The minimal-controller contributions are
\(\int[\Pi_A^2+|\nabla A|^2/3]\), and the explicit potential contribution
to rho+p cancels. The displayed conformal interaction term remains because
the improved stress contains the second time derivative of Phi^2.

At finite K, the projected equation causes no error in this full spatial
integral: integral Phi_K P_K V_Phi=integral Phi_K V_Phi. This is not a
claim that arbitrary local Ward tests have no projection residual.

On the actual initial product Gaussian the cubic spatial mean is zero
because the Y mean is proportional to u dot Z and the clock/body
point distributions are rotation invariant. The quartic contribution is
nonnegative. The remaining quadratic terms are nonnegative since
mu=+/-1/5. Consequently
\[
 \int\langle\rho_{\rm total}+p_{\rm total}\rangle_{\rm initial,raw}
                         \ge {V_0\over g^2}.                   \tag{1}
\]
A fixed free-vacuum scalar subtraction does not cancel this state-dependent
kinetic increment. With a specified finite subtraction of size O_K(1),
that fixed term must be retained explicitly; it cannot scale away (1)
as g goes to zero.

For a static unit ESU, the 00 and spatial Einstein equations require
\(\int(\rho+p)=V_0/(4\pi G)\), independently of Lambda. Therefore merely
adjusting the cosmological constant does not restore this initial
static solution. Equation (1) is an initial-state result, not an
enthalpy lower bound at every later time or for arbitrary preparations.

## 2. The clock uncertainty independently verifies the full variance cost

For a real smooth spatial f with integral f=1 define
\(S_f=g\int fX_K\). The complete potential depends only on coordinate
fields, so on the common initial Schwartz domain
\[
 i[H_{\rm total},S_f]=g\int f\Pi_X,\qquad
 \langle i[H_{\rm total},S_f]\rangle=1 .
\]
Cauchy--Schwarz gives
\[
 \operatorname{Var}(H_{\rm total})\operatorname{Var}(S_f)\ge1/4.
\]
For f=1/V_0, the actual zero-mode packet has
Var(S_f)=g^2 a/V_0. Hence
\[
 \operatorname{Var}H_{\rm total}\ge {V_0\over4ag^2}
 ={V_0\over16g^2}\quad(a=4),
\]
in agreement with the independent real/imaginary wave-function proof
in BACKREACTION_GATE. Increasing the packet width to reduce this
lower bound increases the clock-argument uncertainty. This is a
finite-mode or properly spatially smeared clock statement, not a
point-clock continuum observable.

## 3. A nonzero spatial quadrupole remains at the encoding slice

Let
\[
 S=\epsilon\epsilon^T+\zeta\zeta^T,\qquad
 U_j=\mathbf u_j\cdot Z,\qquad
 Q_2(Z)=Z^TSZ-\tfrac14\operatorname{Tr}S .
\]
At T=pi the classical Y programs have c=1,c'=0. Their density is
exactly homogeneous:
\[
 \rho_{Y,\rm cl}={\|u\|^2\over2g^2},\qquad j_{Y,\rm cl}=0 .
\]
Their spatial tensor is
\[
 T_{ij,Y,\rm cl}
 ={1\over g^2}\sum_j[
       \nabla_iU_j\nabla_jU_j-\tfrac12\gamma_{ij}|\mathbf u_j|^2].
\]
Its spatial trace has second-harmonic part \(-Q_2/g^2\). Thus the
missing row is a spatial stress, not a falsely claimed inhomogeneous
classical density on this particular slice.

The sphere moment identity
\[
 \int Z_aZ_bZ_cZ_d\,dV
 ={V_0\over24}(\delta_{ab}\delta_{cd}
               +\delta_{ac}\delta_{bd}+\delta_{ad}\delta_{bc})
\]
gives
\[
 \|Q_2\|_2^2={V_0\over12}
 \left[\operatorname{Tr}(S^2)-{(\operatorname{Tr}S)^2\over4}\right]
 \ge {V_0\over48}\|u\|^4.                                      \tag{2}
\]
The last inequality uses positivity and rank S<=2. Therefore every
nonzero program in this two-Y model has a nonzero classical spatial
quadrupole. Two program vectors cannot produce a nonzero SO(4)-scalar
matrix S proportional to the four-dimensional identity.

## 4. The actual corrected program is nonzero, and the witness is actual

The declared cap profile f has a continuum center-direction density
moment greater than .029238025996284337, reused from the frozen input.
Because multiplication by Z connects neighboring k shells only,
\[
 \mathbf d-\mathbf d_K
 ={1\over2}\langle P_{k\ge K}f,\mathbf ZP_{k\ge K}f\rangle,\quad
 \|\mathbf d-\mathbf d_K\|
 \le{(22/5)^2\over2(K^2-1)} .
\]
At K=64 this is below .002365, so the target vector d_K is nonzero.

Fix eta=10^-13 and the nonzero target y=(-eta^2 d_K,0).
The actual corrected programs converge to the unique limiting inverse
u_0 as g goes to zero, by the uniform contraction in TOTAL_COLUMNS.
Since F_lim(0)=0, u_0 is nonzero. The conservative derivative bound
\(\|DF_{\rm lim}\|<2000\) on the declared control ball follows from
the controller Frobenius bound and scale, the body norm below six
and the already bounded nonlinear remainder. Thus
\[
 \|u_0\|\ge{\eta^2\|\mathbf d_K\|\over2000}>1.3\,10^{-31}.         \tag{3}
\]

The free-Y tensor is the leading coefficient of its **actual component**
mean, not a value transferred by trace distance alone. For a fixed smooth
second-harmonic test f, the free-Y quadratic spatial trace T_Y(f) has a
uniform H_pos form bound. The positive completion retains the Y kinetic,
gradient and mass forms, and no projected interaction force occurs in this
minimal-field component.

Pulling T_Y(f) into the coherent frame gives the g^-2 classical identity,
g^-1 linear fluctuation and quadratic fluctuation terms. The centered
reference has zero linear mean; its first parametrix correction gives
only O(1). The N=7 energy-form interpolation bounds the actual-state error.
Consequently, at fixed K and along the corrected program family,
\[
 g^2\,\Pi_{\ell=2}
   \langle\gamma^{ij}T_{ij,Y}^{\rm free}\rangle_{\rm actual}
                   \longrightarrow -Q_2(u_0).                 \tag{4}
\]
Taking f=Q_2(u_0) gives a nonzero actual free-controller witness. This is a
finite harmonic mean, not a sharp stress variance. The extra sufficiently
small g threshold is not numerically bounded, so it is not assigned to the
specifically fixed g=10^-40 example.

## 5. Closing the projected-force gap with a stronger graph estimate

The density/current H_pos form estimate alone does not control
\[
 Q_f=\int P_K(f\Phi_+)\,\partial_{\Phi_+}V_{\rm int}.
\]
The projection cannot be deleted when f is a second harmonic. The
following additional argument closes the mean domain at fixed K.

In real canonical mode coordinates write H_g=-Delta_q/2+V_g. The raw
positive completion gives V_g>=R^2/8, where R^2 is the sum of the two Y
and two body coordinate norms squared; the uncontrolled X zero-mode
coordinate is not included. All F derivatives are bounded. With
n_K=sum k^2, A_K=n_K/V_0, S_F=F_0^2+F_1^2,
M=(sum ||F_j||_infty^2)^1/2 and
M_2=(sum ||F_j''||_infty^2)^1/2, direct coordinate differentiation gives
\[
 \Delta_q V_g\le a_0+a_1gR+a_2g^2R^2+a_3g^3R^3+a_4g^4R^4,
\]
where one may take
\[
 a_0=\sum_{k=1}^K k^2(5k^2-1),\quad
 a_1={n_K M\over\sqrt{V_0}},\quad
 a_2=3A_K\|S_F\|_\infty,
\]
\[
 a_3={A_K^{3/2}M_2\over2},\qquad
 a_4={A_K^2\|S_F''\|_\infty\over4}.
\]
For some 0<g_0(K)<=1 choose a_4 g_0^4<=1/128.
Young's inequality bounds all lower-degree terms by R^4/128+C_K,
uniformly for g<=g_0. Hence Delta V_g<=V_g^2+C_K.
The exact compact-core identity is
\[
 \|H_g\psi\|^2={1\over4}\|\Delta\psi\|^2+\|V_g\psi\|^2
 +\int V_g|\nabla\psi|^2-\tfrac12\int(\Delta V_g)|\psi|^2.
\]
It implies
\[
 \|V_g\psi\|^2\le2\|H_g\psi\|^2+C_K\|\psi\|^2.             \tag{5}
\]
The compact smooth core established for this nonnegative finite-mode
Schrodinger potential extends (5) to D(H_g), using closedness of the
multiplication operator V_g. This does not assume actual Schwartz
propagation.

Projection contraction and finite-mode point evaluation give
\[
 |Q_f(q)|\le\|f\|_\infty
  [g\sqrt{A_K}M R^3+g^2A_K\|S_F\|_\infty R^4]
 \le C_{K,f}(1+V_g^2).
\]
Thus Q_f is an H_g^2-form on D(H_g):
\[
 |Q_f(\psi,\chi)|
 \le C_{K,f}\|(H_g+1)\psi\|\|(H_g+1)\chi\|.                \tag{6}
\]
This is a mean-form domain statement. It does not prove
D(H_g) subset D(Q_f) or finiteness of the Q_f^2 noise.

Raise the existing Gaussian-polynomial parametrix to order N. In the
coherent frame H_g=g^-2 E_cl I+g^-1 L+Q+R_int, where R_int contains no
negative g powers. Acting twice on the finite-K Gaussian-polynomial
approximation, or on the initial Gaussian, gives uniformly
||H_g^2 psi_N||=O(g^-4); one program derivative is O(g^-5).
The actual vector inherits the same bounds from autonomous spectral
conservation. Together with norm errors O(g^(N+1)) and derivative
O(g^N), interpolation in (6) gives mean error
O(g^((N-7)/2)) and derivative error O(g^((N-9)/2)).
N=9 therefore suffices for the present O(g) mean error; N=11 would
suffice for C1 control. No stronger domain is inferred from norm
distance alone.

For clarity the actual finite-K projected equation gives the tested
body-plus-interaction spatial trace exactly as
\[
 \sum_{\sigma=\pm}\int f\left[
 H_{\rm can,free,\sigma}-\mu_\sigma\Phi_\sigma^2
                         -\tfrac16\Delta(\Phi_\sigma^2)\right]
                  +Q_f-3\int f V_{\rm int}.                \tag{7}
\]
The other terms already have quadratic/positive-energy form control.
At T=pi every jet of F_j at the classical clock value vanishes.
The bound |F_j(pi+g xi)|<=C_m g^m |xi|^m controls the Gaussian-polynomial
approximation to any prescribed order, so (5)--(6) imply the actual
Q_f mean is O(g). The body terms are O(1); the leading X stress is
homogeneous. Combining (4)--(7) therefore gives
\[
 \boxed{g^2\Pi_{\ell=2}
 \langle\gamma^{ij}T_{ij,\rm total}^{(K)}\rangle_{\rm actual}
                          \longrightarrow -Q_2(u_0).}       \tag{8}
\]
Here T_total^(K) is precisely the formal Hilbert tensor of the declared
finite-mode raw action evaluated with its projected field equation.
No continuum local Ward identity, covariant cutoff limit or sharp
stress variance is asserted.

Its limiting L2 norm is strictly greater than 1e-62 by (2)--(3).
For a unit-normalized single test use f=Q_2/||Q_2||; the unnormalized
test f=Q_2 instead measures the square of that norm.
For all sufficiently small g below the additional unquantified
threshold this full finite-mode spatial row is nonzero, even after
the eight first-harmonic means have been repaired. The conclusion
has not been assigned to the fixed g=10^-40 example without a bound
on that threshold.

## 6. One exact full-source lapse/noise column

There is also a positive result for the complete fixed-K source.
On an autonomous segment with homogeneous lapse N(t)>0, fixed spatial
metric gamma and zero shift, the same raw action gives exactly
H[N](t)=N(t)H_total. Every included scalar constant also scales with N.
The common initial normal state therefore has
\[
 Z[N_+,N_-]=\operatorname{Tr}\rho\,
       e^{-i(\tau_+-\tau_-)H_{\rm total}},\qquad
 \tau_\pm=\int N_\pm(t)\,dt .
\]
Its second connected lapse variation is the full energy variance,
including the apparatus and all cross terms; at the stated initial
preparation it is at least V_0/(16g^2). Variations with integral delta N=0
vanish exactly, as required for this endpoint-fixed reparameterization.
This is one homogeneous CTP/noise column on an autonomous segment.
An intermediate encoder or reader must remain explicitly time-ordered;
noncommuting interventions cannot be absorbed into one total tau.
No general local metric Hessian or quantum Einstein constraint is inferred.

## Decision after reflection

The same actual finite-mode model can prepare a normal total source,
repair eight first-harmonic means and retain a complete positive
record. Its initial complete enthalpy fails the intended static homogeneous
geometry. The stronger graph argument also proves a later nonzero total
second-harmonic spatial trace within this fixed-K raw model. Neither
result supplies its new geometry or its continuum tensor/noise. The
operator and ultraviolet obligations remain as well.

The next common-history problem must include the geometry's spatial
response, its prepared Hadamard data and total apparatus stress.
Adding fields or changing the program could alter this particular
quadrupole witness, but would require a new action, resource ledger
and actual-state proof. No general impossibility of physical
unification is inferred.
