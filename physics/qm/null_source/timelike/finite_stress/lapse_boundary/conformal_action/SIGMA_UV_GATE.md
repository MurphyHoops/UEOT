# J. A required four-derivative term in the full field extension

## J1. A definite ultraviolet test of the actual three-field metric

This is a one-loop NECESSARY-DATA test for the inhomogeneous quantum
extension of LOCAL_AUTONOMOUS. It is not a modification of the already
declared homogeneous Laplace-Beltrami quantization.

In physical target coordinates X=(chi,phi,psi), let
G=dchi²+dphi²+dpsi²+2k_c(chi)dphi dpsi, |k_c|<1.
On a flat Euclidean spacetime patch take the background

 chi=chi0, phi=v x0, psi=0, with k_c'(chi0) nonzero.

It is on shell because Gamma^A_(phi phi)=0. The unit tangent is
e_phi; an orthonormal transverse basis is e_chi and
(e_psi-k_c e_phi)/sqrt(1-k_c²). Direct target curvature calculation
gives the two Jacobi eigenvalues

 a v², a v²,  a=k_c'²/[4(1-k_c²)],                     (J1)

up to the common curvature/Hessian sign convention. The third
eigenvalue is zero. The sign does not affect tr E². The background
gradient has rank one, so the pullback connection curvature
Omega_mu nu vanishes. E is covariantly constant here. Thus

 tr E²=k_c'⁴ v⁴/[8(1-k_c²)²].

For D=-(nabla²+E) in FOUR spacetime dimensions, the flat heat a4
density, excluding total derivatives, is

 (4pi)^-2 tr(E²/2+Omega_mu nu Omega^mu nu/12)
 =(4pi)^-2 k_c'⁴ v⁴/[16(1-k_c²)²] >0.                 (J2)

This coefficient requires a local four-derivative sigma-model
counterterm. Changing only G_AB(X), Lambda, Newton's coefficient or
the old pure-curvature terms cannot absorb this v⁴ dependence on a
flat background. The statement does not preclude additional matter
fields, supersymmetry, a cutoff EFT or a different UV completion.

For an integrated on-shell check, use flat Lorentzian spacetime with
chi=chi0, psi=0 and phi=F(t-x)+G(t+x), where F,G are smooth compact
wave packets. It is again on shell. [(grad phi)²]²=16 F'²G'² has
positive overlap integral (use a finite transverse torus). The
integrated heat total derivative vanishes. Local derivative field
redefinitions may move this term within a four-derivative basis; they
do not justify silently keeping only the original two-derivative
action. No full counterterm-basis classification is claimed here.

A second witness follows the controller itself:
chi=vx0, phi=psi=0. Its transverse sectional curvatures are

 r_+=-k_c''/[2(1+k_c)]+k_c'²/[4(1+k_c)²],
 r_-= k_c''/[2(1-k_c)]+k_c'²/[4(1-k_c)²].

The non-derivative heat density is
(4pi)^-2 v⁴(r_+²+r_-²)/2. For the nontrivial compact coupling pulse
this has positive integral, whereas the total derivative integrates
to zero. Adding only a phi four-derivative term would therefore not
complete the entire interacting field theory.

## J2. Heat coefficient versus determinant convention

The coefficient (J2) is a HEAT coefficient. For the explicitly chosen
proper-time convention
W_Lambda=-(1/2) integral_(Lambda^-2)^infinity dt Tr exp(-tD)/t,
its logarithmic term is -a4 log(Lambda/mu); the required counterterm
has the opposite sign. An infrared regulator may be needed separately.
Nothing here proves positivity of the full Hessian or existence of a
global interacting state.

Primary reference actually inspected:
D.V. Vassilevich, Heat kernel expansion: user's manual,
https://arxiv.org/abs/hep-th/0306138, equations (2.2), (3.16), (4.28),
and (1.20)/(2.31). Section 3.2 illustrates a two-dimensional worldsheet;
we use its dimension-independent geodesic second variation and the
SEPARATE four-dimensional a4 formula, not a two-dimensional beta function.

## J3. The new term changes the homogeneous energy scaling as well

For example add, locally, the Lorentzian homogeneous contribution
L4=V c4(chi) phi'^4/N³. With v=phi'/N, the unperturbed canonical
velocity is v0=(p_phi-k_c p_psi)/[Va²(1-k_c²)].
At fixed canonical momenta, the first-order Legendre correction is

 delta T=-c4(p_phi-k_c p_psi)^4/[V³a⁸(1-k_c²)^4].        (J3)

The terms from the velocity correction cancel by stationarity of
the unperturbed Legendre transform. The simpler -c4 p_phi^4/(V³a⁸)
requires the single-phi-velocity restriction p_psi=k_c p_phi.

Under the one fixed change q=s_*X, s_*=sqrt(V)a_*,
k_c'=s_* k_q', v_old=v_q/s_*, so k_c'⁴v_old⁴ is unchanged.
The full field action in q keeps its overall s_*^-2 metric factor;
it is not obtained by deleting that factor. Set C_q=c4/s_*⁴.
Then (J3) reads

 delta T=-V C_q f(u)^4[(P_phi-k P_psi)/(1-k²)]^4,
 f(u)=a_*²/a².                                         (J4)

The old two-derivative term scales as fK. In general the new
coefficient depends on Q_chi and does not commute with P_chi².
Thus the exact common commuting fK spectral evolution is NOT inherited
by the renormalized field extension. A new action, ordering, contact
matrix, domain and evolution estimate must be supplied.

## J4. Closure and next concrete acceptance object

Completed: a specific nonzero on-shell one-loop UV coefficient and
its effect on the retained lapse/energy scaling have been derived.
Rejected: promoting the bare homogeneous apparatus theorem to a full
four-dimensional quantum apparatus while leaving its action unchanged.

Next: specify the required renormalized four-derivative matter
couplings and independent curvature couplings, retain both CTP
lapses and a common initial state, then derive the new mixed constraint
and contacts. The coefficient values are physical input; the
homogeneous fit alone does not determine them. Physical unification
and the complete four-dimensional apparatus remain open.
