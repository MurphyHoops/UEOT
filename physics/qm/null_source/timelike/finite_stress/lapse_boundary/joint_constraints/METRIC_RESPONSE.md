# AS: same-preparation metric response at a common finite cutoff

## 1. Action, canonical chart and cutoff contract

Use the preceding local linear two-field action, signature (-+++), and
Phi=(phi,psi), mass/source matrix r sigma_x. The spacetime metric is
ds^2=-N^2dt^2+h_ij(dx^i+beta^i dt)(dx^j+beta^j dt).
Keep N, beta, h and the full four-dimensional R[g] until variation.
The comparison geometry is initially the unit ESU, with dV_gamma and
real spherical harmonics Y_a, -Delta_gamma Y_a=(k_a^2-1)Y_a.

Let w=sqrt(det h)/sqrt(det gamma), pi_A=w(N^-1)(dot Phi_A-beta.grad Phi_A).
The reference symplectic variables are the harmonic coefficients q,p
of Phi,pi. Project the canonical action onto a common finite harmonic
space P_K, with all degeneracies. This is an explicitly specified
canonical cutoff. It is not the different operation of first truncating
the Lagrangian kinetic matrix and then inverting that matrix.

For z=(q,p), [z,z^T]=iJ, J=[[0,I],[-I,0]],
H_K=1/2 z^T G_K z+c_K[g,r], with Weyl ordering and
G_K=[[B,C^T],[C,A]]. Species identity factors are implicit in A,C:
\[
 A_{ab}=\int {N\over w}Y_aY_b\,dV_\gamma,\quad
 C_{ab}=\int Y_a\beta^i\partial_iY_b\,dV_\gamma,
\]
\[
 B_{Aa,Bb}=\int Nw\{h^{ij}\partial_iY_a\partial_jY_b\,\delta_{AB}
  +[R[g]\delta_{AB}/6+r(\sigma_x)_{AB}]Y_aY_b\}\,dV_\gamma.
\]
c_K is the scalar counterterm/phase datum; its derivatives are retained.
These are matter evolution operators on an external metric history,
not the already-reduced canonical Hamiltonian of quantum gravity.
R[g] contains metric derivatives; suppressing them changes the response.

## 2. Explicit ESU columns and the boundary term

Write delta N=n, delta beta=b, delta h_ij=k_ij and k=tr_gamma k.
Direct four-dimensional curvature variation gives
\[
 \delta R=Lk+\ddot k-2\partial_t\operatorname{div}b-2\Delta n,\quad
 Lk=\nabla^i\nabla^j k_{ij}-\Delta k-2k.
\]
The actual first columns are
\[
 \delta A_{ab}=\int(n-k/2)Y_aY_b,\qquad
 \delta C_{ab}=\int Y_a b^i\partial_iY_b,
\]
\[
 \delta B_{Aa,Bb}=\int\{[(n+k/2)\gamma^{ij}-k^{ij}]
       \partial_iY_a\partial_jY_b\,\delta_{AB}
 +[(n+k/2)(I+r\sigma_x)+\delta R\,I/6+\delta r\,\sigma_x]_{AB}Y_aY_b\}.
\]
All integrals use dV_gamma. In particular, a spatial lapse n has
delta R=-2 Delta n, giving the improved density term -Delta(Phi^T Phi)/6.
An arbitrary lapse cannot be represented by multiplying the global H alone.

Let Q=phi^2+psi^2. At the reference background, using the field equations
and integrating metric derivatives by parts yields
\[
 \int\delta H_Kdt=\int dt\,dV_\gamma
 [nT_{00}+b^iT_{0i}-\tfrac12k_{ij}T^{ij}+\delta r\,\phi\psi]
 +{1\over12}\left[\int((\dot k-2\operatorname{div}b)Q-k\dot Q)dV_\gamma\right]_{t_i}^{t_f}
 +\int\delta c_Kdt .
\]
One may instead keep the metric jets unintegrated. If the endpoint
variations do not vanish, the displayed boundary term must remain.
At finite K these are common projected bilinear identities at the
reference diagonal background. They do not assert unrestricted
finite-cutoff diffeomorphism covariance at all orders.

For homogeneous k_ij=2u gamma_ij, this boundary is
[ (u'Q-u Q')/2 ]. In conformal coordinates, q=a Phi, h=a'/a,
the exact field action is
\[
 S=S_{\rm bulk}[q;r a^2]-[h(q_s^2+q_p^2)/2].
\]
At a=1, fixed q gives the endpoint variation -[u'Q/2].
At fixed Phi there is also delta q=u q, so the bulk field variation
contributes [p delta q]=[u Q'/2], with the Euler term retained off shell.
Together these give minus the Hamiltonian boundary above. Fixed-q and
fixed-Phi variations cannot be silently interchanged. A full conformal
metric variation also has delta N=u at the reference point.

## 3. Actual preparation, not a replacement ground at each metric

Let Sdot=J G_K S and S(t_i,t_i)=I. For a Gaussian incoming state with
mean m_in and symmetrized covariance V_in,
m(t)=S(t,t_i)m_in and V(t)=S(t,t_i)V_in S(t,t_i)^T
(the affine-force term can be included by augmenting z with 1).
For a physical variation,
\[
 \delta V(t)=S(t,t_i)\delta V_{\rm in}S(t,t_i)^T+
 \int_{t_i}^t S(t,s)[J\delta G_K(s)V(s)-V(s)\delta G_K(s)J]S(t,s)^Tds .
\]
The analogous Duhamel equation holds for m. This formula includes the
actual preparation interval. Its endpoint is not the derivative of a
newly selected ground covariance unless that different preparation is
explicitly implemented.

For A=1/2 z^T M z+ell^T z+c,
\[
 \langle A\rangle=\tfrac12\operatorname{tr}(MV)+\tfrac12m^TMm+\ell^Tm+c.
\]
Differentiation retains delta M, delta ell, delta c, delta m and delta V.
Thus normal/volume/source/curvature contacts and state response are
separate columns of the same calculation. Finite-cutoff response is
\[
 \delta\langle A(t)\rangle=\langle\delta A(t)\rangle
 -i\int_{t_i}^t\langle[A(t),\delta H(s)]\rangle ds
 +\operatorname{Tr}(A_H(t)\delta\rho_{\rm in}).
\]

## 4. The initial mixed CTP block is fixed by preparation

For the same incoming density operator on both branches define
\[
 {\cal R}_{\rm pre}[g_+,g_-]
 =U_{\rm pre}[g_+]\rho_{\rm in}U_{\rm pre}[g_-]^\dagger.
\]
This fixes the off-diagonal kernel, not just its diagonal density family.
With G_a=int U(s,t_i)^dagger H_a(s)U(s,t_i) ds, including the actual
metric jets, boundary terms and scalar phase, at a common history U_0:
\[
 \partial_{+a}{\cal R}=-iU_0G_a\rho_{\rm in}U_0^\dagger,\quad
 \partial_{-b}{\cal R}=+iU_0\rho_{\rm in}G_bU_0^\dagger,
\]
\[
 \boxed{\partial_{+a}\partial_{-b}{\cal R}
       =U_0G_a\rho_{\rm in}G_bU_0^\dagger.}
\]
The physical diagonal derivative is -iU_0[G_a,rho_in]U_0^dagger.
The mixed block is generally nonzero and is source-containing.
If rho_in itself varies, an actual earlier preparation or a declared
common purification must determine its off-diagonal branch kernel too;
the separate diagonal ground covariances do not determine it.

For any finite collection of histories, the full CTP functional
Tr(U_i rho_in U_j^dagger) is a positive Gram matrix. This finite-cutoff
positivity is not a solution of quantum Einstein constraints.

## 5. Complete Gaussian noise, including its quantum term

Define
Gamma(t,s)=S(t,t_i)(V_in+iJ/2)S(s,t_i)^T and b_a=M_a m+ell_a.
Wick contraction on the same state gives the connected Wightman kernel
\[
 C_{ab}(t,s)=\tfrac12\operatorname{tr}
 [M_a(t)\Gamma(t,s)M_b(s)\Gamma(t,s)^T]
 +b_a(t)^T\Gamma(t,s)b_b(s).
\]
The last matrix operation is transpose, not adjoint. The noise is
N=Re C, a positive semidefinite real test-function Gram kernel;
the retarded response for +source*A in H is 2 theta(t-s) Im C,
together with contact and initial terms.

At equal times,
\[
 N(A,A)=\tfrac12\operatorname{tr}(MVMV)
       +\tfrac18\operatorname{tr}(MJMJ)+b^TVb.
\]
The J term cannot be discarded: it exactly cancels the apparent energy
variance of a ground-state oscillator. Real scalar counterterms change
contacts/means and phases, but not this centered noise.

## 6. A nontrivial first-harmonic Ward witness

For one normal species mu=+/-r, retain its k=1 constant mode and the
k=2 mode Y_1=2Z/sqrt(V0), Z=x_4. Since int ZY_0Y_1=1/2,
\[
 H=\tfrac12[p_0^2+p_1^2+(1+\mu)q_0^2+(4+\mu)q_1^2],
\quad A=\int ZT_{00}=\tfrac12[p_0p_1+(2+\mu)q_0q_1],
\]
\[
 O=\tfrac12\int Z\Phi^2=\tfrac12q_0q_1,\quad
 D=\int p\nabla Z\cdot\nabla q=\tfrac32p_0q_1,\quad
 J_Z=D-\dot O=p_0q_1-\tfrac12q_0p_1.
\]
Exactly, dot A=-J_Z. The pure spacetime gauge perturbation
k_ij=2u Z gamma_ij, n=-u''Z, b=0 has delta R=0 and
\[
 \delta H=-\tfrac12(u''+3u)p_0p_1+
          \tfrac12(1+\mu)(3u-u'')q_0q_1
       =\dot F+i[H,F],\quad F=-uD-u'(A-O).
\]
For u,u' zero at the endpoints its integrated interaction-picture
generator vanishes. A time-dependent spatial trace alone, with n=0,
instead has delta R=6u''Z and need not be pure gauge.

Because the reference H_0 commutes with its spectral P_K, this specific
first-order projected commutator identity holds at finite K. That fact
does not license dropping projector/basis transport for arbitrary
histories, higher variations or entire natural metric families.
On an active AQ source history the same spacetime gauge variation also
requires delta r=xi^0 rdot=-u'Z rdot.

More generally delta H=Fdot+i[H,F] gives preparation generator
F_H(t_0)-F(t_i). A naturally transported incoming density has
delta rho_in=-i[F(t_i),rho_in], which cancels the otherwise spurious
initial contribution. The actual initial mixed kernel must be transported
on both branches as well.

## 7. Verification and remaining gates

The certificate checks the exact polynomial Ward/end-point identities,
ground-energy quantum-noise cancellation, and an actual two-mode
preparation derivative against its exact pair Kubo response and a
matrix-exponential derivative. Numerical matrix checks are declared
finite-dimensional tolerance checks, not continuum evidence.

No sharp arbitrary-spatial metric derivative, common-bare-Fock normal
family, full renormalized response limit, dynamical apparatus, normal
quantum geometry state, or Einstein solution is inferred from these
identities. Their continuum domains and the independent zeroth
background/preparation conditions are the next gates.

Stress/renormalization convention: Moretti, gr-qc/0109048, Sections2--3.
The finite-cutoff matrix, initial mixed-block and Ward witnesses above
are explicitly derived here. They are not new counted Core theorems.
