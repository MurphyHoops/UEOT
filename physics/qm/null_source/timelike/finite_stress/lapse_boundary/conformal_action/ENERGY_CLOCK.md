# M. An energy-conditioned clock with a full normal Fock kernel

## M1. A different physical slicing, explicitly declared

This is a comparison in the NEW critical conformal model, without
the apparatus. It does not repair the old minimally coupled operator
by changing a test or claiming that a zero kernel became nonzero.

Let N_q=dGamma(k)>=0 and fix N0=1, u_*=.55, d=.01. Define

 f(N)=u_*+(1/4)log(1+N/N0), tau=u-f(N),
 a=a_* exp(tau)(1+N/N0)^(1/4), a_*=Aexp(u_*).           (M1)

The physical slices now depend on total source energy. An upper
energy cutoff no longer shares the old common-u slice. Put
r=N/a⁴. For |tau|<=d,

 0<=r<=r_max=N0 a_*^-4 exp(4d).

With m=3V/2 and a_c=1/240 choose the lower root

 y(r)=2(VU_0+r)/[m+sqrt(m²-4a_c(VU_0+r))],
 kappa²=a²y(r)-1.                                      (M2)

The certificate verifies r_max<m²/(4a_c)-VU_0 and
a_*² exp(-2d)y(0)>1+.9² for the frozen parameter intervals.
Thus every Fock energy is admitted on the same tau chart.
The expanding sign and lower branch are chosen once.

## M2. Exact self-adjoint evolution and domains

The selected reduced generator is

 h_tau(tau,N)=kappa[
    a²(2m-4a_c y/3)-8a_c/3].                           (M3)

Uniformly on the compact tau chart there are strictly positive
constants c,C such that

 c(1+N)^(3/4)<=h_tau<=C(1+N)^(3/4),
 c(1+N)^(1/4)<=kappa<=C(1+N)^(1/4).

The same order bounds hold for the needed tau derivatives.
They follow from the strict discriminant margin, bounded r and
positive coefficients in (M3); r_tau=-4r.

Therefore h_tau(tau,N_q) is self-adjoint and semibounded on the common
domain D((1+N_q)^(3/4)). Its exact diagonal unitary is
U_tau=exp[-i integral h_tau dtau]. Every normal Fock density operator
evolves normally; finite energy expectation is not required for
bounded observables. Smooth vectors lie in the stated operator domain.

Let R=sqrt(kappa). D(R)=D((1+N_q)^(1/8)), while R^-1 is bounded.
The selected normal form is C_tau=R(P_tau+h_tau)R.
Raw kernels are R^-1 U rho U* R^-1, trace class at each pair of times;
their weighted diagonal trace is one. The separate raw propagator
K_raw=R^-1 U R^-1 obeys weighted gluing. A prepared mixed-state kernel
composes with rho², not rho.

For high-mode-vacuum projections P_K, exact spectral commutation gives
U_K P_K=U_infinity P_K and uniform strong/adjoint convergence.
For any normal rho, normalized P_K rho P_K converge in trace norm.
Two-time physical-kernel trace norm error equals the initial error.
Fixed nonzero compact physical tests give positive kernel values.
Normality alone does not imply Hadamard or finite stress moments.

## M3. Exact finite-energy test complex

On Phi0=C_c^infinity(J_tau) tensor finite-energy Fock vectors, set

 T(phi)=integral U(tau_i,r) R(r)^-1 phi(r) dr.

Then T C_tau=0 by integration by parts. Conversely, if T(phi)=0,
define q(tau)=i integral_left^tau U(tau_i,r)R(r)^-1 phi(r)dr.
It is compactly supported, and
psi=R^-1 U(tau,tau_i)q belongs to Phi0 with C_tau psi=phi.
Thus

 0 -> Phi0 --C_tau--> Phi0 --T--> Fock_fin -> 0

is exact. The first map is injective by uniqueness and compact support;
surjectivity of T follows by a fixed unit-integral bump on each finite
energy subspace. This is a proof of the test-space quotient, not an
inverse-propagator instrument or a physical preparation protocol.
The physical completion is the full Fock norm.

## M4. Exact controlled translation and canonical qualifications

On L²(R_u) tensor Fock define
J=exp[i P_u f(N_q)], (J psi)_N(tau)=psi_N(tau+f(N)).
It is unitary, P_u is unchanged and J u J*=tau+f(N_q).
It transports the DECLARED selected constraint and spectral
coefficients exactly on the finite-energy compact core, and then
the appropriate graph/physical completions.

J need not be bounded on the entire L¹(time;Fock) test class:
choose energies N_j with disjoint translated bump supports and
X_M=chi(tau) M^-1/2 sum_(j=1)^M e_j.
Its L¹ norm is ||chi||1 whereas ||J*X_M||1=sqrt(M)||chi||1.
This does not undermine L² unitarity, nor prove that every weighted
physical test loses integrability. It prevents an unjustified
identification of all old fixed-u L¹ tests with the new slicing.

Classically, for a homogeneous quadratic N_cl with the symmetric
source potential theta_s satisfying theta_s(X_N)=N_cl, the
source flow Z=Phi_N^(-P_u f')z gives

 P_u du+theta_s(z)
   =P_tau dtau+theta_s(Z)+d[P_tau N_cl f'(N_cl)].        (M4)

If instead N_tilde=H_raw-E0,K, then
theta_s(X_Ntilde)=N_tilde+E0,K, and the endpoint is
P_tau(N_tilde+E0,K)f'(N_tilde). The cutoff zero-point term cannot
silently be dropped from this canonical identity.
The quantum N_q prescription in (M1) is declared normal ordering;
no unique Weyl quantization of nonlinear f(N_cl) is inferred.

J transforms an annihilator b_k with an energy-dependent tau shift
f(N-k)-f(N), on the sectors where it acts. Hence the old local
field is not transported as a bare equal-tau oscillator field.

## M5. Why this is not a full local-field recovery

For the naive bare equal-tau field, vacuum-to-one-particle frequencies
are h_tau(tau,k)-h_tau(tau,0), which grow as k^(3/4).
A Klein-Gordon high-k phase on one nondegenerate common classical
FLRW geometry is linear in k times its conformal-time derivative.
These cannot agree for all k. The claim excluded is that this
specific bare equal-tau field is the usual local field on one
classical FLRW history. No universal no-Hadamard theorem is claimed.

The correctly J-transported field contains energy-dependent time
shifts. Its local physical interpretation, a usable clock apparatus,
full spatial constraints and an unrestricted field Einstein-CTP
solution remain open. Full Fock normality has been established on
this declared slicing; that is a precise advance, not physical unification.
