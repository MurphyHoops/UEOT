# D. A nonzero normal fixed-clock continuum for the changed action

## D1. Precise model and selected geometry domain

Use ANOMALY_ACTION B3--B4 with g=lambda-n_s/240 nonzero and all
renormalized coefficients independent of the source cutoff. Work on
a fixed compact u chart. In x=(2/3)kappa^(3/2), the selected principal
operator is -d²/dx²+eta/x² with eta>=-1/4 and its Friedrichs form;
the unsplit critical form is kept at eta=-1/4. The unitary change from
L²(dkappa) is f(x)=kappa^(-1/4)f_old(kappa). A_eta in B4 denotes its
transport back to the geometry space.

Let F be the conformal S³ Fock space for n_s fields,
H_exc=sum k N_kr>=0, H_c=H_exc+E_c. Every energy eigenspace is finite
dimensional, and finite-energy sums are dense in F. The full Hilbert
space for THIS nondegenerate construction is L²(R_+,dkappa) tensor F.

For source energy e (including E_c), define the actual geometry block

    H_e(u)=alpha A_eta+[e+d0(u)]/kappa+d1(u)kappa+d3 kappa³.

The real lens and comparison-form proof of the frozen
relational_coupled/ALL_SIGN_EVOLUTION applies with D_osc=0 and without
the old free zero modes. We use it as an abstract verified construction,
not by rerunning its code and not by assuming positive g.

For completeness, in the lens frame take S=(1+H_exc)³ and
Q=D(q_eta) intersect D(y) intersect D(S^(1/2)).
The same scalar Young inequalities control (e+|d0|)/kappa by a small
part of q_eta+y² plus C(1+e)³. Thus

    F(u)=sign(g)H_diag(u)+Lambda S

is uniformly equivalent to q_eta+||y psi||²+<S>, closed and positive,
with common form domain Q and C² form dependence. Source spectral
projections commute with both terms. There is NO source dilation
commutator growing with K. The comparison term Lambda S is not an
added source. The selected snapshot realization and the actual
unitary evolution follow; no common operator-domain claim is needed.

Equivalently, assemble the scalar block unitaries:

    U_infinity(u,v)=direct_sum_e U_e(u,v) tensor I_deg(e).  (D1)

Dense finite-energy sums and unitary bounds give strong continuity,
composition, adjoints and all normal initial states. Finite energy
moments are additional conditions for unbounded observables.

## D2. Exact finite-cutoff compatibility

Let P_K project onto vacuum in all modes k>K; occupations of modes
k<=K are unrestricted. Then P_K increases strongly to I and commutes
with U_infinity. On the embedded finite-K space,

    U_K(u,v)P_K=U_infinity(u,v)P_K                         (D2)

EXACTLY. A finite-mode excitation stops changing as soon as all of its
modes are retained. Extending by the identity on the complement gives

    ||(U_K-U_infinity)psi||<=2||(I-P_K)psi||

uniformly over every clock pair in the chart, and the same for adjoints.
This is an original-u window result in the newly declared representation,
not the predecessor's shrinking-time comparison.

For arbitrary normal rho set p_K=Tr(P_Krho), rho_K=P_Krho P_K/p_K
once p_K>0. Purification gives D_tr(rho_K,rho)<=sqrt(1-p_K).
The EXACT two-time trace-norm error is

 ||U_K(u,i)rho_K U_K(v,i)*-U_infinity(u,i)rho U_infinity(v,i)*||_1
       =||rho_K-rho||_1.                                (D3)

Shared normal reference systems are retained. No moment hypothesis
is needed for this normality result; arbitrary normal Fock states
are not automatically Hadamard or finite-stress.

## D3. Positive physical kernel and a fixed nonzero test

Use R=kappa^(1/2), f=R^-1 and the selected constraint
C=R[-i partial_u+H(u)]R on transported compact/form tests.
The raw propagator is K_raw(u,v)=f U(u,v)f and obeys weighted gluing

    K_raw(u,v) kappa K_raw(v,w)=K_raw(u,w).

Its state kernel is f U(u,i)rho U(v,i)*f, tested where f is unbounded;
R Gamma(u,u) R is normal trace one. The physical test map
T Phi=integral U(i,u)f Phi(u)du annihilates the constraint test
complex and gives the positive form <T Phi,rho T Psi>.

It is genuinely nonzero on FIXED tests. Choose a compact smooth
finite-source vector psi with q=<psi,rho psi>>0. Strong continuity
provides a fixed interval near i with
sup||U(i,u)psi-psi||<sqrt(q)/2. Pick a nonnegative fixed smooth bump
chi there, integral chi=1, and Phi(u)=chi(u)Rpsi. Then
||T Phi-psi||<sqrt(q)/2 and ||rho^(1/2)T Phi||>sqrt(q)/2.
Consequently the physical norm is greater than q/4.
No inverse propagator is hidden in the test.

## D4. Actual bounded instruments and limits of the claim

Fixed bounded Kraus instruments acting on geometry and finitely many
source modes preserve P_K once these modes are included. Complete
multi-time records are then exactly cutoff-compatible, and their
trace-distance error is bounded by that of the initial normal states.
All failure records and references must remain.

General bounded effects can be strongly compressed, but arbitrary
compressed Kraus families require a missing-probability completion.
Unbounded field stress and all local spatial constraints need their
own domains and estimates. The finite-dimensional numerical regression
in the checker verifies the algebra/normality identities, not this
infinite-dimensional theorem.

This is a positive Hilbert norm, normal density and nonzero kernel
for an explicitly CHANGED renormalized homogeneous action. It does
not make the total generator semibounded; see ENERGY_STABILITY.
It does not prove a full four-dimensional Einstein--CTP theory.
