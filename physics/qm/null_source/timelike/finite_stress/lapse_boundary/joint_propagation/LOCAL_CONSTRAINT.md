# Exact local original-constraint quotient and three distinct completions

## Q1. Fixed finite-K input and endpoint multipliers

Fix one finite K, the selected ordering eta>=-1/4 and its Friedrichs
realization, and a connected bounded clock patch J whose closure avoids
g_K=0. Let H be the bulk slice Hilbert space, Q=W_K Q_sharp the fixed
invariant energy space of ALL_SIGN_EVOLUTION, and U its complete bulk
propagator. Put R=kappa^(1/2), f=kappa^(-1/2),
D=-i partial_u+H_K(u), and C_eta=R D R. At eta=0 this is the original
square-order constraint; another eta is the previously declared ordering.

The accepted evolution preserves Q, has trajectories C(Q) intersect
C^1(Q*), and H_K(u):Q->Q* is symmetric and norm-continuous. U is uniformly
bounded on Q on each compact clock pair. In the W frame write

    r_eta=1+sqrt(1+4eta)/2 >= 1,
    q_eta[x]=integral kappa^-1 ||x'-r_eta x/kappa||^2 d kappa,
    T_3=q_eta+||y x||^2+<lambda^3>, y^2=4kappa^3/9.

At eta=-1/4 keep the entire closed ground-state form: its kinetic and
singular potential pieces must not be split into divergent integrals.
On compact/Schwartz tests, integration by parts and Cauchy--Schwarz give
r_eta I_1<=sqrt(m q_eta), where I_1=<kappa^-1>, m=<kappa>.
Closed-form approximation extends this to Q. Since
kappa<=1+4kappa^3/9 and lambda^3>=1,

    ||R x||^2=m<=T_3,
    ||f x||^2=I_1<=T_3/(2 r_eta).

R and f commute with W_K. They are therefore bounded Q->H in the energy
norm; neither is declared bounded on H. Their multiplication identities
are used only on the actual stated ranges.

## Q2. Adapted tests and the original differential action

Fix u_i in J and set Vq(u)=U(u,u_i)q(u). Define

    F_c=C_c(J;Q),  X_c=V[C_c^1(J;Q)],
    Phi_C=R F_c,  Y_C=f X_c.

Use the transported compact-time Q topologies, not an unstated flat
kinematic topology. These are actual H-valued functions by Q1.
The Q/Q* product rule yields D(Vq)=-iUq', hence

    C_eta(fVq)=-i R U q' in Phi_C.

Cancellation occurs before applying the unbounded R; the resulting
D(Vq) lies in Q. This is the original congruence on a declared test
restriction, not a changed lapse or action.

Define the Q-valued Bochner map

    T_C phi=integral_J U(u_i,u) f phi(u)du.

It is bounded in the transported compact-time norm:
||T_C phi||_Q<=M_J integral ||f phi||_Q du.

## Q3. Exactness and a constructive split

Choose h in C_c^infinity(J) with integral h=1, and let
J_h xi(u)=R U(u,u_i) h(u) xi. Then T_C J_h=I_Q and
T_C C_eta(fVq)=-i integral q'=0.

If T_C phi=0, define

    q(u)=i integral_{u_-}^u U(u_i,s) f phi(s)ds,
    G_C phi=f U(u,u_i)q(u).

The primitive vanishes before the support and after it because the total
integral is zero. Thus q is compactly supported C^1(J;Q), G_C phi lies in
Y_C and C_eta G_C phi=phi. If C_eta(fVq)=0, then q'=0 and compact time
support forces q=0. Consequently the local complex is EXACT:

    0 -> Y_C --C_eta--> Phi_C --T_C--> Q -> 0.

Extend the primitive to G_h phi=G_C(phi-J_hT_Cphi). Then

    C_eta G_h=I-J_hT_C,  G_h C_eta=I,
    T_C J_h=I,          G_h J_h=0.

This compact primitive selects no physical clock-end boundary condition
and is not a global Green operator.

## Q4. Relation to the old tests, symmetry and physical completion

The original compact-time, compact-kappa-away-from-zero, source-Schwartz
smooth tests Phi_0 lie in Phi_C. They also lie in Y_C. For psi in Phi_0,
chi=R psi is regular and Dchi lies in C_c(J;Q), because the actual finite-K
formal expression preserves compact kappa/Schwartz source regularity.
Snapshot agreement was proved in ALL_SIGN_EVOLUTION; no operator-core
claim is used. Pairing with transported Q vectors and mollifying in time
gives the weak interaction-picture identity
q'=i U(u_i,u)Dchi, q=U(u_i,u)chi. Its continuous Q-valued right side makes
q compactly supported C^1(J;Q). Hence psi=fVq is in Y_C with the same
original constraint action. Exactness is not asserted on the smaller
image C_eta Phi_0.

The state-independent form

    eta_C(phi,psi)=<T_Cphi,T_Cpsi>

has nullspace exactly C_eta Y_C. Its quotient completion is H, because
T_C maps onto Q and Q is dense in H. This extends the already accepted
PHYSICAL_SLICE form; positivity alone is not counted as a new result.
Even T_C(Phi_0) is dense: a narrow time bump multiplying R xi, for a
regular slice xi, tends under T_C to xi by strong continuity.

For Psi_j=fUq_j in Y_C,

    integral <Psi_1,C_eta Psi_2>du
        =integral <q_1,-i q_2'>du.

Compact-time integration by parts proves symmetry in L^2(J;H).
Y_C contains the dense old test class, so this restriction is closable.
No self-adjoint global constraint, endpoint condition, graph-core
equality or exactness of an arbitrary graph closure is asserted.
Changing the reference slice replaces T_i by T_j=U(u_j,u_i)T_i.
Nested connected patches identify compact tests by extension by zero;
this does not continue through g_K=0.

## Q5. Three completions that must be kept distinct

1. The state-independent constraint quotient above completes to H.
2. A given normal slice density rho defines
   eta_{C,rho}(phi,psi)=<T_Cphi,rho T_Cpsi>.
   Its VECTOR-test feature space completes via sqrt(rho)T_C to
   supp(rho)H. For pure rho it is one-dimensional.
3. The GNS representation of omega_rho(A)=Tr rho A on B(H) is
   closure{A sqrt(rho)} in Hilbert--Schmidt norm, namely
   S_2(supp(rho)H,H), isomorphic to H tensor conjugate(supp(rho)H).
   If rho e_j=lambda_j e_j, lambda_j>0, the bounded rank-one operator
   A=lambda_j^(-1/2)|x><e_j| gives A sqrt(rho)=|x><e_j|.
   These finite-rank columns are dense. For pure rho this GNS space
   is H, rather than one-dimensional.

The density-dependent vector-kernel nullspace is not preserved by every
bounded A. If x is orthogonal to a pure psi, x is null but
A=|psi><x| sends it to a nonnull vector. The condition is
A ker(rho) subset ker(rho). This is why a density kernel alone cannot
replace the state-independent physical completion.

## Q6. Physical operations and classification of preparations

Every bounded A acts on completed H. If A and A* preserve Q, an explicit
adapted-test lift is L_A=J_h A T_C, with

    T_C L_A=A T_C, L_A L_B=L_AB,
    L_I-I has null range,
    eta_C(L_A phi,psi)=eta_C(phi,L_{A*}psi).

These are quotient and physical-adjoint identities, not kinematic strong
commutation with C_eta. The actual bounded geometry readout
B=kappa^2/(1+kappa^2) has

    c_B^2=sup kappa^-1 |B'|^2=7^(7/2)/1024<1,
    q_eta[Bx]<=2q_eta[x]+2c_B^2||x||^2,
    T_3[Bx]<=4T_3[x].

The closed ground-state product rule proves this even at critical eta.
The finite-prefix coherence projection in BOUNDED_WITNESS needs only
boundedness on completed H, not an unproved Q-preservation property.

A normal physical preparation means a trace-class positive density of
trace one on H. It does not make the raw kernel fU rho U* f trace class
in flat kappa measure, or create a normal kinematic history state.
The raw objects use their declared tests and weighted normalization;
finite expected T_3 supplies extra raw control through Q1.

More generally, every positive form beta annihilating C_eta Y_C and
bounded by M||T_Cphi||||T_Cpsi|| uniquely has the form
<T_Cphi,B T_Cpsi>, with B>=0 bounded on H. Exactness, density and Riesz
prove this. Normal preparations are the trace-class trace-one subclass;
the state-independent flux rigging has B=I. The local constraint fixes
the transport and quotient; it does not choose the preparation.

The executable checks verify the closed-form ordering identity, the
exact B bound, and finite-dimensional distinctions between these
completions. Domain, exactness and completion statements are the
analytic proofs Q1-Q6, not machine formal theorems or a full-K limit.
