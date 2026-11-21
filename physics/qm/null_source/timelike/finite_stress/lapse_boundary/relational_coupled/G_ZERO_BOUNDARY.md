# The g=0 clock boundary: complete finite-mode scattering and normal-state escape

This result concerns the selected finite-K relational quantization, kappa>0,
a fixed eta>=-1/4 and its Friedrichs principal realization. It treats both
one-sided limits of g_K(u)=0. It does not identify a spacetime curvature
singularity, select a different clock, or take the spatial K limit.
The full nonzero-g evolution used here was constructed in ALL_SIGN_EVOLUTION.

## Z1. Exact logarithmic time and a fixed comparison space

Let u_c=-4g_K(0), so g_K(u)=(u-u_c)/4. On either side put
u=u_c+epsilon exp(tau), epsilon=+1 or -1. Then tau tends to minus infinity
at the boundary; the two sides have opposite orientations relative to u.
Use the W-frame and remove only the zero-mode dilation, with reference u_c:
R0(u)=exp[-i(u-u_c)D0]. On every finite tau interval the complete generator is
\[
 H_\tau=2A_\eta+\epsilon e^\tau(V_{\rm diag}(u)+D_{\rm osc}),\qquad
 V_{\rm diag}={H_{\rm osc}+e^{-2(u-u_c)}P_0^2/2+d_0(u)\over\kappa}
              +d_1(u)\kappa+\beta(u)x^2,\quad \beta=9d_3/4.       \tag{Z1}
\]
All coefficients, including V0 a^4 U0 in d0, are retained. Near u_c they
are smooth even though the original 1/g coefficient is singular.
Set lambda0=1+Hosc+P0²/2, S=lambda0³ and
\[
 {\cal Q}=D(q_{\eta,F})\cap D(x)\cap D(S^{1/2}),\quad
 T=q_\eta+X+\langle S\rangle,\quad X=\|x\psi\|^2.              \tag{Z2}
\]
This is the fixed Hilbert rigging Q subset H subset Q*. No strong
transport of the original snapshot domain is assumed.

## Z2. Critical-safe fractional estimates

For N=||psi||² and q=q_eta[psi], the closed ground-state form obeys
\[
 I=\langle\kappa^{-1}\rangle\le5q^{1/3}N^{2/3},\qquad
 J=\langle\kappa^{-2}\rangle\le2\sqrt5\,q^{2/3}N^{1/3}.       \tag{Z3}
\]
Here alpha=1+sqrt(1+4eta)/2>=1 and psi=kappa^alpha f.
For a cutoff chi_R equal to one below R, zero above 2R and
|chi_R'|<=1/R, the ground-state form gives
q[chi_R psi]<=2q+2N/R³ and <kappa>_cut<=2RN.
ORDERING_DOMAIN then gives I<=2 sqrt(RNq)+3N/R.
Choose R=(N/q)^(1/3); the zero-vector case follows by continuity.
On the original form core, integration by parts gives
(alpha-1/2)J<=sqrt(Iq), proving the second bound. Apply the bounds to
differences of form-core approximants and use closedness of multiplication
by kappa^-1 to extend them to the full closed form domain.
This proof includes eta=-1/4 and does not split its form into divergent
positive and negative terms.

Source spectral resolution and Holder yield
\[
 \langle\lambda_0/\kappa\rangle
 \le5q^{1/3}\langle\lambda_0^{3/2}\rangle^{2/3}
 \le(5/3)q+(10/3)\langle S\rangle.                          \tag{Z4}
\]
Also kappa=(3x/2)^(2/3)<=C(1+x²). First fix a compact coefficient
neighborhood [u_c-r,u_c+r]. There are finite C0,C1 depending on that
neighborhood, K and eta such that |Vdiag|<=C0 T and
|partial_u Vdiag|<=C1 T as forms. The oscillator dilation is Q->Q*
bounded. No estimate is claimed uniform in K.

## Z3. A positive comparison with only polynomial loss at past infinity

Put a_tau=(1+tau²)^-1. Choose tau0<min(-1,log r) sufficiently negative
that C0 exp(tau0)(1+tau0²)<=1/4. This fixes constants before choosing
tau0 and avoids a circular interval choice. Define
\[
 F_\tau=H_{{\rm diag},\tau}+a_\tau x^2+2S,\qquad
 H_{{\rm diag},\tau}=2A_\eta+\epsilon e^\tau V_{\rm diag}.
\]
For tau<=tau0,
\[
 {7\over4}q+{3\over4}a_\tau X+{7\over4}\langle S\rangle
 \le F_\tau\le {9\over4}(q+a_\tau X+\langle S\rangle).        \tag{Z5}
\]
Thus F_tau is closed, positive, >=1, with common form domain Q on every
finite tau interval. The 2S shift is solely a comparison operator,
not an extra physical source in Z1.

Let D_x=(xp_x+p_x x)/2. In the inverse-square ground-state form
|<D_x>|<=sqrt(q X), including the critical endpoint. The exact commutator is
\[
 i[H_\tau,F_\tau]=8a_\tau D_x+
    2\epsilon e^\tau i[D_{\rm osc},S]+
    e^{2\tau}\kappa^{-1}i[D_{\rm osc},H_{\rm osc}].           \tag{Z6}
\]
ALL_SIGN_EVOLUTION supplies |i[Dosc,S]|<=72d S and
|i[Dosc,Hosc]|<=2Hosc. Combining Z4--Z6 and
F_tau'=epsilon e^tau Vdiag+e^(2tau) partial_u Vdiag+a_tau' x² gives
\[
 |F_\tau'|+|i[H_\tau,F_\tau]|
 \le\left({8\over|\tau|}+C_*e^\tau(1+\tau^2)\right)F_\tau,
\quad C_*={4\over3}(C_0+C_1)+{80\over9}+192d.                \tag{Z7}
\]
This single absolute bound covers epsilon of either sign.

The commutator holds on the actual D(F_tau^(3/2)) required by the
comparison theorem, not merely a formal test space. Source terms use
the commuting occupation/zero-momentum cutoffs from ALL_SIGN_EVOLUTION.
For the additional x² term use B_R=x²/(1+x²/R):
B_R is bounded on H, maps Q to Q, |B_R'|<=2x, and B_R psi tends to
x² psi in Q* for each psi in Q. Pair with F_tau psi in Q on
D(F_tau^(3/2)); the ground-state derivative formula and dominated
Cauchy--Schwarz pass the bounded commutator to the limit.
No claim that compact/Schwartz functions form an operator core is needed.

Apply the same abstract comparison theorem as ALL_SIGN_EVOLUTION
on each finite interval, or its bounded-resolvent energy proof with the
pointwise coefficient in Z7. Uniqueness identifies the propagator
with the already constructed full one. Gronwall gives
\[
 \langle F_\tau\rangle_{\psi_\tau}
 \le\langle F_{\tau_0}\rangle_{\psi_{\tau_0}}
 (|\tau|/|\tau_0|)^8
 \exp\{C_*e^{\tau_0}(\tau_0^2-2\tau_0+3)\}.
\]
Since T<=C(1+tau²)F_tau,
\[
 \|\psi_\tau\|_{\cal Q}\le C(1+|\tau|)^5\|\psi_{\tau_0}\|_{\cal Q}.
                                                               \tag{Z8}
\]
Here the exponent 8 is justified by a separate sharp energy argument,
not by reading a sharper constant into the abstract theorem's displayed
norm estimate. Let J_R=(I+F_tau/R)^-1 and F_R=F_tau J_R.
F_R preserves Q and is C1 there; F_R'=J_R F_tau' J_R is bounded on H.
For psi in Q, J_R psi belongs to D(F_tau^(3/2)), and F_tau J_R psi
belongs to Q. The symmetric-form identity
i[H_tau,F_R]=J_R i[H_tau,F_tau]J_R follows by writing
psi=J_R psi+F_tau J_R psi/R; the extra two symmetric terms cancel.
It assumes no strong product H F. Lions' product rule for the already
constructed C(Q) intersect C1(Q*) trajectory therefore gives
|partial_tau <F_R>|<=f_tau <F_tau J_R^2><=f_tau <F_R>,
where f_tau is the right-hand coefficient in Z7. Integrate and pass
R to infinity monotonically. This proves the stated energy Gronwall
and hence the powers 8,5,6 without a circular existence argument.

The estimate proves a polynomial past bound. It does not claim a
uniform energy bound at the boundary.

## Z4. Forward Cook limit without a snapshot-domain assumption

Write Z(t)=exp(-2it A_eta). In x variables the Friedrichs A_eta is the
homogeneous inverse-square operator with nu=sqrt(1+4eta)/3>=0.
The Hankel transform in the primary source listed in REFERENCES is
unitary and diagonalizes A_eta as multiplication by k².
Take a dense set of geometry packets with smooth spectral support
compactly contained in k>0, finite oscillator occupations and smooth
compact zero-mode momentum support. They lie in Q.

For such a geometry packet with spectral profile f,
\[
 A_{\nu,k}(e^{-2itk^2}f)=e^{-2itk^2}
 [A_{\nu,k}f+8itk f'+4itf+16t^2k^2f].                       \tag{Z9}
\]
Therefore ||x² Z(t)psi||<=C(1+t²). Z3 bounds
||kappa^-1 Z(t)psi|| uniformly; the source norms of Hosc,P0²,Dosc
are finite on the chosen source vectors. Hence
\[
 \|(V_{\rm diag}(u(\tau))+D_{\rm osc})
          Z(\tau-\tau_0)\psi\|\le C(1+\tau^2).
\]
The product with exp(tau) is integrable at minus infinity.
The weak equation in Q* gives the H-valued Duhamel identity by Lions
pairing with Q solutions and density, since this residual is H-valued.
It does not require that the free curve belong to a strong domain of
the original R5 snapshot.
Thus
\[
 \Omega_-=\mathop{\rm s-lim}_{\tau\to-\infty}
 U_z(\tau_0,\tau)Z(\tau-\tau_0)                              \tag{Z10}
\]
exists first on this dense set and then on all H as an isometry.

## Z5. Reverse limit and completeness

The free group preserves q and S and satisfies
||x Z(t)psi||<=||x psi||+4|t|sqrt(q).
One proves this on the Hankel packets and extends in the joint form norm;
it also holds at the critical endpoint. Consequently
||Z(t)||_(Q->Q) and ||Z(t)||_(Q*->Q*) are <=6(1+|t|).

For initial psi0 in Q put
z_tau=Z(tau0-tau)U_z(tau,tau0)psi0.
Lions pairing cancels 2A and shows
\[
 z_\tau'=-i\epsilon e^\tau Z(\tau_0-\tau)
 (V_{\rm diag}(u(\tau))+D_{\rm osc})\psi_\tau\quad\hbox{in }Q^*.
\]
Z8 gives ||z_tau||_Q<=C(1+|tau|)^6 and
||z_tau'||_Q*<=C exp(tau)(1+|tau|)^6.
For any two times in [-n-1,-n], their difference has Q norm <=C n^6
and Q* norm <=C exp(-n)n^6. The rigging interpolation inequality gives
\[
 \|z_\tau-z_\sigma\|_H\le C e^{-n/2}n^6.                    \tag{Z11}
\]
This is summable in n. It proves the reverse strong limit on Q and
then on all H by density and the unitary norm bound. At finite tau
the two operator families in the forward and reverse limits are
mutual inverses. Both strong limits exist, so their products converge
strongly to the identity. Therefore Omega_- is onto and unitary.
This argument removes the earlier possible restriction to a proper
Cook scattering subspace.

## Z6. Exact consequence for normal physical slices

Since R0(u)->I strongly at u_c and commutes with Z, every initial vector
in the original W-frame has a unique asymptotic vector zeta_- with
\[
 \|\chi(u_c+\epsilon e^\tau)-W Z(\tau-\tau_0)\zeta_-\|\to0.
                                                               \tag{Z12}
\]
The Hankel representation gives local decay
1_{kappa<=R} Z(t)->0 strongly as |t|->infinity for every finite R.
It follows either by nonstationary phase on the spectral packets and
density, or by the stated local-decay result in the same primary source.
W and R0 commute with kappa projections. Hence for **every normalized
normal initial density operator**,
\[
 \lim_{u\to u_c^\epsilon}
 {\rm Tr}\{\rho_u\,1_{\kappa\le R}\}=0\quad(R<\infty).         \tag{Z13}
\]
The extension from pure states uses the positive trace-class spectral
decomposition and dominated convergence. In particular every positive
kappa^p moment tends to infinity in the extended sense. No normalized
vector has an H strong limit, and no normalized normal density has a
trace-norm normal limit on this same slice Hilbert space: such a limit
would assign zero probability to every 1_{kappa<=R}, whose increasing
limit is the identity.

The phase-corrected scattering chart does have a unitary asymptotic
limit. Gluing the two sides through those charts would require an
additional boundary identification; it is not selected here by the
original action. Z13 concerns the chosen u-clock, positive-kappa sector,
finite K and Friedrichs family. It is not a curvature-singularity
theorem, a rejection of all clocks or quantum theories, a statement
about the full field, or an instability inside the old short quiet
window. The explicit K=65536 and 131072 boundaries lie outside that
declared quiet u-window.

## Verification scope

The companion script checks the clock factor, Hankel product rule,
fractional-cutoff balance, polynomial energy exponents, comparison
constants and finite-window boundary location. The closed-form,
commutator-domain, scattering-completeness and trace-class arguments
are analytic proofs reviewed separately, not consequences of the
script returning PASS.


### Cutoff dependence of the g=0 location

The original coefficient can be written exactly as
\[
 g_K(a)={1\over4}\{\log(a/2)+\gamma-H_K+19/30\}.
\]
Thus its zero occurs at
\[
 a_c(K)=2\exp(H_K-\gamma-19/30),\qquad
 {a_c(K)\over K}\longrightarrow 2e^{-19/30}.
\]
The reference A cancels. Equivalently u_c(K)=H_K-C_0/30 tends to
positive infinity at fixed A, and K/a_c(K) tends to e^(19/30)/2 in model
units. This bare-cutoff boundary is not a cutoff-independent physical
critical scale. The combined source/counterterm continuum problem
remains the separate CUTOFF_GATE requirement.
