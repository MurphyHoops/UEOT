# Geometric recovery, normal examples and an exact fixed-source history obstruction

This returns to the actual old-source recovery question. The branch is
the actual K=131072 member of the same homogeneous action, fixed
incoming thin source, fixed nonzero U0 and quiet finite slice.
Both results use the original pure geometric momentum Pi_g, not the
coordinate-shifted bulk P_u or an independent pointer reading.

## N1. The actual raw source cube is finite and explicitly bounded

In the original phi variables, the raw conformal source Hamiltonian is
Hraw= T_A^\dagger H0 T_A, independent of the quantum kappa coordinate.
In the bulk representation this same observable is W H0 W^\dagger;
one must not replace it by the bulk bare H0.

The frozen ACTUAL_INVERSE I3/I5 bounds apply to the quiet history:
|F_k|<=2, |F_k'|<=4 mu_J/omega_k<1, |h_i|<1, omega_k>=sqrt3.
For v_k=e^(-i omega eta)F_k/sqrt(2omega) and
r_k=v_k'-h_i v_k they give
|v_k|<=2/sqrt(2omega) and |r_k|<4omega/sqrt(2omega).
Consequently each real oscillator contributes
\[
 H_r=\alpha_r(N_r+1/2)+
                (\beta_r a_r^2+\overline\beta_r a_r^{\dagger2})/2,
\quad \alpha_r=|r_k|^2+\omega_k^2|v_k|^2<10\omega_k\le10K,
\quad |\beta_r|\le\alpha_r.                                \tag{N1}
\]
This is the actual transported mode state; no static covariance is
substituted at the nonstatic slice.

On the thin zero-mode annuli e(P)=P²/(2A³)<2e6 and A<1e5, so the
zero raw conformal energy A e(P)<1e12. The incoming oscillator support
has total occupation <=2, including the correlated NOON branch; all
higher modes are vacuum. Each Hraw application raises occupation by
at most two and preserves the zero-momentum annulus.
For d=2 sum_(k=2)^K k²=1501217055703038, triangle bounds give
\[
 \|H_{\rm raw}\psi\|\le M_n\|\psi\|,\quad
 M_n=10^{12}+10K[n+d(n+3/2)]\quad\hbox{on occupation }\le n.
\]
Therefore, on every source support vector and hence on the rank-two density,
\[
 L_3=\operatorname{Tr}\rho_{\phi,\rm old}H_{\rm raw}^3
 \le M_6 M_4 M_2<10^{69}<e^{160}.                          \tag{N2}
\]
The proof uses actual successive domains, not the invalid implication
H<=C H_in implies H³<=C³ H_in³. It keeps the entire finite-K vacuum.
Zero/shell correlations do not invalidate the support estimate.
The occupation support is stated in the incoming annihilation basis,
after pulling the actual raw Hamiltonian back to that basis. The finite-
slice sigma-prime used below is generally squeezed in the instantaneous
H0 basis; it is not asserted to have occupation at most two there.

Any normal joint slice state with this complete original-phi source
marginal has exactly this source cube, even if source and geometry are
correlated. N2 is not a renormalized continuum stress cumulant.
In particular, the source-only gate defined using the prescribed
h_i momentum A(p-h_i q) is not automatically covered: at quantum
kappa!=h_i it changes the true raw A(p-kappa q). Its joint raw cube
would have to be recomputed. Neither N3 nor the positive example below
uses that gate.


## N2. Recheck the pure geometric target at this larger K

SOURCE_BUDGETS had a different numerical K range. Here we separately
verify H_K<13, |B_K|<1e10 and C<400 at K=131072.
The same frozen quiet epsilon<exp(-1158) gives
|kappa|,|chi_acc|,|D chi_acc|<=epsilon, |V|<2epsilon,
|D V|<3epsilon. Directly from ACTION_LIFT L5,
|D P_kappa,ct|<14epsilon and |P_u,ct|<3e10 epsilon.
The pure gravitational term is <6e11 epsilon. Thus
\[
 |\Pi_{g,\rm ref}|<6.3\,10^{11}e^{-1158}<e^{-1130}<1.        \tag{N3}
\]
This does not silently extend the old K<=100000 table.
The actual old h is positive and h<exp(-19980).

## N3. Reject recovery with the old raw source and controlled geometry tails

GEOMETRIC_MOMENTUM G8 gives, in its declared combined-budget and
legitimate G-mean domain, the necessary condition
\[
 1.15\,T_3+0.02\,L_3>h^{-3},\qquad T_3=\langle\kappa^3\rangle,
                                                                  \tag{N4}
\]
if <kappa>=h and the pure geometric momentum matches the old budget.
For the unchanged actual raw source, N2 and T3<=2h³ make the left side
times h³ smaller than
2.3 exp(-119880)+0.02 exp(-59780)<1, a contradiction.
Thus this controlled-tail recovery is rejected for every allowed
normal mixed or entangled joint state, not just a product ansatz.
The restriction to the stated domains and T3 budget is essential.

## N4. Once the tail budget is relaxed, construct a normal state that matches

The exclusion is not extended to all negative-g states. Here is an
explicit positive contrast that keeps the original raw source exactly.

Choose an even real normalized Cc∞ bump b on (-1,1) with
J=integral |b'|²<200. For example normalize
exp[-x²/(1-x²)]; its L² norm squared is at least exp(-2/3), and the
unnormalized derivative is bounded by 8/e. Thus its normalized
derivative is <10, proving the claimed J bound.

Let f_s(y) be this bump centered at 1/2 with width 1/8, and f_l(y)
centered at 1 with width 1/10. For the selected fixed eta>=-1/4 define
q_s=q_eta[f_s], q_l=q_eta[f_l],
i_s=<y^-1>_s, i_l=<y^-1>_l, t_s=<y³>_s, t_l=<y³>_l.
Then
q_s>=8 alpha_eta², q_l>=alpha_eta², i_s<3, i_l<2,
t_s<1 and 1<=t_l<2.
The direct core expression
q_eta[f]=integral y^-1|f'|²+(eta-3/4)y^-3|f|² gives
\[
 q_s\le(512/3)J+(512/27)|\eta-3/4|,\quad
 q_l\le(1000/9)J+(1000/729)|\eta-3/4|.
\]
Set Q_eta=60000+21|eta-3/4|>q_s+q_l+1.

Let psi_s(kappa)=h^-1/2 f_s(kappa/h) and
psi_R(kappa)=R^-1/2 f_l(kappa/R), R>=1. Their supports are disjoint.
Put w=h/(2R-h) and take the **pure** geometric vector
psi_geo=sqrt(1-w)psi_s+sqrt(w)psi_R.
Its mean kappa is exactly h. Set
sigma'=T_A rho_phi,old T_A^\dagger and
rho_W=|psi_geo><psi_geo| tensor sigma', then rho_bulk=W rho_W W^\dagger.
The raw-phi source marginal is exactly rho_phi,old.
The total joint density has rank at most two and is normal. Each
source support vector is Schwartz; each geometric packet is compactly
supported away from zero. These are actual common-test-domain states
of the selected snapshot realization, so the following means are
legitimate spectral means, not just formal cancellations.

Write b0=1/(2|g|), D=Tr sigma'H0+d0 and E_target=-Pi_g,ref.
Every source and scalar term, including V0 A^4 U0, is present:
\[
 G_s=-b_0q_s/h^3+D i_s/h+d_1h/2+d_3t_s h^3,
\]
\[
 G_R=-b_0q_l/R^3+D i_l/R+d_1R+d_3t_l R^3,\qquad
 F(R)=(1-w)G_s+wG_R.                                      \tag{N5}
\]
All cross terms between the two packets vanish because G is a local
differential/multiplication operator and their supports are disjoint.
No added source state or shift of the action is used.

The verified actual coefficients obey
3<b0<4, .14<d3<1, 0<d1<exp(30), |D|<exp(60).
They imply G_s<-20h^-3 and F(1)<-1<E_target.
For the finite
\[
 R_{\rm up}=10\sqrt{Q_\eta}\,h^{-2}
\]
the bounds h/(2R)<w<h/R give
\[
 F(R)\ge-4q_s h^{-3}-3e^{60}h^{-1}
             +.07hR^2-2e^{60}h/R^2-4q_lh/R^4.
\]
At R_up the right side times h³ is greater than
7Q_eta-4q_s-3e60 h²-.02 e60 h^8/Q_eta-.0004 q_l h^12/Q_eta²>2.
Thus F(R_up)>1>E_target. Continuity gives at least one finite
R_* in (1,R_up) with F(R_*)=E_target; the least root in this compact
bracket is one definite once-selected choice. No numerical ODE,
time-dependent reselection or uniqueness claim is involved.

The resulting normal physical slice matches
<kappa>=h and <Pi_g>=Pi_g,ref while preserving the complete old raw
source marginal. ALL_SIGN_EVOLUTION supplies its subsequent weak
unitary history. This is a precise finite-mode positive example.

## N5. The cost explains why it does not recover the old semiclassical history

N4 and the unchanged N2 force the root state to have
\[
 T_3>\tfrac12 h^{-3},\qquad
 R_*>\tfrac13 h^{-2},\qquad
 \operatorname{Var}(\kappa)>\tfrac1{12}h^{-1}.               \tag{N6}
\]
For example T3<=h³+2hR² gives the R bound; the far-packet contribution
to <kappa²> is at least hR/2 and the old h is extremely small.
Consequently Var(kappa)/h²>1/(12h³). The rare far tail carries enormous
higher moments despite the tiny mean. Omitting that branch would
destroy the exact matched expectation.

N5 does not reproduce the old mean Einstein trajectory, all higher
geometric moments, a controlled fluctuation expansion or an actual
autonomous preparation. It solves the declared homogeneous quantum
constraint through its physical-slice evolution and matches those
initial means only. Pi_g on the constrained slice is -G and includes
the source Hraw/kappa; it is not an independent tensor-factor record
of the type excluded by the earlier fixed-marginal extension theorem.

The physical lesson is now explicit: this negative branch permits a
normal correlated constraint state with the desired initial means,
but the fixed old source and a narrow geometric state cannot supply
them together in the declared quantization. A physical replacement
must address the tail/state/domain costs and the subsequent common
history, not just tune two means.


## N6. Reflection and one additional initial geometric derivative

The real two-packet construction has a limitation that can be computed:
its initial derivative of the mean expansion with respect to u is zero,
whereas the prescribed history requires h'_eta/h. Here prime_eta denotes
the original conformal derivative, not differentiation with respect to u.

This derivative is legitimate in the weak-energy evolution. In the
W/R0 representation use B_R=kappa/(1+kappa/R). It preserves the common
form domain: the ground-state product rule and |B_R'|<=1 give
q_eta[B_R psi]<=2R²q_eta[psi]+2<kappa^-1>.
The commutator form is bounded uniformly in R by
2|alpha|sqrt(q_eta I), I=<kappa^-1>, alpha=1/(2g).
Apply the Lions integrated Ehrenfest identity, then dominated convergence
on a compact u interval using continuity in the common form norm.
The result is a continuously differentiable mean
\[
 {d\langle\kappa\rangle\over du}
     ={1\over g}\langle\kappa^{-1/2}P_\kappa\kappa^{-1/2}\rangle .
                                                               \tag{N7}
\]
This does not assume the unresolved strong-domain transport of the
original raw Hrel.

Multiply the once-selected real packet profile by exp(i b kappa²/2).
Its current in N6 is b, its q_eta increases by b²h, and its mean kappa
and complete original-phi source marginal are unchanged.
Choose once
\[
 b=g\,h'_\eta/h .
\]
Then the initial derivative equals the old h'_eta/h exactly.
The G expectation shifts by -b²h/(2|g|), independently of R.
The same continuity bracket therefore fixes one new R_*; at R_up the
extra negative term after multiplication by h³ is
|g|(h'_eta)²h²/2, below the previous strict margin by the frozen bounds.
The lower bracket remains negative.

Thus the initial expansion mean, pure geometric momentum mean and this
one initial expansion derivative can all be matched in a normal joint
state with the exact old raw source. The enormous third moment and
variance bounds still apply. This is not recovery of the old positive-
time history: the canonical P_kappa includes, among other terms,
-H_K<kappa²>/4, whose large-tail value has not been matched, and the
remaining geometric jets and state preparation still require a proof.


## N7. A bounded source record rejects this candidate's full old source history

Matching the preceding three geometric data still does not reproduce
the old complete raw source evolution. This can be tested directly,
without using the large variance as a proxy for history mismatch.

Let D0=sum_j{phi_j,P_j}/2 be the original two-zero-mode dilation and
V_s=exp(i s D0). It is bounded and unitary, and
\[
 V_sP^2V_s^\dagger=e^{-2s}P^2,\qquad
 [P^2,V_s]=(1-e^{-2s})P^2V_s .
\]
Under the raw-phi, W, R0 and T_a identifications this is the same
observable: the extra matter transformations are dilations commuting
with D0, and the remaining phase is geometric. V_s and its adjoint
preserve the common weak-energy form domain: zero momentum only scales
by a finite constant, so lambda0³ remains equivalent, while the
geometric form is unchanged. The commutator form is controlled by the
existing lambda0/kappa estimate. The Lions pairing therefore supplies
a continuously differentiable bounded-record expectation. It does not
require strong-domain transport of the unbounded D0.

The original raw-phi initial state of N4/N6 is a geometry/source product,
with exactly the old raw source density sigma. Define
I=<kappa^-1> and M_s=Tr(sigma P²V_s). The zero-mode part of the original
u-clock Hamiltonian is P²/(2a² kappa). All its other terms commute
with V_s, so at the common initial a=A,
\[
 F_{\rm joint}'(0)={i(1-e^{-2s})\over2A^2}\,I M_s,\qquad
 F_{\rm old}'(0)={i(1-e^{-2s})\over2A^2h}\,M_s .             \tag{N8}
\]
Prime here means the u derivative. The second formula is the actual
prescribed old source history, with du/deta=h. There is no resetting
of source annuli or replacement of h by an independently selected value.

The source support vectors are Schwartz, so M_s tends to
M0=Tr(sigma P²)>0 as s tends to zero. One can specify a nonzero witness:
for the actual spectral decomposition sigma=sum_j p_j|psi_j><psi_j|,
let C=sum_j p_j||P²psi_j|| ||D0psi_j||<infinity.
Then |M_s-M0|<=|s|C. Any
0<s<min{1,M0/[2(C+M0)]} has Re M_s>M0/2.
The bounded self-adjoint source observable sin(sD0) consequently has
a strictly different initial derivative in the two histories.

For the two geometric packets Jensen's inequality gives exactly
\[
 I\ge(1-w){2\over h}+{w\over R}
       ={2\over h}-{1\over R}>{1\over h}.                  \tag{N9}
\]
The quadratic phase in N6 does not change this inverse moment or the
raw source factorization. Thus N8 differs for every once-selected
root in this family. These normal candidates cannot reproduce the old
complete raw-source history on any positive interval starting at the
matched slice, even after the initial expansion derivative is repaired.

This rejects this specific preparation family as a full-history
recovery. It does not reject all normal entangled extensions with that
source marginal. The bounded witness is not by itself proof that each
mean-RSET component differs, and it is not a calibrated physical
instrument; an apparatus action and its stress are still absent.


## N8. Exact fixed-source first-jet obstruction for every allowed joint extension

The preceding product-state rejection can be strengthened using the
actual source support. Fix any finite K, a nonzero-g u-clock patch,
positive kappa, the declared eta>=-1/4 Friedrichs choice, and a normal
joint physical-slice density with finite common comparison-form energy.
Require its complete original-phi source marginal to be the current
rho_phi,old and <kappa>=h>0 at a=A. Arbitrary geometry/source entanglement
is allowed. This uses the physical-slice density with its already
derived raw-variable transport, not a flat kinematic zero eigenvector.

### The actual bounded source observable

Set E=(P1²+P2²)/(2A³). The two-dimensional radial measure is
r dr=A³ dE. Absorb this constant into the radial unitary identification.
The actual source support vectors have the form
\[
 \psi_N(E,\theta,\mathrm{osc})
 =\sigma^{-1/2}w((E-e_N)/\sigma)
       e^{i\Theta E+i\gamma_N}u_0(\theta)\xi_N,\quad N=0,2.
 \tag{N10}
\]
BOUNDARY_STATE (67),(68) fix w and the centers once. Common finite-slice
transport gives the same real phase slope Theta=-A³ I_i in both
branches; the transported oscillator vectors xi_0,xi_2 remain orthogonal.
Let P_M project onto their rank-two span. The old zero/shell correlation
and the branch probabilities are retained.

Choose a real Cc-infinity vector field v(E) on (0,infinity), equal to one
on [e2-2sigma,e0+2sigma] and zero near zero and infinity. That interval
is positive for the actual frozen input. Its complete flow Phi_s defines
a unitary on the same radial source Hilbert space,
\[
 (V_s f)(E)=\sqrt{\partial_E\Phi_{-s}(E)}\,f(\Phi_{-s}(E)).
\]
For 0<s<sigma the two source supports and their shifted images stay in
the unit-speed region, so V_s psi_N(E)=psi_N(E-s). This is a bounded
observable construction, not a physical gate or an everywhere
self-adjoint variable conjugate to a semibounded energy.

Define j(s)=integral w(z)w(z-s/sigma)dz. The actual bump is positive on
(-1,1), so j(s)>0 for 0<s<sigma. Orthogonality of xi_0,xi_2 and the common
phase give
\[
 P_MV_sP_M=e^{-i\Theta s}j(s)P_M.
\]
At the initial slice the original raw conformal source Hamiltonian is
Hraw=A E+Hosc. It commutes with V_s in the oscillator part, and
[E,V_s]psi_N=s V_spsi_N. Thus the self-adjoint bounded record
\[
 B_s={e^{i\Theta s}V_s-e^{-i\Theta s}V_s^\dagger\over2i},
 \qquad\|B_s\|\le1
\]
satisfies the exact compression
\[
       P_M\,i[H_{\rm raw},B_s]\,P_M
                  =A s j(s)P_M=:c_sP_M,\qquad c_s>0.       \tag{N11}
\]
Fix s=sigma/2 once. For the displayed normalized bump, an optional
explicit bound follows on z in [0,1/2]:
j(sigma/2)>=w(1/2)²/2>=exp(-2/3)/4>0.
Normalization cancels the overall exp(-1) in the original bump.

The global flow has bounded energy displacement, hence preserves all
fixed zero-energy polynomial weights and lambda0³ up to finite
equivalence. It commutes with the geometry and nonzero oscillators.
The T_a and zero-mode R0 dilations cancel in the original Noether
momenta, leaving fixed reference momenta in the W/R0 representation.
Consequently this observable is constant in that representation;
there is no omitted time-dependent-observable term.
B_s preserves the common form domain and its form commutator is
controlled by the existing source-energy/kappa and inverse-kappa
bounds. The Lions product rule gives a genuine C1 expectation,
including for normal densities of finite comparison-form energy.
One does not assume transport of an unbounded Q0 domain or of the
original raw Hamiltonian's strong operator domain.

### Joint entanglement cannot remove this particular initial discrepancy

Positivity and the exact source marginal imply
rho=(I tensor P_M)rho(I tensor P_M). Every non-source term of the
original u-clock Hamiltonian commutes with B_s. The source term is
Hraw/kappa, so N11 gives for every such joint state
\[
 {d\langle B_s\rangle_{\rm joint}\over du}\bigg|_i=c_s I,
 \quad I=\langle\kappa^{-1}\rangle .
\]
The actual old prescribed source, with the same u and du/deta=h,
instead gives c_s/h. The finite-form hypothesis makes I finite.
Using <kappa>=h,
\[
 I-{1\over h}={\langle(\kappa-h)^2/\kappa\rangle\over h^2}>0,
 \qquad
 {\partial_u\langle B_s\rangle_{\rm joint}\over
  \partial_u\langle B_s\rangle_{\rm old}}-1
      =hI-1={\langle(\kappa-h)^2/(h\kappa)\rangle}>0.         \tag{N12}
\]
Strictness follows because a normal geometry marginal on the positive
kappa multiplication representation cannot have support on the
singleton kappa=h. The weighted raw-variable gluing does not create
such a spectral projection.

Therefore the unchanged complete raw source marginal and the old
expansion mean cannot extend to the identical complete old raw-source
history on a positive u interval in this stated quantum class.
This result does not depend on the sign of g or on the two-packet ansatz.
It is a first-derivative obstruction for an actual bounded source
record, derived from the same action and the actual thin-state support.

There is no common positive error floor for all normal states:
narrow normal geometry families may make hI-1 approach zero, subject
to the other geometric momentum and domain/resource conditions.
For N4/N6's two packets, the stronger numerical ratio
hI-1>=1-h/R follows from N9 and is close to one.
The angularly directed rho_g has the same two translated radial
profiles and common phase, so the same conclusion applies if its
complete marginal and its own prescribed-history target are held fixed.

This is not a no-go for physical unification, a changed source
preparation, a different mean-history target, the signed-kappa
matter-clock quantization, or states outside the declared finite-form
contract. It is also not proof that every mean-RSET component differs.
No apparatus implementing B_s has been constructed.


## N9. The underlying obstruction for an arbitrary normal free source

There is a broader structural statement in the same selected model.
It removes the special thin/rank-two assumption but retains positive
kappa, the u-clock, normal physical-slice states, finite comparison-form
energy, finite <kappa>=h, and the original free raw separation
Hrel=H_geometry+Hs(a)/kappa. It addresses equality of the complete
source first jet, not merely mean stress.

Let sigma=Tr_geometry rho. Define the positive trace-class weighted
source density without an unbounded cyclic trace:
\[
 X=(\kappa^{-1/2}\otimes I)\rho^{1/2},\qquad
 \tau=\operatorname{Tr}_{\rm geometry}(XX^\dagger),\qquad
 \operatorname{Tr}\tau=I=\langle\kappa^{-1}\rangle .
 \tag{N13}
\]
Finite I makes X Hilbert--Schmidt. For every bounded source rank-one
O=|f><g| with f,g Schwartz, [Hs,O] extends to a bounded finite-rank
operator. The raw source weak first derivative is
Tr tau i[Hs,O]. Under the W/R0/T_a identification O(u) is a C1
finite-rank family with Schwartz vectors, preserving the common form
domain. Its explicit derivative cancels the source dilation term in
the transformed generator. The Lions product rule thus gives precisely
this raw expression; no assertion that the entire reduced-density
curve is trace-norm C1 is necessary.

If all these source-record derivatives equal evolution of the same
sigma on the prescribed classical history with expansion h, then the
self-adjoint trace-class operator K=tau-sigma/h obeys
\[
             \operatorname{Tr}K\,i[H_s,O]=0
\]
for every such rank-one O. Equivalently,
<g,K Hs f>=<Hs g,Kf> on the Schwartz core.
For fixed core f, the adjoint definition implies Kf belongs to D(Hs)
and HsKf=K Hs f. Graph-core approximation and closedness extend this to
K D(Hs) subset D(Hs), with equality of the two products on D(Hs).
K therefore commutes with every resolvent and the spectral group of Hs.

The original finite-K raw source Hamiltonian has no point spectrum.
Its nonzero-mode oscillator factors have a countable eigenbasis, while
in each such channel the two free zero modes contribute
P_zero²/(2a²); each fixed total energy surface in R²_P has Lebesgue
measure zero. The countable channel sum still has zero eigenprojection
at every energy. Fixed scalar energy shifts do not affect this fact.

A nonzero compact self-adjoint K has a nonzero eigenvalue of finite
multiplicity. Strong commutation would make its finite-dimensional
eigenspace invariant under the Hs spectral group, yielding an Hs
eigenvector. Since Hs has no eigenvectors, K must be zero.
Taking traces in tau=sigma/h gives I=1/h, contradicting strict
Jensen for a normal positive-kappa marginal with mean h.

Thus exact classical full-source-first-jet recovery is impossible in
this free, positive-kappa, finite-form u-clock class even for a changed
normal source and arbitrary joint entanglement. At least one bounded
Schwartz finite-rank source record differs. N8 supplies a concrete
single fixed observable for the actual thin source; N9 is an existence
argument for a general source.

This is not a restriction on all possible quantum gravity dynamics.
It does not cover nonadditive geometry/source or apparatus interactions,
a different clock/normality domain, approximate histories, conditional
records, or the weaker requirement of matching only mean RSET.
The next joint-history object is the actual weighted source tau and
its geometry correlations, not an assumed substitution tau=sigma/<kappa>.
Writing tau=I sigma+Delta, Tr Delta=0, makes the source weak derivative
-i[Hs,tau] explicit. For an initial product Delta=0, the source's initial
clock rate corresponds to 1/I, which is smaller than <kappa>.
A physical approximate or alternative-clock history must calculate
this difference and its resources instead of deleting it.


## N10. Quantitative initial errors and the next reduced-source dynamics

The explicit N8 witness already gives a state-dependent local error.
For trace distance D_tr=(1/2)||rho-sigma||1, ||B_s||<=1 and its C1
expectation imply
\[
 \liminf_{\delta u\downarrow0}
 {D_{\rm tr}(\sigma_{\rm joint}(\delta u),\sigma_{\rm old}(\delta u))
       \over\delta u}
       \ge {c_s\over2}(I-1/h)>0 .                         \tag{N14}
\]
This allows the initial entanglement covered by N8. With the fixed
s=sigma/2 and width sigma=sqrt(3)/(100A),
c_s=sqrt(3)j(sigma/2)/200. There is no state-independent finite-window
or experimental lower bound in N14.

For the actual N4/N6 initial raw product family, one can go further
even if the first derivative is compared using the harmonic clock
rate 1/I instead. Let sigma be the old raw source, Hs=Hraw(A),
I2=<kappa^-2> and J=(dI/du)_i. At the initial slice,
\[
 \sigma'=-iI[H_s,\sigma],\qquad
 \sigma''=-i[I H_s'+JH_s,\sigma]
                  -I_2[H_s,[H_s,\sigma]] .
\]
Both formulas are legitimate here. Each rank-two source support vector
is Schwartz and each geometric packet, including its phase, is smooth
with compact support away from kappa=0. These are in every required
initial common-core product domain. The approximation
psi_app(u)=psi-i delta u H0 psi
+delta u²(-i H0'-H0²)psi/2 has an H-valued residual O(delta u²).
Weak Duhamel and unitarity give norm error O(delta u³).
Partial trace of the finite-rank density then justifies the displayed
second-order expansion without global strong-domain transport.

The purity p(u)=Tr sigma(u)² consequently satisfies
\[
 p''(0)=-2\,\operatorname{Var}(\kappa^{-1})
                         \|[H_s,\sigma]\|_{HS}^2<0 .       \tag{N15}
\]
The inverse-kappa variance is positive for these normal packets.
The commutator is Hilbert--Schmidt and nonzero: otherwise the compact
normal sigma would commute with the point-spectrum-free Hs, contrary
to the argument in N9.

Every closed prescribed-background unitary source history starting
at the same sigma preserves purity, including after a smooth change
of time parameter. This product candidate therefore cannot be repaired
merely by replacing h with 1/I.
For trace-one densities,
|Tr rho²-Tr sigma²|<=2 D_tr(rho,sigma), obtained by pairing rho-sigma
with rho+sigma-I. Hence every such unitary target obeys
\[
 \liminf_{\delta u\downarrow0}{D_{\rm tr}
       (\sigma_{\rm joint}(\delta u),\sigma_{\rm unitary}(\delta u))
             \over(\delta u)^2}
 \ge {1\over2}\operatorname{Var}(\kappa^{-1})
                          \|[H_s,\sigma]\|_{HS}^2>0 .      \tag{N16}
\]
N15/N16 apply to these initial product preparations, not arbitrary
initially entangled joint states. The coefficients are state-dependent
and no common nonzero time radius has been certified. They identify
the actual reduced-source channel and the weighted density tau as
the next objects to evolve, rather than a closed free source on a
prescribed classical geometry. No device calibration follows.
