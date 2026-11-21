# Negative-g recovery: a controlled-tail rejection and a normal large-tail example

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
