# AE. Complete resource, backaction and full-source state accounting

## AE1. Exact clock and complete pre-readout total energy

For chi(y)=u(y+2) and q=y+1/2=z-3/2,
<p_y^2>=12, <p_y^4>=504,
<q^2>=45/44, <q^4>=2603/2288,
Re<p_y^2 chi,q^2 chi>=12.
These are quadratic expressions on the H2 packet; D(h_R^2) is not asserted.
They yield for arbitrary m and Omega
E_R=6/m+45mOmega^2/88,
Var_R=90/m^2-3Omega^2/22+577m^2Omega^4/25168.
For AD's m=1, Omega=2pi,
E_R=6+45pi^2/22,
Var_R=90-6pi^2/11+577pi^4/1573.                         (AE1)

The independent initial LO has mean and variance B^2=10^8.
Since W_R=I on the initial clock support, the FULL H_ext mean and variance
are exactly
E_ext=(1.25*10^13+1.46)+10^8+E_R,
Var_ext=(4.8*10^13+2.804)+10^8+Var_R.                  (AE2)
The same full Hamiltonian conserves the entire spectral distribution
during its autonomous unitary evolution. The controller, oscillator
clock, LO, all fields and transformed interaction are all included.
These resources are model quantities, not SI laboratory estimates.

## AE2. The final register projection: finite mean cost, not an assumed zero

At T=1/2 the clock is entirely on F=1. In the W_R^dagger frame the
physical projections have, on this endpoint state, the form
A_j^out=U^dagger P_j U, independent of y.
They commute with h_R. Thus the nonselective endpoint projection preserves
the ENTIRE covariant-clock energy law for this preparation.
This is an endpoint-state statement, not [P_j,H_ext]=0 on all states.

A_j^out also commute with Ntot, the source free terms, high modes,
x, p_x and the counterterm potential. Only the low interaction can change.
Let Q_U=U q_p U^dagger and Z_R=P_0-P_1.
For the pinching map D_R,
D_R(Q_U)-Q_U=(Z_R Q_U Z_R-Q_U)/2.
Since Q_U^2<=2Ntot+1 as a form and Z_R commutes with Ntot,
||(D_R(Q_U)-Q_U)Omega_state||
 <=sqrt(<2Ntot+1>).
The mean-energy difference obeys
|Delta E_ext| <=r_* sqrt(<q_s^2>) sqrt(<2Ntot+1>).       (AE3)

There is a small bound on actual low energy independent of the enormous
controller kinetic mean. Set Klow=N_s+N_p+1. On actual finite cutoffs,
i[H_M,Klow]=-r(x)(p_s q_p+q_s p_p).
The absolute quadratic-form expectation is <=r_*<Klow>.
Energy-form regularization and Gronwall give
<Klow>_t <=(3/2)exp(r_* t).
The estimates pass to the actual full model by the same positive-form
lower-bound argument; they concern ACTUAL low moments, not just the
reference Gaussian comparison. Therefore at T=1/2
<q_s^2><=3 exp(.1),
<N_p><=(3/2)exp(.1)-1.
Ntot adds the actual LO mean B^2. Substitution into (AE3) proves
|Delta E_ext|<5200.                                    (AE4)

The endpoint operators A_j commute with p_x and the high-mode field terms,
preserve the Ntot form and leave source quadratures untouched. The stable
low quadratic form is bounded by these same source/probe number forms.
Together with the unchanged clock this proves preservation of the full
sum-form domain. Thus the register projection preserves the closed form domain. This finite
MEAN backaction bound neither asserts that the actual energy change is
strictly nonzero nor that it vanishes. A second total-energy moment after
this projection is not proved here. The physical mechanism for that final
projection and its own source remains a subsequent gate.

## AE3. Do not transfer the Gaussian-reader energy formula to this reader

For comparison, AB's original mathematical Gaussian P reader is a different
complete instrument. Its nonselective channel averages exp(-i lambda P)
with Var(lambda)=v=1/(4sigma^2). The exact full-H form identity is
V_lambda^dagger H_M V_lambda=H_M+lambda Zf+lambda^2/2,
Zf=q_p+r(x)q_s.
Thus Delta<H_M>=v/2, and for inputs with finite second H_M spectral moment
Var_out(H_M)=Var_in(H_M)+v<Zf^2>+v^2/2.                 (AE5)
No HZf or ZfH domain product is used: expand the squared norm and average
the odd powers of lambda to zero.

Using the actual Klow bound,
<Zf^2><=3(1+r_*^2)exp(.1).
For sigma=.1, the mean increase is 12.5, and the variance increase lies
between 312.5 and 312.5+78exp(.1).
These are the Gaussian P reader's formulas. AD's coherent LO/memory
instrument instead has (AE2)--(AE4); its kappa score is not an application
of that Gaussian quantum channel.

## AE4. A separate high-mode calculation completes the full-source bound

AB's sqrt(3)/50 disturbance estimate only controls source k=1.
For the REFERENCE classical pulse, each k>1 signed mode begins and ends
at zero squeezing. If a_k=r_*/k^2, the total variations of its instantaneous
squeeze parameter are
TV(theta_plus)=log(1+a_k)/2,
TV(theta_minus)=-log(1-a_k)/2.
The Bogoliubov evolution gives |beta_sign|<=sinh(TV(theta_sign)).
After undoing the fixed source/probe rotation, the source occupation is
one half the sum of the two signed occupations. Including degeneracy,
<N_source,>1>_ref
 <= Ctail=[r_*^2/(4(1-r_*^2/16))](pi^2/6-1)<.00647.     (AE6)
This is a reference number bound, not an unbounded-number estimate
inferred for the actual state from a trace-distance estimate.

For any normal state, its vacuum failure probability is bounded by <N>.
Therefore the high-source half trace distance from vacuum is <=sqrt(Ctail).
At each actual finite K, the reference low and high modes factorize,
and AB/AC give the whole vector comparison. Hence
D_half(rho_source,actual(T),rho_source,free(T))
 <=epsilon+sqrt(3)/50+sqrt(Ctail)<.116,                 (AE7)
where the target is the free-evolved k=1 coherent state tensor the entire
high-source vacuum. This inequality passes directly to the actual U_K limit
with the target fixed, without assuming a full reference phase limit.

Both AD's unitary reader and its nonselective register channel act only on
probe/LO/register/clock at the endpoint. They leave the ENTIRE source
marginal exactly unchanged from its post-collision value.
Neither (AE7) nor this locality of a terminal partial trace proves a local
stress, Hadamard error bound or preservation of the complete initial bare
source state.
