# A normal two-mean example, and the source cost that prevents recovery

This is the constructive check after the U_B family was rejected. It changes
the source bare state and uses a different joint state. It matches only
<kappa> and <P_u>; GEOMETRIC_MOMENTUM shows why these are insufficient
for the actual geometric canonical history. The state is a mathematical
physical-slice initial density, not a local autonomous preparation.

## T1. Explicit packets and a finite-rank normal state

Use the same K=65536, g>0,d3>0, eta=0 example; the construction also works
for any fixed eta>=-1/4 once its finite reference expectation is used.
Let b be the real even normalized bump
Z^(-1/2) exp[-1/(1-x²)] on (-1,1), and mu_b2=integral x²b²>0.
Define g_{m,e}(kappa)=e^(-1/2)b((kappa-m)/e).
It is normalized, has mean m and variance e² mu_b2.

Choose gs=g_{h/2,h/8}, gR=g_{R,R/10}, R=1e12,
and w=h/(2R-h), where h is the fixed actual h_i.
Their supports are [3h/8,5h/8] and [.9R,1.1R].
The normal initial density
\[
 \rho_0=[(1-w)|g_s\rangle\langle g_s|+
                    w|g_R\rangle\langle g_R|]\otimes\rho_{S,K}
\]
has <kappa>=h. Each rank-two source branch is finite-K Schwartz, so all
four joint vectors are in the common compact-kappa/Schwartz core.
Its finite E0=Tr rho0 H_eta is >exp(59000) by MEAN_RECOVERY.

This parameter is not an unspecified free energy. For either real
geometry packet g_m, it is the explicit finite integral
\[
 E(g_m)=a q_\eta[g_m]+a\int \frac{|g_m|^2}{\kappa}
    [A_K(\kappa)^2+2A_K(\kappa)\bar Q+q_{2,0}^2]d\kappa
 +( \bar H_0+d_0)I_m+(d_1-\bar Q)m+d_3\langle\kappa^3\rangle_m,
\]
with a=1/(2g), I_m=<1/kappa>_m, and E0=(1-w)E(gs)+wE(gR).
All source moments are from the same frozen finite-slice source.
This gives an analytic parameter specification; no high-mode ODE or
numerical evaluation of these enormous finite integrals is claimed.

## T2. A different source shift with its endpoint phase

For one zero mode set
\[
 T_L=e^{-iL(p_z-hq_z)},\quad V_L=e^{iL^2\kappa/2},\quad U_L=V_LT_L.
\]
Here h is the fixed old mean number, not the operator kappa.
T_L shifts q_z by L and p_z by hL; the geometry phase gives
\[
 U_L^\dagger(P_\kappa-A_K-Q)U_L
                  =(P_\kappa-A_K-Q)-Lq_z.                 \tag{T1}
\]
The parity-even original source makes all linear-L expectation terms vanish.
Thus for the tail product state the complete Hamiltonian changes by L² C_R,
\[
 C_R=a I_R\langle q_z^2\rangle+(h^2 I_R-R)/2 .
\]
I_R<=1/(.9R), <q_z²><2e19, and the actual g>.0377 imply
\[
 -R/2\le C_R<-R/4 .
\]
The ordering eta term is unchanged.

Define
\[
 \rho(L)=(1-w)|g_s\rangle\langle g_s|\otimes\rho_S
       +wU_L(|g_R\rangle\langle g_R|\otimes\rho_S)U_L^\dagger .
\]
It is normal, rank at most four, and all finite-L vectors remain in the
common core. For Htarget=-P_u,ref and Delta=E0-Htarget>0, choose once
\[
 \boxed{L^2=\Delta/(w|C_R|)} .
\]
Then exactly <kappa>=h and <H_eta>=Htarget, hence
<P_u>=P_u,ref at this initial core slice.
These are two means, not all constraint jets, a prepared trajectory or
a mean-history recovery theorem.

The source marginal is (1-w)rhoS+w T_L rhoS T_L†.
Because p-hq=P_in/A, T_L is a scalar phase in incoming zero momentum.
It preserves the predecessor's stated source algebra A_{P,h} on the
**prescribed old h history**, including its nonselective restriction.
The complete source bare state changes. This does not establish unchanged
source stress when the geometry variable is the operator kappa.

## T3. Exact costs, including the actual raw source kinetic energy

The geometry marginal includes the phase-shifted tail packet, but its
kappa distribution is unchanged. The exact variance is
\[
 \operatorname{Var}\kappa=(1-w)(h/8)^2\mu_{b2}
       +w(R/10)^2\mu_{b2}+h(R-h)/2,
 \qquad \operatorname{Var}\kappa/h^2>R/(4h).                 \tag{T2}
\]
Let q2,L²=Tr sigmaS(L) Q². Source parity gives
\[
 \bar Q_L-\bar Q=wL^2/2,\quad
 q_{2,L}^2=q_{2,0}^2+wL^2(\langle q_z^2\rangle+\bar Q)+wL^4/4 .
\]
Consequently
\[
 \Delta/R\le\bar Q_L-\bar Q<2\Delta/R,\qquad
 q_{2,L}>\Delta/\sqrt{Rh}.                                  \tag{T3}
\]
No source-coordinate resource is omitted from the normal-state construction.

More directly, the original action's single-zero-mode proper kinetic energy
on the actual quantum geometry is E_raw,z=(p_z-kappa q_z)²/(2A).
Under U_L, its raw momentum shifts by (h-kappa)L. Parity removes the cross,
so the nonselective energy increase is
\[
 \Delta\langle E_{\mathrm{raw},z}\rangle
 =\frac{wL^2}{2A}\langle(\kappa-h)^2\rangle_R
 \ge\frac{wL^2(R-h)^2}{2A}
 >0.8 R\Delta/A>8\,10^6\Delta.                              \tag{T4}
\]
The source energy that a quantum-kappa geometry actually sees is therefore
not kept at the old budget. T4 is a positive finite-K zero-mode kinetic
quantity, not a calculation of the missing controller's total energy.

## T4. The genuine constant-field symmetry does not supply this repair

A true constant original-field shift uses the operator kappa:
\[
 {\cal T}_c(u)=e^{-iL(u)(p-\kappa q)},\quad L(u)=a(u)c.
\]
It sends q->q+L, p->p+kappa L and
P_kappa->P_kappa+Lq+L²/2, leaving both D_kappa and raw p-kappa q unchanged.
Since L'=L, it sends P_u->P_u-L(p-kappa q), while the rest of the full
constraint changes by +kappa L(p-kappa q). The constraint and Pi_g
are unchanged. On the parity-even reference it cannot tune the required
mean using the mechanism in T2.

Thus there is a precise normal two-mean example after changing bare state,
and an equally precise reason it is not a physical recovery of the old
geometry/source history. This counterexample prevents the earlier
gate-specific rejection from being advertised as an all-state no-go.
It does not close local preparation, controller stress, full-field
normality or calibrated measurement.
