# L. Actual reduced-model spatial covariance and a controlled field comparison

## L1. A legal bounded observable, not a presumed sharp-time full operator

Fix the critical lower branch, J=[.54,.56], and L=10000. Let
P_L=1_[E_c,E_c+L](H_c). Define

 A_(m,L)=P_L T00,K(Y_m) P_L for any field-mode cutoff K>=L.   (L1)

Every initial/final occupied mode then has k<=L, so all finite
matrix elements stabilize exactly. This is the DEFINITION of A_(m,L).
It does not first apply an undefined full sharp-time T00 to vacuum.
The finite-dimensional Hermitian matrix is bounded.

Use the actual physical reduced slice u_*=.55,
U_L(u,u_*)=exp[-i integral h(w,H_c)dw]. The previous L=100 chart
certificate alone would not justify L=10000; the present certificate
checks the larger slab, even including excitation energies up to 1e8.

A coarse independent admission proof is useful. Put m0=3V/2 and
a_c=1/240, and write the same constraint as

 F(x)=a_c(1+x)²+Va²[U_0a²-(3/2)(1+x)]+N_exc.

Frozen parameters give 2.9<U_0a²<3.1 and Va²>3e11 on J.
At x=.81, F>.185 Va²>0. At x=1.21,
F<-.215 Va²+1e8+.021<0. Throughout, F_x<-4e11.
There is a unique lower root with .9<kappa<1.1 and
sqrt(Delta)>4e11 on the whole stated slab.

## L2. Exact actual propagation and positive two-time kernel

Set w_(m,n)=1_(E_c+n)(H_c) A_(m,L)|0>. From SPATIAL_NOISE,

 ||w_(m,n)||²=C_m, n=m+1+2r<=L,

and different n are orthogonal. With the common phase origin u_*,

 A_(m,L)(u)|0>=sum_n exp[i Theta_n(u)] w_(m,n),
 Theta_n(u)=integral_(u_*)^u [h(w,E_c+n)-h(w,E_c)]dw
           =integral_(u_*)^u dw integral_0^n dx/kappa(w,E_c+x).

The double integral avoids subtraction of enormous geometry phases.
The actual covariance and any real time-smeared variance are exactly

 W_m(u,v)=C_m sum_n exp[-i(Theta_n(u)-Theta_n(v))],
 Var=C_m sum_n |integral g_u(u)exp[iTheta_n(u)]du|².      (L2)

The physical density harmonic is rho_(m,L)=a^-4 A_(m,L).
Thus the observable in (L2) is integral a⁴ g_u rho_(m,L) du.
It is a conformally weighted density; it is not a unit-proper-time
average, a metric percentage or an implemented measurement device.

This is the selected reduced physical observable. In the raw weighted
representation its representative is A_raw=R^-1 A_(m,L) R.
It obeys A_raw* kappa=kappa A_raw, and weighted expectations agree.
A_(m,L) changes energy and generally does NOT commute with R.
The original bare matrix in raw variables would be a different
operator. If the R² endpoint phase is restored, transport the state,
propagator and observable together by exp[iF_lambda(kappa)].
The covariance is invariant under that simultaneous transport.

## L3. A fixed compact test that approximates the full field smearing

Let y0=2VU_0/[m0+sqrt(m0²-4a_cVU_0)]. Then
kappa0(u)=sqrt(A²exp(2u)y0-1), and the vacuum conformal clock is

 tau0(u)=atan kappa0(u)-atan kappa0(.55), tau0'=1/kappa0.

This is explicit; no ODE is solved. Since kappa0<1.1, tau0(J)
contains [-1/110,1/110]. Fix the six-box test of SPATIAL_NOISE with
delta=1/600 and define

 g_u(u)=g(tau0(u))/kappa0(u).

Its support is strictly inside J and its integral is one. It is fixed
independently of L, the field cutoff and apparatus input; it is C4 /
W^(5,1), not C-infinity. For physical density use a⁴g_u.

The exact derivative h_EE=-1/[2kappa³sqrt(Delta)] gives, uniformly,

 |Theta_n(u)-n tau0(u)|<=Gamma n²,
 Gamma=(1/100)/[4(.9)³(4e11)].                         (L3)

The factor 1/100 is the maximum CENTER-to-end u distance.
Both actual and reference vectors are aligned at the same u_*.
There is no discarded energy-dependent phase constant.

For m=3, L=10000, M=L/2, the squared GNS-vector comparison error is

 epsilon_L² <= C_3 {
 Gamma² *16[M(M+1)(2M+1)(3M²+3M-1)/30-1]
                         +(2/delta)^12 L^-11/22 }.     (L4)

The first term bounds phases of 4999 retained frequencies; the
orthogonal second term bounds the omitted infinite reference tail.
It is a comparison for this ONE fixed finite band and smearing,
not a same-chart L->infinity claim. Consequently

 |sqrt(Var_actual)-sqrt(Var_reference)|<=epsilon_L,
 |Var_actual-Var_reference|
                  <=epsilon_L(2sqrt(Var_reference)+epsilon_L).

The outward certificate establishes epsilon_L<1e-5.
Also any nonnegative unit-integral u test on J gives the direct
nonzero bound Var_actual>=C_3 cos²(2/45) from the n=4 sector.
Exact homogeneous constraint matching therefore does not remove this
bounded spatially nonconstant fluctuation.

## L4. The SAME observable with a backreacting independent apparatus

Let a source-independent K_app commute H_c, with a normal apparatus
state rho_A on a common invariant spectral interval I_A. Assume the
whole rectangle N in [0,L], e in I_A is admitted for
T(u)=E_c+N+f(u)e. Actual U is the same reduced h(u,T), and the observable
is A_(m,L) tensor I_A. Let mu(de)=Tr rho_A dP_K(e). Then

 Theta_(n,e)=integral_(u_*)^u dw integral_0^n dx/
                              kappa(w,E_c+f(w)e+x),
 Var_actual=C_3 sum_(n<=L) integral mu(de)
                 |integral g_u exp[iTheta_(n,e)]du|².   (L5)

This is an exact positive kernel with actual apparatus energy.
Apparatus coherences are not removed from the state; this particular
expectation depends only on its K spectral law.
For the three-field apparatus of LOCAL_AUTONOMOUS, f=exp[-2(u-.55)].
Its complete energy-class hull plus L fits inside the new 1e8 slab.

With S_max=sup|f e|, the SAME fixed vacuum-profile comparison has

 |Theta_(n,e)-n tau0|<=Gamma[n²+2nS_max],
 epsilon_app²<=C_3{Gamma² sum_(n<=L)(n²+2nS_max)²
                              +(2/delta)^12 L^-11/22}. (L6)

The actual apparatus is not replaced by its mean. The certificate
evaluates this uniform bound for the admitted local-device hull.

For an energy-dependent QND apparatus, such as the qubit, a common
unchanged e across a source transition would be wrong. On a common
admitted apparatus space the exact general expression is instead

 C_3 sum_n ||integral g_u U_n(u)* U_0(u) rho_A^(1/2) du||_HS².

Source-dependent spectral projections must also be retained when
there is no common invariant space.

## L5. Remaining physical identification

The result closes an actual normal reduced-model covariance and a
controlled comparison with a full-field conditional smearing.
It does not derive A_(m,L) from an inhomogeneous lapse variation of
the full action, restore unrestricted field CCR, solve spatial
Einstein constraints, or construct a density-measuring apparatus.
Those are additional physical gates; physical unification is open.
