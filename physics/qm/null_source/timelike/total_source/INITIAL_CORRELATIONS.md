# Source noise does not determine a unique metric record

## 1. The exact missing initial block

For a specified linear model write u=H Y+R Xi, including every homogeneous,
state and memory initial datum in Y. With CY=Cov(Y), K=Cov(Y,Xi), N=Cov(Xi),
\[
 {\rm Cov}(u)=H C_Y H^*+H K R^*+R K^*H^*+R N R^* .
\]
A source-only metric difference requires the compared initial contribution
I=H CY H*+H K R*+R K* H* to agree on the chosen observables. Holding CY and K
separately fixed is a transparent sufficient condition, not a necessary one.

If a legal Gaussian constrained baseline Sigma_minus already exists and
Delta N>=0 lies in the constraint null direction, adding diag(0,Delta N)
to its joint covariance preserves positivity, CY, K and the constraints.
It can be represented by an independent Gaussian increment. This conditional
existence statement is not a quantum CP preparation of the two NOON states,
nor an all-order influence-factorization theorem. In particular it does not
supply the missing absolute baseline in CONSTRAINTS.md.

## 2. Same marginals, different answer

Let Z=(Zc,Zs) be two independent standard Gaussian auxiliaries for the
rank-two pressure increment. Set
u_p=-A^2 sqrt(Dp)(qc Zc+qs Zs).
Choose a legitimate coupled homogeneous state-geometry tangent h, P h=0,
and a real test ell with b=ell(h) !=0. Define a=(ell(qc),ell(qs)),
v=A^2 sqrt(Dp) a/b, Y_plus=+v^T Z, Y_minus=-v^T Z, u_plus/minus=u_p+hY_plus/minus.
Both joint covariances are positive Gram matrices:
\[
 \Sigma_\pm=\begin{pmatrix}I_2&\pm v\\\pm v^T&v^Tv\end{pmatrix}\ge0 .
\]
The entire source law and the marginal law of the homogeneous initial amplitude
coincide. In particular the metric, first and second derivative initial
marginals coincide, since their forced contributions vanish. No unavailable
higher-order initial jet is assumed.
Nevertheless
\[
 {\rm Var}\,\ell(u_+)=0,\qquad
 {\rm Var}\,\ell(u_-)=4A^4Dp\|a\|^2 .
\]
Only the initial cross correlations differ.

For fixed Var(Y)=sigma_Y^2 the exact allowed range is
(sqrt(Vp)-|b|sigma_Y)^2 <= Var(ell u)
 <=(sqrt(Vp)+|b|sigma_Y)^2, Vp=A^4Dp||a||^2.
With only Var(Y)<=Vmax, the minimum is
(sqrt(Vp)-|b|sqrt(Vmax))_+^2.

Choosing h=exp(sigma_F t) and
Y_F=A^2 sqrt(Dp)(rc Zc+rs Zs) cancels the fast amplitude in this linear
model; the required variance is
A^4Dp/[(sigma_F^2+Omega^2)P'(sigma_F)^2].
The opposite correlation quadruples that amplitude variance while preserving
both marginals. This is an initial choice, not a causal feedback protocol,
and cancels neither the other modes nor the initial UV issue.

The mode h must include its legitimate Hadamard Cauchy covariance and normal
derivatives, as proved in ../dynamic_inverse/STATE_MATCHING.md. Arbitrary
metric jets are not admissible substitutes. Gaussian amplitudes are unbounded,
so this construction does not yield a uniform nonlinear small-history bound.

## 3. An explicit quantum uncertainty obstruction

The auxiliaries Zc,Zs are not two simultaneously readable quantum pressure
quadratures. For all eight shell oscillators let
A2=sum a_j^2, Q=A2+A2^dagger, P=i(A2^dagger-A2).
Then
\[
 [Q,P]=2i(4N_{\rm tot}+16),\qquad
 \langle4N_{\rm tot}+16\rangle=16(1+2n)>0.
\]
For any normal joint extension of either specified NOON state, with finite
required moments, if a
geometry/carrier variable Y commutes with the matter algebra,
\[
 {\rm Var}(Q-kY){\rm Var}(P)
  -{\rm Cov}_{sym}(Q-kY,P)^2\ge[16(1+2n)]^2>0 .
\]
Thus a finite-resource quantum joint state of that kind cannot cancel the
entire actual pressure quadrature variance. The Gaussian example cancels an
auxiliary DIFFERENCE component; it does not evade this inequality.

The actual NOON preparations themselves obey it:
Var Q_plus/minus=Var P_plus/minus=16(2n^2+2n+1) +/-8cd.
Since c<=w<n^2 and d=4, even the lower value exceeds 16(1+2n).
The missing task is a physical joint initial state, not merely a positive
classical covariance matrix.
