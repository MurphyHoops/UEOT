# A normal correlated boundary source: small density residual and its costs

This is a new initial-state family in the ORIGINAL two-field minimal
massless action on the same static mean background A. There is no new
dust field, lattice, ordering, or gravity action in this entry.
It changes the original matter marginal substantially. It is not a
solution of the full stochastic or quantum gravitational constraints.

The result has two sides. A normal correlated source can have arbitrarily
small, explicitly controlled global density fluctuation while retaining
the original total mean stress and a nonzero NOON pressure contrast.
Exact zero global energy variance is impossible in the standard normal
matter representation; improving the finite tolerance changes the source
records and makes canonical Q/dilation spreads grow.

## 1. Fix the action, state, time and energy normalization

Use physical proper-time energy and conformal time eta:
\[
 V=V_0 A^3,\quad V_0=2\pi^2,\quad
 \omega_k=\sqrt{k^2-1},\quad \varepsilon_2=\sqrt3/A .
\]
The normal-ordered free matter Hamiltonian, including the fixed vacuum
and U0 contributions as the finite c-number E_c, is
\[
 H_s={P_1^2+P_2^2\over2A^3}
        +\sum_{k\ge2,m,i}{\omega_k\over A}N_{kmi}+E_c.
\tag{65}
\]
The zero modes use the same de-sheared canonical frame [Q_j,P_l]=i delta_jl.
Let E_z denote the frozen unfiltered mean zero-mode energy:
\[
 K_2=V_0M_2,\quad \mu=L+1/\nu_0,\quad
 E_z={K_2\mu\over2A^3},\quad L=1+\sqrt3/4.
\]
The mean here is L+1/nu0, not the earlier preparation's L+2/nu0.
The frozen k=2 occupation is n=0.0180421959121815... per oscillator.

All A, n, packet centers and widths below are selected once on this
initial slice. On a changed metric the SAME canonical state is
transported. In particular e_N(A) is never replaced by e_N(a(t))
time by time to re-narrow an evolving distribution.

## 2. An explicit positive normal density

Let d=4 and
\[
 |A_i\rangle=d^{-1/2}\sum_{m=1}^d |2_m\ {\rm in\ species}\ i\rangle,
 \qquad |A_\pm\rangle=(|A_1\rangle\pm|A_2\rangle)/\sqrt2.
\]
Put p=4n, so 0<p<1, and
\[
 E_*=E_z+2p\varepsilon_2,\qquad
 e_0=E_*,\qquad e_2=E_*-2\varepsilon_2.
\tag{66}
\]
The frozen constants give e2>0.

Choose one real even w in C_c^infinity(R), supported on [-1,1],
with integral w^2=1. For the quantitative example use the normalized
bump proportional to exp[-1/(1-x^2)] on |x|<1, zero elsewhere.
Write
mu2=integral x^2 w(x)^2 dx, J=integral |w'(x)|^2 dx;
for the displayed decreasing bump, 0<mu2<1/3. For 0<sigma<e2, define
\[
 e(P)={|P|^2\over2A^3},\qquad
 \psi_N(P)={w((e(P)-e_N)/\sigma)\over\sqrt{2\pi A^3\sigma}},
 \quad N=0,2.
\tag{67}
\]
Since d^2P=A^3 de dtheta, each vector is exactly normalized.
Its support is a compact annulus away from P=0, so it belongs to
C_c^infinity(R^2) and has all canonical Q/P polynomial moments.

The actual source state is
\[
 \rho_\pm=(1-p)|\psi_0\rangle\langle\psi_0|\otimes|0\rangle\langle0|
       +p|\psi_2\rangle\langle\psi_2|\otimes|A_\pm\rangle\langle A_\pm|,
\tag{68}
\]
tensored with the vacuum of every k>=3 mode. This is a positive,
trace-one, rank-at-most-two normal density. It is a correlated
zero/shell state, not an independent replacement of the two marginals
and not a delta distribution on a continuous energy surface.

## 3. What is exactly preserved

In either branch the total energy above E_c is E_*+sigma x,
with x distributed by w(x)^2. Thus both signs have the same complete
global energy law, not just its first two moments. Moreover
\[
 \langle H_z\rangle=(1-p)e_0+pe_2=E_z,\quad
 \langle N_2\rangle=2p=8n.
\]
For each of the eight shell oscillators,
< a_j^dagger a_l >= n delta_jl and <a_j a_l>=0.
Its FULL species marginal is not the old thermal density.

Consequently the summed zero-mode mean rho=p, shell radiation mean
p=rho/3, fixed vacuum terms and U0 are unchanged. Both original static
mean Einstein equations therefore hold exactly. The fixed evolution
exp(-it H_s), t=A eta, gives one normal free-field history; all the
mean residuals and their normal derivatives remain zero on it.
The density matrix itself need not be stationary.

There is also a useful precise transport statement. For the same
minimal massless action and canonical Cauchy identification, with metric
perturbations after that slice, write the linear field solution as
Phi_i[g]=Q_i/sqrt(V0)+P_i f_g+high_i[g]. A constant is an exact solution
on every prescribed metric, so stress derivatives remove Q_i.
The new state has the same sum_i<P_i^2>, zero zero/high quadratic cross
moments, the same high-mode quadratic moments, and the same ultraviolet
sector as the frozen input. Hence the TOTAL trace of differentiated W2,
sum_i<dPhi_i(x)dPhi_i(x')>, agrees with the old state under this common
transport. With a common covariant subtraction, the total mean-RSET
functional and its existing retarded metric variation agree as well.
This is a derivative-W2 statement for the summed shift-invariant stress,
not equality of the full species W2, higher moments, or boundary CTP
functional. A changed transport/controller requires a fresh calculation.

Between rho_plus and rho_minus the complete W2 itself is identical:
a quadratic operator cannot connect A1 and A2. Their higher stress
correlations and influence are different. All fixed-background Hadamard
singularities are preserved because only finitely many mode moments
have changed, by finite smooth functions.

## 4. A uniformly small absolute global density residual

Let k=H_s-E_c-E_*. Then
\[
 \langle k\rangle=0,\quad
 \operatorname{Var}H_s=\sigma^2\mu_2,\quad
 {\rm spec}_{\rho_\pm}(k)\subset[-\sigma,\sigma].
\tag{69}
\]
Thus the global density fluctuation delta rho_bar=k/V is bounded in its
actual spectral law by sigma/V, with RMS sigma sqrt(mu2)/V.
It is conserved throughout the fixed static free history. Any smooth
unit-integral time test gives the same global density law.
This is not a bound on arbitrary local density noise.

The example sigma=epsilon2/100 gives
\[
 \sigma_{\bar\rho}< {1\over100 V_0 A^4},\qquad
 {\sigma_{\bar\rho}\over\rho_0}
 <{1\over150 V_0 A^2},\quad \rho_0={3\over2A^2}.
\tag{70}
\]
The interval certificate gives its numerical enclosure. The family can
meet any strictly positive global-density tolerance by choosing a
smaller fixed sigma. No source record is discarded.

It cannot attain zero tolerance as a normal matter state. The nonzero
mode Fock occupation basis is countable and complete on compact S3.
In each occupation sector H_s acts on L2(R2,d2P) by multiplication by
|P|^2/(2A^3)+E_alpha+E_c. Every fixed-energy level is a circle, a point,
or empty, with two-dimensional Lebesgue measure zero. Hence
ker(H_s-E)=0 for all E. If a normal density with finite required moments
had Var H_s=0, then
||(H_s-<H_s>)rho^(1/2)||_HS^2=0 would force support rho into that zero
eigenspace, a contradiction.

There is no trace-one normal limit as sigma tends to zero. A putative
normal limit would give probability one to every shrinking interval
around E_c+E_*, and by normal continuity to the zero spectral projection
at that single energy. Generalized eigenstates or singular algebraic
limits are outside this claim.

Accordingly, the inherited identically-zero linear density response row
still cannot solve an EXACT stochastic constraint with any fixed sigma>0.
This entry supplies a controlled finite residual in a new source family,
not the missing exact absolute gravitational baseline.

## 5. The COMPLETE spatially averaged density-pressure covariance

This section computes the absolute homogeneous source covariance,
including its vacuum tail, not merely the difference of two noises.
It does not compute every local tensor component.

Let N=N2 and A2=sum_(j=1)^8 a_j^2. Define
Q_eta=A2 exp(-2i sqrt(3) eta)+A2^dagger exp(2i sqrt(3) eta).
After spatial integration, harmonic orthogonality removes cross-shell
and zero/nonzero cross terms in the averaged stress. The fluctuations are
\[
 \delta\bar\rho=k/V,\qquad
 \delta\bar p=k/V-{2\varepsilon_2\over3V}\delta N
                 -{\varepsilon_2\over3V}Q_\eta
                 +\delta\bar p_{\rm rest}.
\tag{71}
\]
The common profile makes the JOINT spectral law of k and N a product,
so Cov(k,N)=0. Number grading gives
Cov_sym(k,Q_eta)=Cov_sym(N,Q_eta)=0 in the actual block-diagonal state.
These cross terms are computed, not set to zero by a false independence
assumption.

One has Var N=4p(1-p),
A2|A_plus>=4|0>, A2|A_minus>=0, and [A2,A2^dagger]=4N+16.
Thus the Q variance in vacuum/plus/minus is respectively 16/56/24,
and in (68) it is 16+(24+/-16)p.
For tau=eta-eta' and s_rho^2=sigma^2 mu2/V^2,
\[
 N_{\rho\rho}(\eta,\eta')=N_{\rho p}(\eta,\eta')=s_\rho^2,
\tag{72}
\]
\[
 \begin{split}
 N_{pp}^{\pm}(\eta,\eta')={}&s_\rho^2+
 {16p(1-p)\varepsilon_2^2\over9V^2}\\
 &+{\varepsilon_2^2[16+(24\pm16)p]\over9V^2}
            \cos(2\sqrt3\,\tau)\\
 &+{4\over9V_0^2A^8}
       \sum_{k\ge3}k^2(k^2-1)\cos(2\sqrt{k^2-1}\,\tau).
 \end{split}
\tag{73}
\]
All kernels are connected symmetrized covariances with no extra 1/4
normalization. The final line is a distribution. An equal-time value
for it is not assigned. Against real compact smooth time tests its
Fourier coefficients decay rapidly and its quadratic form converges.
The constant density/pressure block is positive, and each oscillatory
pressure contribution has nonnegative spectral weight, consistent with
the explicitly positive density (68).

## 6. One genuine smooth positive-window source budget

Use I=(0,2) in CONFORMAL time. Let
b(x)=exp[-x^2/(1-x^2)] for |x|<1, zero elsewhere,
B=integral b, and
\[
 f(\eta)=2b(2(\eta-1))/B.
\]
It has support [1/2,3/2] compactly inside I, is nonnegative, smooth and
has integral one. The frozen HISTORY_WITNESS proof gives
B>2/3 and ||b'''||1<100, so ||f'''||1<1200.
Three integrations by parts and the frozen convergent tail estimate give
\[
 {4\over9V_0^2A^8}\sum_{k\ge3}k^2(k^2-1)
              |\widehat f(2\sqrt{k^2-1})|^2
 <{200000\over27 V_0^2A^8}.
\tag{74}
\]
Indeed the intermediate bound is
||f'''||1^2/(144 V0^2 A^8) times
sum_(k>=3) k^2/(k^2-1)^2 <20/27.
The ultraviolet sum has not been numerically truncated.

Using |fhat|<=1, the plus/minus absolute pressure variance satisfies
\[
 \operatorname{Var}_\pm\bar p_f
 <{\sigma^2\over3V^2}
  +{200000/27+(16+(40\pm16)p-16p^2)/3\over V_0^2A^8}.
\tag{75}
\]
The plus sign gives 56p and the minus sign 24p.

The normalized density proportional to b has second moment <1/3,
because b is strictly decreasing in |x|. After removing the center phase,
cos x>=1-x^2/2 gives |fhat(2sqrt3)|>1/2. Hence the pressure contrast on
this SAME test is strictly positive:
\[
 \Delta\operatorname{Var}\bar p_f
 ={32p\varepsilon_2^2\over9V^2}|\widehat f(2\sqrt3)|^2
 >{8p\varepsilon_2^2\over9V^2}>0.
\tag{76}
\]
This is a full absolute SOURCE variance budget and a source contrast.
The proper duration of I is 2A, not the earlier proper-time 1/24
response window. Neither a stable metric inverse nor a local measurement
of this global average has been constructed here.

## 7. Local noise DIFFERENCE and a full-field influence witness survive

Let K=|A1><A2|. Then
rho_plus-rho_minus=p |psi2><psi2| tensor (K+K^dagger).
A nonzero connecting matrix element needs four selected k=2 operators.
A product of two local stresses contains only four field factors.
Every term involving a zero mode, another shell, a subtraction term
or a mean product therefore drops out of the DIFFERENCE; this includes
the local zero/high cross terms, which cannot just be omitted pointwise.
Only the four-shell-operator term remains.

Thus the frozen complete local difference formula applies with
c_eff=p/2=2n:
\[
 \Delta N_{abcd}(x,x')={8p\over d}
       \operatorname{Re}[{\cal T}_{ab}(x){\cal T}_{cd}(x')^*].
\]
On the static background it is a pure pressure kernel with
D_new=8 p d [sqrt(3)/(3V0 A^4)]^2, consistent with (76).
Density and momentum DIFFERENCE slots vanish, not all higher records.
The absolute local tensor noise is not being replaced by this difference.

For the frozen balanced prescribed-history pair, the zero-mode relative
PROPAGATOR is exactly the identity. This remains true in the correlated
state (68); zero/shell independence is unnecessary.
The exact full-field influence contrast is consequently
\[
 \Delta F_{\rm full}
 =-{p d|\beta_2|^2\over(\alpha_2^*)^{d+2}}F_{\rm rest}.
\tag{77}
\]
Read-only frozen evidence gives
|beta2|>33/100000, |beta2|<1/600 and |F_rest|>0.9, with the full vacuum
implementability/tail proof. Therefore
\[
 |\Delta F_{\rm full}|>
 {0.9\,p d(33/100000)^2\over(1+1/360000)^3}>0.
\tag{78}
\]
This is a prescribed-history amplitude, not an on-shell gravity signal,
an instrument probability, or a control protocol. For unbalanced histories
a nontrivial psi2 zero-mode factor remains; the old full influence is not
generally unchanged.


## 7a. Exact non-Gaussian homogeneous boundary factor

The actual correlated density (68) permits more than a difference witness.
Here the histories are real Lorentzian homogeneous histories, identified
on common canonical initial and final Cauchy data. The relative mode
coefficients must come from one family of actual implementable evolutions,
not independent choices for each pair. A useful restricted class has
smooth deformations supported away from the common endpoints, with the
necessary endpoint jets agreeing. General endpoint changes can spoil
ultraviolet implementability and are not certified by this finite-shell
calculation.

Write
\[
 V^\dagger aV=\alpha a+\beta a^\dagger,\qquad
 y=|\beta|^2,\qquad |\alpha|^2=1+y .
\]
Choose the continuous implementer branch from the diagonal. Its
one-oscillator Bargmann kernel is
\[
 K(z,\zeta)=(\alpha^*)^{-1/2}
 \exp\left({\beta z^2\over2\alpha^*}
       +{z\zeta\over\alpha^*}
       -{\beta^*\zeta^2\over2\alpha^*}\right).
\]
Direct coefficient extraction gives
\[
 {V_{22}\over V_{00}}={1-y/2\over(\alpha^*)^2},\qquad
 {V_{20}V_{02}\over V_{00}^2}={-y\over2(\alpha^*)^2}.
\]
Summing the d diagonal and d(d-1) within-species terms and the d^2
cross-species terms, with the actual normalized states, gives
\[
 \langle A_\pm|V^{\otimes2d}|A_\pm\rangle
 ={1-\frac d2(1\pm1)y\over(\alpha^*)^{d+2}},\qquad d=4.
\tag{77a}
\]
The minus state is a lowest-weight vector of the collective pair-lowering
operator; it is not a pressure eigenstate and is not invariant under
general squeezing.

For a lapse N and coordinate t set
\[
 \Delta I=\int\left({N_+\over a_+^3}-{N_-\over a_-^3}\right)dt,
 \qquad
 W(z)=\int w(x)^2e^{-izx}\,dx,\qquad z=A^3\sigma\Delta I .
\]
In a common conformal parametrization this is the difference of the
integrals of a^{-2} d eta. The initial e_N, A and sigma in (67) stay fixed.
The zero-mode relative propagator is exp(-i P^2 Delta I/2), so its actual
conditional factors are
\[
 \chi_N=e^{-iA^3e_N\Delta I}W(z).
\]
Consequently the exact state-dependent homogeneous influence is
\[
 F_\pm=F_{\rm rest}^{\rm ren}\left[
 {(1-p)\chi_0\over(\alpha^*)^d}
 +{p\chi_2[1-\frac d2(1\pm1)y]\over(\alpha^*)^{d+2}}
 \right].
\tag{77b}
\]
The two correlated branches are summed before taking a logarithm. This
cannot be replaced by the product of their zero-mode and shell marginal
influences, or by a Gaussian trace-log using W2 alone.

Here F_rest^ren denotes the common admissible vacuum/rest influence and
the U0/local counterterm phase under ONE prescription. Formula (77b)
does not newly evaluate an unrestricted infinite vacuum phase, complete
tensor CTP Hessian, boundary Ward terms, or the gravitational path
integral. For the frozen balanced witness its implementability, modulus
bound and zero-mode identity are already supplied by the cited frozen
proof. General histories require their own common domain and phase
prescription.

On the diagonal alpha=1, beta=0, Delta I=0 and F_rest^ren=1, giving F=1.
The exact difference is
\[
 F_+-F_-=-{pd\,y\over(\alpha^*)^{d+2}}\chi_2F_{\rm rest}^{\rm ren},
\]
which reduces to (77) on the balanced witness. At general Delta I, W
can have zeros; a nonzero contrast is not asserted for every history pair.

There is an independent physical unit and phase check. For a STATIC
proper elapsed-time difference s, Delta I=s/A^3 and alpha=exp(-i s
epsilon2), beta=0. Both correlated branches then equal
\[
 e^{-is(E_*+d\varepsilon_2)}W(s\sigma).
\]
Including the common renormalized c-number phase gives
\[
 F_\pm(s)=e^{-is(E_c+E_*)}W(s\sigma).
\tag{77c}
\]
This recovers the mean and variance of the SAME total Hamiltonian (69).
The relation between Delta I and the oscillator phase used here holds
for this static time-translation subfamily, not every beta=0 history.

## 7b. A controlled logarithm domain, with an explicit cumulant error

Choose the stated even bump, whose squared profile decreases with |x|.
Then mu2<1/3 and mu4=integral x^4 w^2<1/5; evenness alone would not imply
these estimates. Write alpha*=sqrt(1+y) exp(i theta) on a continuous
phase chart and phi=2(A^3 epsilon2 Delta I-theta). Factoring (77b) gives
\[
 F_\pm=F_{\rm rest}^{\rm ren}
       e^{-iA^3E_*\Delta I}(\alpha^*)^{-d}W(z)B_\pm,\quad
 B_\pm=(1-p)+p e^{i\phi}{1-c_\pm y\over1+y},\quad
 c_+=4,\quad c_-=0 .
\tag{77d}
\]
For y>=0, (1-4y)/(1+y) lies in (-4,1], whereas 1/(1+y) lies in (0,1].
Thus
\[
 |B_+-1|\le5p<1,\quad |B_--1|\le2p<1,\qquad
 |B_+|\ge1-5p,\quad |B_-|\ge1-2p .
\tag{77e}
\]
Each B has a well-defined principal logarithm in the displayed disk.
For real |z|<=1, evenness and cos x>=1-x^2/2 give W(z)>5/6.
Taylor's cosine remainder and the log remainder give
\[
 \left|\log W(z)+{\mu_2z^2\over2}\right|
 \le z^4\left({\mu_4\over24}
       +{\mu_2^2\over8(1-\mu_2/2)}\right)
 \le {z^4\over40}.
\tag{77f}
\]
The last inequality is strict for 0<|z|<=1; at z=0 both sides vanish.
For clarity, put u=W-1. One has |u|<=mu2 z^2/2,
|u+mu2 z^2/2|<=mu4 z^4/24 and
|log(1+u)-u|<=u^2/[2(1-|u|)], proving the bound.
It controls only the zero-energy profile's quadratic-cumulant remainder.
It is NOT a Gaussian closure error for the full metric influence.
A logarithm of the remaining alpha/vacuum phase still needs the same
local or simply connected continuous phase branch; nonvanishing does
not supply a global single-valued logarithm on an arbitrary history space.

At every finite mode cutoff, actual common unitaries give
F_ij=Tr(U_i rho U_j^dagger)=Tr(rho U_j^dagger U_i).
With Hilbert-Schmidt vectors v_i=sqrt(rho) U_i^dagger this is
F_ij=<v_i,v_j>, so every finite matrix is positive semidefinite,
F_ii=1 and F_ji=F_ij^*. The infinite-field statement requires the stated
common implementable/renormalized limit. A real counterterm action
difference multiplies rows and columns by conjugate phases and preserves
this positive-type property; arbitrary independently selected pair
phases need not. This does not prove conditional positivity of log F,
infinite divisibility, a classical stochastic representation of all
cumulants, or an actual CP instrument.

## 8. The source change and canonical costs are large

For J=integral |w'|^2 and
d_w=integral(2xw'+w)^2=4 integral x^2|w'|^2-1>=0, direct differentiation
in the declared frame gives
\[
 \langle Q_1^2+Q_2^2\rangle={2E_z J\over A^3\sigma^2},\qquad
 \langle D_0\rangle=0,
\]
\[
 \operatorname{Var}D_0=
 {4J[E_z^2+4\varepsilon_2^2p(1-p)]\over\sigma^2}+d_w.
\tag{79}
\]
Integration by parts gives mu2 J>=1/4, so
Var H_s Var D0>=E_z^2, in accord with the quantum bound in
ORIGINAL_CTP_GATE. Improving the energy tolerance grows these spreads,
rather than preserving the original full marginal and evading its bound.

For the example sigma=epsilon2/100, the Dirichlet Poincare inequality
J>=pi^2/4 gives a rigorous lower bound on the ratio of (79) to the
frozen de-sheared initial sum 2/x0. For this flat compact bump the
Poincare bound also follows directly by writing w=cos(pi x/2) z and
integrating: integral |w'|^2-(pi^2/4)integral |w|^2
=integral cos^2(pi x/2)|z'|^2>=0.
This is a canonical record/spread
cost. The mean field energy stays fixed. No apparatus energy, work, or
preparation-time cost follows from this Q-spread formula alone.
An added shear/phase or a different canonical frame must be accounted
for explicitly.

The change is also large in trace distance. Put kappaE=K2/(2A^3).
For every sigma<=kappaE/100 the certificate proves that the new P^2/K2
law is supported in [7/5,3/2]. The original law is the two-ring Gaussian
mixture with centers R=1 and r_hi=1+sqrt3/2 and normalized covariance
I/(2nu0). Let
d_*=min(sqrt(7/5)-1,sqrt(r_hi)-sqrt(3/2)).
The reverse triangle inequality and the exact two-dimensional Gaussian
radial tail give
\[
 \Pr_{\rm old}\{7/5\le P^2/K2\le3/2\}
 \le e^{-\nu_0d_*^2}.
\]
Measuring this spectral event and using trace-distance contractivity gives
\[
 D_{\rm tr}(\rho_{\pm},\rho_{\rm old})
 \ge1-e^{-\nu_0d_*^2}.
\tag{80}
\]
The same lower bound holds already for the bare zero-mode marginal.
The certificate reports the exponent, without rounding a strictly
positive tail to zero. This is a quantitatively different preparation,
not an approximation of the original complete source.

## 9. An autonomous preparation cannot omit its apparatus

The construction above specifies a legal boundary density. It has not
built an autonomous device that takes the original source to it.

For a heralded preparation whose selected Kraus operators commute with
the P^2/K2 event projection in (80), and whose selected output is supported
in that event, the success probability cannot exceed its input probability:
p_success<=exp(-nu0 d_*^2). This follows from the Kraus contraction bound
and is a necessary limit for that nondemolition-filter route, not an
achievable success probability or a bound on all possible preparations.
Keeping the entire trace-preserving record of a P-nondemolition instrument
also preserves the input P distribution. A different operation that changes
P must include its actual control and energy exchange.

There is a necessary conditional ledger. Suppose the preparation starts
from rho_old tensor rho_app, the endpoint interaction is off, and a unitary
U conserves the closed apparatus-plus-source Hamiltonian H_s+H_app,
with all variances in this ledger finite.
Then its entire spectral law and variance are unchanged:
V_tot,out=V_tot,in=V_old+V_app,in >= V_old.
If the outgoing source has variance V_s,out=sigma^2 mu2, the triangle
inequality for centered energy observables implies
\[
 \sqrt{V_{\rm app,out}}
 \ge(\sqrt{V_{\rm tot,in}}-\sigma\sqrt{\mu_2})_+.
\tag{81}
\]
Lowering the field variance does not lower the CLOSED total variance;
the other degrees of freedom and cross terms must be included.
This statement assumes the displayed conserved total energy and product
initial input. A changed background, initial correlations, work reservoir
or time-dependent control must be explicitly included in a new contract.
It is not an optimal device mean-energy bound, and it does not prohibit
redistribution of local stress or a pressure-dependent gravity record.

## 10. Closure and the next concrete task

This entry establishes one normal, Hadamard source family, one fixed free
history, exact inherited mean stress, a finite positive-window absolute
homogeneous noise budget, and a nonzero pressure/influence contrast.
It also proves the exact-normal zero-variance obstruction, a large bare
state change, diverging canonical spreads, and the missing apparatus
variance ledger under an autonomous preparation assumption.

The original complete-source contract is therefore NOT replaced.
The next step remains a legal TOTAL geometry-matter-device boundary state
and one common CTP/constraint evolution. Its required new boundary column
must be derived, all local constraints and initial Ward terms must pass,
and the source replacement/device costs must be stated before calibration.
The arbitrary-small source-only residual is not acceptance of the exact
gravitational baseline or physical unification.
