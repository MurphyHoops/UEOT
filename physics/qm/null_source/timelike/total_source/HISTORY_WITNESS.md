# A smooth balanced history pair with nonzero full-field influence contrast

This closes an actual free-field history question, without solving or
numerically integrating a new geometry or mode ODE. It does not certify that
these prescribed metrics obey the semiclassical Einstein equations.

## 1. Histories and exact zero-mode cancellation

Set b(x)=exp[-x^2/(1-x^2)] for |x|<1 and zero otherwise,
omega=sqrt(3), delta=pi/(8 omega), Delta=4 delta, epsilon=1/1000, and
\[
 f(\eta)=b(\eta/\delta)-b((\eta-\Delta)/\delta),\quad
 a_+={A\over\sqrt{1+\epsilon f}},\quad a_-=A,\quad N_\pm=a_\pm .
\]
The two bump supports are disjoint. Both histories are positive, smooth,
and exactly static with all common endpoint jets outside the compact pulse.
Since int f=0,
\[
 \int(a_+^{-2}-a_-^{-2})d\eta=0.
\]
The complete zero-mode relative propagator is identity: F0=1 for any common
initial zero-mode state. This avoids assuming a zero-free characteristic
function or overlooking its large phase scale.

## 2. A finite, controlled nonzero Bogoliubov coefficient

In fixed canonical q=A phi,p=P/A and scaled real quadratures,
\[
 H_\eta=\tfrac12[(1+\epsilon f)p^2+
              \omega^2q^2/(1+\epsilon f)],\quad
 M_\epsilon=\omega\begin{pmatrix}0&1+\epsilon f\\
                       -(1+\epsilon f)^{-1}&0\end{pmatrix}.
\]
In the freely rotating frame, the integrated perturbation norm is
K<=(pi/2) epsilon/(1-epsilon). The first-order term gives
beta_1=i omega int f exp(2i omega eta)deta. The delay has phase pi, so the
opposite bumps add in this Fourier component. On the center half of each
bump b>=exp(-1/3)>2/3; throughout the first support cos(2 omega eta)>=1/sqrt2.
Therefore |beta_1|>=pi/(6 sqrt2).

The nonlinear-generator and Dyson remainders together are bounded by
\[
 R\le{\pi\epsilon^2\over2(1-\epsilon)}+e^K-1-K
 \le{\pi\epsilon^2\over2(1-\epsilon)}
                   +{K^2\over2(1-K)}<3\,10^{-6}.
\]
Extraction of beta from a real 2x2 matrix has norm <=1. Hence
\[
 {33\over10^5}<{\pi\over6000\sqrt2}-3\,10^{-6}
          <|\beta_2|\le e^K-1
          <{11\over6982}<{1\over600}.
\]
The middle lower bound is deliberately conservative.

## 3. All ultraviolet modes, without truncating the vacuum

For v_k=a phi_k,
v_k''+(omega_k^2-V)v_k=0, V=a''/a in C_c^infinity.
The incoming Jost multiplier m=e^{i omega_k eta}v_k, normalized to 1 in the
past, obeys its Volterra equation. If L=||V||1, L1=||V'||1,
\[
 \|m\|_\infty\le e^{L/\omega_k},\quad
 \|m'\|_\infty\le Le^{L/\omega_k},\quad
 |\beta_k|\le{e^{L/\omega_k}(L1+L^2)\over4\omega_k^2}
              \le {B\over\omega_k^2}.
\]
The last step is integration by parts in
beta=(2i omega)^(-1) int e^(-2i omega eta) V m; all boundary terms vanish.

There is also rapid decay to every order. For
K_omega g=int_{-infty}^eta exp[2i omega(eta-s)]g(s)ds,
m'=K_omega(Vm) and differentiation commutes with K_omega on the compact
integrands. Set C0=e^(L/sqrt3) and
C_r=sum_(j=0)^(r-1) binom(r-1,j)||V^(j)||1 C_(r-1-j).
Then ||m^(r)||infinity<=C_r uniformly in k, and N integrations by parts give
\[
 |\beta_k|\le{\sum_{j=0}^N {N\choose j}
             \|V^{(j)}\|_1 C_{N-j}\over(2\omega_k)^{N+1}} .
\]

Here the quantitative bounds require only three bump derivatives.
With z=(1-x^2)^(-1),
b''=(4z^4-12z^3+6z^2)e^(1-z).
The peak of |b'| is at z=(3+sqrt3)/2 in (2.35,2.37), where |x|<.77.
A finite Taylor lower bound for exp(1.35) gives
|b'|<2(.77)(2.37)^2(.26)<9/4 and ||b''||1<9.
The only two extrema of b'' for z>=1 are the roots of
2z^3-14z^2+21z-6, in (1.59,1.60) and (5.03,5.04).
Exact root counting, monotonic polynomial bounds and finite Taylor sums give
min b''>-38/9 and max b''<599/28. Its total variation is
4(max-min)-4<6203/63<100. These are finite rational certificates.

Let h=1-epsilon. Disjoint supports give
||f''||1<18/delta, ||f'||2^2<9/delta,
||f'''||1<200/delta^2,
||f'f''||1<81/(2 delta^2), ||f'||3^3<81/(4 delta^2).
The exact expression
\[
 V=-{\epsilon f''\over2(1+\epsilon f)}
    +{3\epsilon^2(f')^2\over4(1+\epsilon f)^2}
\]
therefore implies
\[
 L\le{9\epsilon\over h\delta}
       +{27\epsilon^2\over4h^2\delta}<{1\over25},
\quad
 L1\le{1\over\delta^2}\left[
 {100\epsilon\over h}+{81\epsilon^2\over h^2}
                     +{243\epsilon^3\over8h^3}\right]<{39\over20}.
\]
Use the exact delta^(-2)=192/pi^2. Thus
B=e^(L/sqrt3)(L1+L^2)/4 <(85/83)(39/20+1/625)/4<1/2.

The two-species mode transformation is Hilbert-Schmidt:
sum_(k>=2) 2k^2 |beta_k|^2 <=(32/9)B^2(pi^2/6-1)<infinity.
The Shale implementability theorem and vacuum determinant give
\[
 |F_{\rm rest}|=\exp[-\tfrac12\sum_{k\ge3}
                   k^2\log(1+|\beta_k|^2)]
       >\exp(-5/54)>0.9 .
\]
Here sum_(k>=3) k^2/(k^2-1)^2
<=(16/9)(pi^2/6-5/4)<20/27 was used.
Only the modulus is needed. The common AE/CTP prescription must fix the
state-independent phase; no unrenormalized vacuum phase product is claimed.
For the general implementer/determinant theorem see Bruneau-Derezinski,
arXiv:math-ph/0511069, section 3.1, Theorem 3.2.

## 4. Nonzero full-field contrast and precise scope

The initial zero modes, chosen shell and higher vacuum modes are independent
in this comparison. Therefore
\[
 |\Delta F_{\rm full}|
 =|F_0 F_{\rm rest}\Delta F^s|
 >.9\,{8c(33/10^5)^2\over(1+1/360000)^3}
 >\tfrac34\,10^{-6}c>0 .
\]
This is a finite-history full free-field amplitude difference. It is not a
metric probability, detector total variation, sensitivity, or on-shell
gravitational signal. During the nonstatic pulse, the pure-pressure tensor
form of the static comparison must not be reused; full W2 equality and mean
equality still persist under each common linear propagation.
