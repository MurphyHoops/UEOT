# JC15 — An actual lapse history supplies a missing preparation column

## 1. Same incoming state, a real metric history

The static natural-ground theorem in STATIC_RESPONSE.md is not a
theorem about all actual metric histories. Here is a controlled
countercolumn using the **same incoming AP ground**, with no
instantaneous ground resets.

Let \(\delta=1/100\),
\[
 w(u)=e^{\,4-1/[u(1-u)]}\quad(0<u<1),\qquad
 I_w=\int_0^1w,\quad
 b_\delta(t)=w((t+\delta)/\delta)/(\delta I_w).
\]
It is zero outside \([-\delta,0]\), has flat endpoints and integral one.
On \([1/3,2/3]\), \(w\geq e^{-1/2}\), so
\(I_w\geq e^{-1/2}/3>1/5\) and \(\|b_\delta\|_\infty<500\).
Set
\[
 ds^2=-N(t,x)^2dt^2+\gamma_{ij}dx^idx^j,\quad
 N=1+f(t)Z(x),\quad f=\epsilon b_\delta,\quad r=1/5 .               \tag{1}
\]
For \(|\epsilon|\leq10^{-4}\), \(N>0.95\).
The past and future metrics are exactly the same ESU.
Measure at \(T=\delta\), so every source-to-read lag lies in
\([\delta,2\delta]\).

Because the spatial metric is fixed and the shift is zero,
\[
 NR[g]=6N-2\Delta N .
\]
The entire quadratic field Hamiltonian in the fixed canonical chart is
therefore exactly
\[
 H^{\rm quad}_K[N]=H_{r,K}+f(t)A_{Z,K},\qquad A_Z=\int ZT_{00}.     \tag{2}
\]
This includes the conformal improvement. Scalar metric counterterms
are separate; (2) does not assert their nonlinear part vanishes.

## 2. Exact first response and a uniform sign

Let \(v_{\sigma k}=d_{\sigma k}^2W_{\sigma k}\) and
\(\Omega_{\sigma k}=\omega_{\sigma k}+\omega_{\sigma,k+1}\).
The finite dipole spectral variance in SHARP_CHARGES.md gives
\[
 \chi(t)=-2\sum_{\sigma,k}v_{\sigma k}\sin(\Omega_{\sigma k}t).
\]
Define \(M_1=\sum\Omega v,\ M_2=\sum\Omega^2v\). Elementary bounds give
\[
 M_1>4/23763,\qquad M_2<9/1024 .                                 \tag{3}
\]
For the first inequality the plus first pair alone suffices; for
the second use the same positive-gap shell estimates as for the
dipole variance. Since \(|\sin x-x|\leq x^2/2\),
\[
 \chi(t)\leq t(-2M_1+M_2t)
 \leq-\delta[8/23763-9/51200]<-1.6\times10^{-6}
 \quad(\delta\leq t\leq2\delta).                                 \tag{4}
\]
Normalize \(b_\delta\) and integrate this bound. It proves the actual
first tangent is strictly nonzero, with terminal spatial metric
variation equal to zero. At cutoff \(K\), the missing response is
at most twice the variance tail; for example \(K=16\) still preserves
the strictly negative sign.

## 3. A finite-amplitude normal history, not only a tangent

In the AP diagonal Fock space write
\[
 H_0=d\Gamma(D),\quad
 A_Z=d\Gamma(a)+\tfrac12(a^\dagger ba^\dagger+\mathrm{h.c.}).
\]
Here \(D\) contains both \(\mu=\pm r\) fields; only adjacent shells
occur. The edge coefficients in the number and pair blocks are
\[
 a_{kl}=\frac{kl+\mu+\omega_k\omega_l}{2\sqrt{\omega_k\omega_l}}F_{kl},
 \qquad b_{kl}=\frac{d_k}{2\sqrt{\omega_k\omega_l}}F_{kl}.
\]
They obey
\[
 \|aD^{-1}\|<5,\quad |a|\leq2D\ {\rm as\ a\ form},\quad
 \|b\|_{\rm HS}<0.03,\quad \|Db\|_{\rm HS}<0.133 .                  \tag{5}
\]
The notation \(|a|\leq2D\) means the two-sided quadratic form bound,
not an unproved operator ordering for a noncommuting absolute value.

For clarity, the full Fock domain estimate is explicit. On an
\(n\)-particle sector, the same-factor terms in
\((\sum_i a_i)^2\) are bounded by \(25D_i^2\).
Writing \(a=D^{1/2}BD^{1/2}\), \(\|B\|\leq2\), bounds different-factor
terms by \(4D_iD_j\). Thus
\(\|d\Gamma(a)\psi\|\leq5\|H_0\psi\|\).
The pair bound is at most
\(0.03\|(N_{\rm num}+2)\psi\|\), and \(D\geq\sqrt{0.8}\), yielding
\[
 \|A_Z\psi\|\leq6\|H_0\psi\|+0.06\|\psi\| .
\]
Since \(|f|<0.05\), \(H_0+fA_Z\) has relative bound below \(0.3\),
is self-adjoint and bounded below on the common \(D(H_0)\), and
depends smoothly on time in its graph norm. Kato's common-domain
evolution theorem applies; see
[Integration of the equation of evolution in a Banach space](https://www.jstage.jst.go.jp/article/jmath1948/5/2/5_2_208/_pdf),
§1, Theorem 4 and its hypotheses.

The actual compressed coefficients converge on a finite-mode,
finite-particle core, with the same relative bounds.
They therefore converge on \(D(H_0)\). Common-domain Duhamel
estimates on compact graph-norm evolution orbits give strong
\(U_K,U_K^\dagger\) convergence. The inherited common-diagonal
identification and the free high-mode tails are retained:
\(D_K-D\) has relative norm tending to zero and \(e_K\to e\).
No fixed physical \(H_r\) domain is imposed on bare-tail cutoff vectors.

The resulting normal endpoint state is the actual metric PDE state,
by uniqueness of its symplectic Cauchy evolution. Propagation of the
incoming Hadamard condition and return to the same final operator
give a final Hadamard state. On compact \(S^3\) its smooth two-point
difference gives all final coupled-energy moments.
This last assertion is about the limit state; all-order cutoff graph
convergence for this metric pulse is not claimed.

## 4. A controlled nonlinear endpoint signal

The adjacent-shell bound gives
\(\|[D,a]D^{-1}\|<6\). For the number-part evolution,
\[
 \|Du_\epsilon D^{-1}\|\leq e^{6|\epsilon|}<1.001,\qquad
 \|(u_\epsilon-u_0)D^{-1}\|\leq5|\epsilon|.
\]
Factoring out that evolution, the pair kernel is Hilbert--Schmidt
and has an integrable \(D\)-weighted norm. The pair Dyson estimate
and (5) give, throughout the stated amplitude interval,
\[
 \|D\beta\|_{\rm HS}<0.134|\epsilon|,\quad
 \|\beta\|_{\rm HS}<0.031|\epsilon|,\quad
 E_{\rm exc}<0.005\epsilon^2 .
\]
The anomalous covariance differs from its linear term in HS norm
by less than \(3\epsilon^2\).
Using the number form bound and the pair HS bound yields the safe
remainder
\[
 |\langle A_Z(T)\rangle-\epsilon\chi[b_\delta]|
 \leq\epsilon^2 .                                                \tag{6}
\]
This weighted argument is necessary: trace-norm density convergence
alone would not control the unbounded energy observable.

At the concrete amplitude \(\epsilon=10^{-8}\),
\[
 \boxed{\langle A_Z(T)\rangle<-1.59\times10^{-14}.}                 \tag{7}
\]
The same incoming ground has thus acquired a nonzero endpoint
density dipole through a genuine smooth metric history.

## 5. The candidate is not a self-consistent Einstein solution

At the endpoint the geometry is again the signed static ESU,
so its geometric dipole constraint is zero. The residual projected
scalar constraint is
\[
 \int Z(R^{(3)}-2\Lambda-16\pi G_N\rho)
          =-16\pi G_N\langle A_Z\rangle>0 .
\]
The certificate gives its explicit model-unit lower bound.
Thus this particular metric pulse is rejected as a complete mean
Einstein history. It proves that the actual-history preparation
column exists; it does not close the coupled geometric equations.

Nor does the chosen normal-ordering implementer phase by itself
match the covariant metric CTP phase. LAPSE_CURVATURE.md records
the exact curvature subtraction data and the remaining finite-phase
obligation.
