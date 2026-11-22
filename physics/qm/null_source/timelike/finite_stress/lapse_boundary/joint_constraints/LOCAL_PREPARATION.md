# JC6 — A local smooth source pulse with an actual normal endpoint state

## 1. Physical input and local action

Use the AP ground \(\Omega_r\) at \(r=1/5\), not the actual AQ ramp
output. Put \(\Phi_+=(\phi+\psi)/\sqrt2\), \(\mu=r\), \(Z=x_4\), and
add
\[
 \Delta S=-\frac12\int\sqrt{-g}\,s(t,x)\Phi_+^2,\qquad
 s(t,x)=\epsilon b(t)Z(x).                                       \tag{1}
\]
In the original fields this is
\(-\epsilon bZ(\phi+\psi)^2/4\): it changes the diagonal masses as
well as the mixing. It is not simply a spatially varying version of
the old off-diagonal source \(r\).
The interaction is a pointwise local action over a compact time interval
and the compact \(S^3\). Implementing its spatial profile would require
an actual distributed actuator; no such apparatus is presumed.

For \(|u|<1\) let \(w(u)=\exp[1-1/(1-u^2)]\), and zero outside.
Set
\[
 I=\int_{-1}^1w(u)du,\quad a(t)=10w(10t)/I,\quad
 b=a*\widetilde a,\quad \widetilde a(t)=a(-t).
\]
Then \(a,b\) are real, even, nonnegative and smooth with flat ends,
\(\int a=\int b=1\), \({\rm supp}\,b\subset[-1/5,1/5]\), and
\[
 \widehat b(\omega)=|\widehat a(\omega)|^2\geq0,\quad
 I\geq e^{-1/3},\quad \|b\|_\infty\leq10e^{1/3}<14.                \tag{2}
\]
For \(|\epsilon|\leq1/100\), the instantaneous plus spatial operator
is bounded below by \(1.2-0.14>1\); the minus field retains gap \(0.8\).
Smooth normally hyperbolic propagation transports the incoming Hadamard
state for the actual operator. After the pulse that operator is again
the same \(P_r\).

## 2. Uniform constituent-cutoff endpoint construction

On the plus one-particle space let
\[
 D=\sqrt{-\Delta_\gamma+1+\mu},\quad
 {\cal D}={\rm diag}(D,-D),\quad
 B_Z=\tfrac12D^{-1/2}ZD^{-1/2},\quad
 V_Z=\begin{pmatrix}-iB_Z&-iB_Z\\iB_Z&iB_Z\end{pmatrix}.
\]
For the canonical annihilation variable
\(a=(D^{1/2}q+iD^{-1/2}p)/\sqrt2\), the Bogoliubov evolution has
generator \(-i{\cal D}+\epsilon b(t)V_Z\), with
\(\nu=\|V_Z\|\leq1/\sqrt{1.2}\).
The actual cutoff is the same spectral \(P_K\) in both blocks;
it commutes with \(D\), and \(V_{Z,K}=P_KV_ZP_K\) has the same norm bound.

In the interaction picture the \(n\)-th Dyson term has ordered time
integrals of \(b(t_1)\cdots b(t_n)V(t_1)\cdots V(t_n)\).
At finite \(K\), applying \({\rm ad}_{\cal D}^p\) to the product is
\(i^{-p}(\sum_j\partial_{t_j})^p\).
This common translation is tangent to every ordering facet
\(t_j=t_{j+1}\); the external boundaries vanish by flatness of \(b\).
Integration by parts therefore gives, uniformly in the actual \(K\),
\[
 \|{\rm ad}_{\cal D}^pU_n\|
 \leq\frac{n^p(\nu L_p)^n}{n!},\qquad
 L_p=\max_{0\leq j\leq p}\|b^{(j)}\|_1 .                          \tag{3}
\]
After summing the multinomial assignments, the integrand is permutation
symmetric; this is the justification for the \(1/n!\), even though
individual derivative assignments need not be symmetric.

For the off-diagonal block \(\beta\), put
\(C_p=(D\,\cdot+\cdot\,D)^p\beta\). In an eigenbasis,
\[
 \beta_{ij}=(C_p)_{ij}/(\omega_i+\omega_j)^p,\qquad
 \|D^q\beta\|_{\rm HS}^2
 \leq\|C_p\|^2\,{\rm Tr}\,D^{2q-2p}<\infty
 \quad(p>q+3/2).                                                 \tag{4}
\]
The same estimate applies to the actual cutoff. The Dyson series and
their integrated commutators converge strongly, together with their
adjoints, since \(V_K\to V\) strongly with uniform norms. Consequently
each row of \(C_{p,K}\) converges in \(\ell^2\).
The summable row bound in (4) then proves
\[
 D^q\beta_K\longrightarrow D^q\beta
 \quad\hbox{in Hilbert--Schmidt norm, for every }q.                \tag{5}
\]
The estimates are uniform on compact small complex-parameter sets.
They therefore also justify parameter derivatives and Taylor
remainders in these weighted spaces. Bounds on every diagonal
\({\rm ad}_D^p\alpha\), and the inverse commutator identity, show
that \(\alpha,\alpha^\dagger\) and their inverses preserve the
corresponding energy graph domains.

In a sufficiently small parameter neighborhood the associated
symmetric Bogoliubov quotient has operator norm below one. With the
Heisenberg convention \(U^\dagger aU=\alpha a+\beta a^\dagger\),
the output squeeze kernel is
\[
 Z_{\rm out}=(\alpha^\dagger)^{-1}\beta^T .
\]
Choose vacuum-overlap-positive Gaussian representatives. Their
determinant normalization and quadratic exponential, using (5) and
the graph bounds, define a normal pure Gaussian density, real analytic
in the real parameter, with all final \(H_r\) moments. The actual
constituent densities and energy graphs converge to it. The unchanged
minus field and the inherited common-diagonal/varying-\(H_K\)
identification are retained.

This proves an actual endpoint density construction and a uniform
first-order remainder, stronger than a formal first Dyson vector.
It does **not** prove convergence of the unadjusted physical scalar
phases of \(U_K\), nor complete the phase-sensitive CTP action.
Those phases and local contacts remain in SOURCE_ACCOUNTING.md.

For a concrete coarse budget, put \(z=|\epsilon|\nu L_3\). From (3),
\(\|C_3\|\leq e^z(z^3+3z^2+z)\), and
\({\rm Tr}D^{-5}\leq\zeta(3)\). Hence
\[
 E_{\rm exc}={\rm Tr}(D\beta\beta^\dagger)
 \leq\zeta(3)e^{2z}(z^3+3z^2+z)^2 .                              \tag{6}
\]
This finite bound is not an optimized experimental resource estimate.

## 3. A strictly nonzero, full-field preparation column

Write \(\omega_k=\sqrt{k^2+\mu}\), \(\Omega_k=\omega_k+\omega_{k+1}\),
and \(W_k,d_k\) as in SHARP_CHARGES.md for the plus field. Let
\[
 O_Z=\tfrac12\int Z\Phi_+^2,\qquad A_Z=\int ZT_{00}.
\]
The pair matrix elements of \(A_Z\) are \(d_k\) times those of \(O_Z\).
The actual endpoint derivative is
\[
 a_1(T):=\left.\frac{d}{d\epsilon}\langle A_Z(T)\rangle\right|_0
 =-2\sum_{k\geq1}d_kW_k\,\widehat b(\Omega_k)\sin(\Omega_kT).
                                                                    \tag{7}
\]
The number block of \(A_Z\) is first order relative to \(D\), and its
pair block is Hilbert--Schmidt. Equations (3)–(5) justify evaluating
this observable on the actual analytic endpoint states, and
interchanging the derivative with this constituent limit.

At \(T=\pi\), write \(\Omega_k=2k+1+\delta_k\).
Here \(0<\delta_k\leq\delta_1<0.15\), \(d_k<0\), and
\(\sin(\pi\Omega_k)=-\sin(\pi\delta_k)<0\).
Every term in (7) has the same negative sign; there is no uncontrolled
high-frequency cancellation. Since
\(\widehat b(\Omega_1)\geq\cos^2(\Omega_1/10)\),
\[
 -a_1(\pi)\geq
 2|d_1|W_1\cos^2(\Omega_1/10)\sin[\pi(\Omega_1-3)]
 >9\times10^{-4}.                                                \tag{8}
\]
The certificate encloses this first-shell lower bound without any
mode or geometry ODE.

For four profiles \(Z_A\), \(SO(4)\) covariance gives
\(\langle A_A\rangle=a_1(\pi)\epsilon_A+O(|\epsilon|^3)\).
The actual analytic state map and (8) imply a local inverse for four
small target moments. The existence neighborhood has not yet been
assigned a numerical radius.

## 4. The tensor, work and fluctuations that accompany this column

Define
\[
 o_1(T)=-2\sum_kW_k\widehat b(\Omega_k)\sin(\Omega_kT).
\]
To first order for \(\mathbf z=\boldsymbol\epsilon\cdot\mathbf Z\),
\[
 \delta\rho=\frac{4a_1}{V_0}\mathbf z,\quad
 \delta T_{0i}=-\frac{4a_1'}{3V_0}\partial_i\mathbf z,\quad
 \delta T_{ij}=\frac{4(a_1-2\mu o_1)}{3V_0}\mathbf z\,\gamma_{ij},
 \quad
 \delta\langle\Phi_+^2\rangle=\frac{8o_1}{V_0}\mathbf z .
\]
The identity \(d_k(\Omega_k^2-1)=-2\mu\) implies
\(a_1''+a_1=2\mu o_1\), verifying both post-pulse conservation
equations and the state-dependent trace. At \(T=\pi\),
\(a_1'<0\), so the associated momentum is not zero.

For the scalar pulse the exact endpoint energy and its variance obey
\[
 E_{\rm exc}=\epsilon^2E_b+O(\epsilon^4),\quad
 {\rm Var}(H_r)=\epsilon^2V_b+O(\epsilon^4),
\]
\[
 E_b=\sum_k\Omega_kW_k|\widehat b(\Omega_k)|^2>0,\qquad
 V_b=\sum_k\Omega_k^2W_k|\widehat b(\Omega_k)|^2>0 .
\]
They are finite by the smooth pulse estimates. The work is quadratic
in the control, while its energy standard deviation is linear.
Neither this work nor this fluctuation can be erased from an eventual
total apparatus source. JOINT_PREPARATION.md next controls the
longitudinal momentum as well.
