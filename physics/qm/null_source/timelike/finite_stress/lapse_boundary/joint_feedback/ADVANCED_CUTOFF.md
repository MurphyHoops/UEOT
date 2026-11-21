# Independent advanced cutoff convergence on the actual history

This page completes a missing inference. Strong convergence of forward inverses alone does not imply strong convergence of their adjoints. We prove the advanced estimates independently, with the same incoming state and finite-cutoff action, and only then identify the transpose. The result concerns external-metric linear response on the accepted classical history, not a quantum geometry propagator.

## A1. Spaces and the frozen forward result

Let \(I=[0,T]\), \(T=1/50\), \(a=Ae^U\), \(h=U'\), \(\gamma=24A\). Keep the one-time selection \(c=e^{-20000}\), the same incoming modes and thin low state, the full fixed \(U_0\), and the original AE finite terms. The accepted history obeys \(\varepsilon<e^{-1158}\). Put
\[
Y_\pm=L^2(I,e^{\mp2\gamma t}dt),\quad
X_+=\{w\in H^4:w^{(j)}(0)=0,\ j=0,\ldots,3\},
\]
\[
X_-=\{z\in H^4:z^{(j)}(T)=0,\ j=0,\ldots,3\},
\qquad \|w\|_{X_\pm}=\|w^{(4)}\|_{Y_\pm}.
\]
Thus \(Y_-\) has the growing weight. A star below denotes the transpose under the unweighted test pairing \(Y_+\times Y_-\), not an uncorrected adjoint in either weighted Hilbert space.

The predecessor ACTUAL_CUTOFF_INVERSE proves the static and actual **action** inverses strongly \(Y_+\to X_+\), with a common static bound \(M_0=10^{15}\) for \(K\ge10^9\). Its comparison budget is \(1000\varepsilon\), hence
\[
q=10^{18}e^{-1158}<e^{-1100}<1.
\]
We reuse that forward result and its exact static resolvent estimate. We do not infer a new adjoint statement from it. The limiting action row is on its graph domain; the fourth-order logarithm does not define a bounded row on all \(H^4\).

## A2. A time derivative of the actual AE mean remainder

A bound for \(S_K'\), as well as \(S_K,E_K\), is needed before transposing the finite-cutoff Ward defect. It follows by differentiating a **uniformly controlled time-shift family**, not by differentiating an \(O(K^{-2})\) statement formally.

Choose \(d>0\) so that the accepted analytic bidisc contains the background through \(T+2d\). For \(|\zeta|\le d\) set \(U_\zeta(t)=U(t+\zeta)\). Positive background frequencies and the larger-center analytic coefficient norm give, for every fixed finite \(j\),
\[
|\partial_t^jU_\zeta(t)|\le \rho\,j!d^{-j}e^{s(t-T)},\qquad t\le T.
\]
The norm \(\rho\) here includes the translation factor at the larger center. In particular the first nine jets give finite common \(L^\infty\) and \(L^1\) bounds for \(V_\zeta=U_\zeta''+(U_\zeta')^2\) and the time/parameter derivatives needed below. These constants are not all asserted to be \(\varepsilon\)-small.

The correctly normalized shifted mode is
\(v_{k,\zeta}(t)=e^{i\omega_k\zeta}v_k(t+\zeta)\).
The compensating phase preserves the same incoming normalization. For
\[
\Omega=\omega-\frac{V}{2\omega}
 +\frac{V''-V^2}{8\omega^3}
 +\frac{-V^{(4)}+5(V')^2+6VV''-2V^3}{32\omega^5},
\quad
W=(2\Omega)^{-1/2}e^{-i\omega t-i\int_{-\infty}^t(\Omega-\omega)},
\]
choose a common finite threshold with \(F=\Omega/\omega\in[1/2,3/2]\).
The exact residual identity from RETARDED_RESPONSE is
\[
4F^2\{\,\omega^2-V-\Omega^2-\Omega''/(2\Omega)
                    +3(\Omega')^2/(4\Omega^2)\,\}=z^3P(z),\quad z=\omega^{-2}.
\]
The finite polynomial \(P\), and its shift derivative, are bounded by the stated jets. The residual is \(O(\omega^{-6})\) in both \(L^1\) and \(L^\infty\), uniformly in \(\zeta\).
The shift derivative of the normalized WKB mode is
\[
\partial_\zeta W/W=-\Omega'/(2\Omega)-i(\Omega-\omega),
\]
so it is \(O(\omega^{-3/2})\), and its first time derivative is \(O(\omega^{-1/2})\).
The zero-incoming Duhamel equation for \(e=v-W\), and then for \(\partial_\zeta e\), gives \(e,\partial_\zeta e=O(\omega^{-15/2})\) and their first time derivatives \(O(\omega^{-13/2})\).

Substituting in the physical density/pressure and the **same frozen \(k\)-AE subtractors** gives a per-mode remainder and its shift derivative bounded by \(Ck^{-5}\). The degeneracy is \(k^2\). The zero-mode momentum, low occupation, and \(U_0\) are not reselected, and their means transform by the same shift. Therefore, for some finite stated-seminorm constant \(C_{\rm mean,1}\),
\[
\boxed{\|E_K\|_\infty+\|S_K\|_\infty+\|S_K'\|_\infty
                   \le C_{\rm mean,1}/K^2.}                         \tag{A1}
\]
The full means vanish on this history. The shifted family is a proof device: its initial \(a\) need not equal \(A\), and it is not a new physical initial condition.

## A3. Independent advanced action estimates

Reflection
\((JF)(r)=e^{\gamma T}F(T-r)\)
is an isometry \(Y_-\to Y_+\), and \(X_-\to X_+\).
Define the static advanced convolution explicitly by \(G_{0,K}(s-t)\) for \(s\ge t\). Reflection, the same vertical line \(\Re z=\gamma\), and weighted Plancherel give
\[
G_{0,K}^{\rm adv}\longrightarrow G_0^{\rm adv}
\quad\hbox{strongly }Y_-\to X_-,
\qquad \|G_{0,K}^{\rm adv}\|\le M_0.
\]
This uses the static multiplier proof anew. The fast poles have not been discarded.

For the actual-minus-static action row, the gravitational derivative form, the mean chain term \(-2D(\Delta\bar QD)\), and real multiplication terms transpose directly. The local AE fourth-order coefficients satisfy
\(a_3=2a_4'\), \(a_1=a_2'-a_4'''\).
Thus their formal transpose is the same expression; the potentially extra high background derivatives cancel exactly.

The retarded nonlocal block \(D_U^\dagger R^{\rm ret}D_U\) becomes \(D_U^\dagger R^{\rm adv}D_U\), with \(R^{\rm adv}(t,s)=R^{\rm ret}(s,t)\).
For \(D_+=\partial_t+\partial_s\), the already established pointwise estimates reprove the advanced weighted Schur bounds
\[
\|D_+^jR_K^{\rm adv}\|_{Y_-\to Y_-}<23\mu,\qquad
\|D_+^j(R_K^{\rm adv}-R^{\rm adv})\|<22\mu/K,\quad j=0,1,2.
\]
Here \(\mu<5\varepsilon\).
The integration identity is explicitly
\[
D T_R^{\rm adv}f=T_R^{\rm adv}f'
 +T_{D_+R}^{\rm adv}f-R(T,t)f(T).
\]
The terminal zero traces of \(D_Uz\) remove the displayed boundary term and the one in its second derivative. The static advanced \(K_{0,K}\) map from terminal-zero \(H^1\) to \(Y_-\) is independently uniformly bounded by \(3/\sqrt\gamma\) times the derivative norm, and converges strongly by its reflected multiplier.

Using the finite-window terminal Hardy inequalities gives the same separate epsilon budgets:
\[
500+61+12+4+17+3+30=627<1000.
\]
They correspond respectively to the nonlocal difference, static variable coefficients, mean chain contact, anomaly, gravity, zero mode, and \(U_0\).
Consequently the advanced Neumann construction has norm at most \(M_0/(1-q)\) and converges strongly \(Y_-\to X_-\).
At finite \(K\), Green's identity on smooth initial/terminal cores and Fubini identify it with the unweighted action transpose. Density and the uniform bounds extend the identity. Only after this independent proof is it legitimate to denote the result \(\widehat G_K^*\to\widehat G^*\).

## A4. Retain the finite-cutoff off-shell correction

On the fixed full-field history, the finite \(K\) means are generally off shell:
\(E_K'=h(2S_K-E_K)\).
The exact action–pressure relation is
\(\widehat H_K=M L_{p,K}+D_K\), where the predecessor gives
\[
D_Kw=e^{2U}(2S_K+E_K)w+
 \tfrac12e^U\int_0^t e^U(2S_K-E_K)w'.
\]
For \(w(0)=0\), integration by parts and the finite Ward identity give
\[
D_Kw=e^{2U}(3S_K+E_K/2)w
               -e^U\int_0^t e^US_K'w.                              \tag{A2}
\]
Thus
\[
d_K=e^{2\varepsilon}
 [3\|S_K\|_\infty+\tfrac12\|E_K\|_\infty+\|S_K'\|_\infty/\gamma]
 =O(K^{-2})
\]
bounds \(D_K:Y_+\to Y_+\). Its exact transpose is
\[
D_K^*z=e^{2U}(3S_K+E_K/2)z
            -e^US_K'\int_t^T e^Uz,                                 \tag{A3}
\]
with the same \(Y_-\) norm bound.

Set \(r_K=d_KM_0/[\gamma^4(1-q)]\).
There exists a finite \(K_2\ge10^9\), also above the WKB threshold, such that \(r_K\le1/2\). This proof does not numerically identify \(K_2\).
The pressure transpose is
\[
\boxed{G_{p,K}^*=M^*\widehat G_K^*
                     (I-D_K^*\widehat G_K^*)^{-1}.}                 \tag{A4}
\]
All factors and domains have now been controlled. For every fixed \(F\in Y_-\),
\[
q_K=-a^2G_{p,K}^*F\longrightarrow q_F=-a^2M^*\widehat G^*F
                      \quad\hbox{in }H^3(I),
\]
\[
q_K(T)=q_K'(T)=q_K''(T)=0,\qquad
\|q_K\|_{H^3,-}\le
\frac{1536A^2M_0}{\gamma(1-q)}\|F\|_{Y_-}.                          \tag{A5}
\]
This is fixed-input strong convergence with a common bound. It is not operator-norm convergence, an effective total cutoff rate, unweighted stability, or a replacement of the incoming state by a future vacuum. PREPARED_LIMIT next applies it to the actual source-GNS observables.
