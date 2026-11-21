# The full homogeneous interior lapse–scale CTP matrix

## L1. What is closed

This page constructs the common-cutoff limit of the **two by two homogeneous external-metric response and noise data**, with the original gravitational action, AE prescription, \(U_0\), incoming matter state, and actual background. The two metric entries are the logarithmic scale \(u\) and conformal lapse \(N\). Both CTP branches retain their lapse until differentiation.

“Full” in this title refers to these four homogeneous interior blocks. Geometry has not itself been quantum-integrated. This is not the normal geometry–matter propagator, the spatial momentum constraints, every tensor harmonic, an initial-density variation theorem, or a finite-amplitude non-Gaussian influence functional.

Let \(x=(w,\nu)\), \(y=(z,\mu)\) be real compact-interior smooth directions on \(I=(0,T)\), \(T=1/50\). They vanish near the original coordinate endpoints. **Their lapse integrals need not vanish.** The initial incoming state and original-coordinate final pairing are unchanged. The two unit-lapse conformal endpoints obtained by separate reparameterizations may differ; neither is silently reset to \(T\).

## L2. General lapse variations and a common differentiable mean tail

For \(N_\epsilon=1+\epsilon\mu\), choose a fixed small parameter interval with \(N_\epsilon\ge1/2\), and set
\[
\tau_\epsilon(t)=\int_0^tN_\epsilon(s)\,ds,\qquad
f(t)=\int_0^t\mu(s)\,ds,\qquad W=z-hf.
\]
This \(\tau\) is unit-lapse **conformal** time, not the proper clock of PREPARED_LIMIT.
The family is the original physical history rewritten in that coordinate, with the incoming identification fixed in the past. For the scalar stress components,
\[
\boxed{\delta_y\rho=D_W\rho+f\rho',\qquad
       \delta_y p=D_Wp+fp'.}                                       \tag{L1}
\]
The moving-evaluation terms are essential.

The high-frequency proof needs a uniform family, not only a formal tangent. A strict analytic margin for \(U\), and finite common jets through order nine for \(U,z\) and order eight for \(\mu\), give common \(L^\infty\) and \(L^1\) bounds for the pulled-back potential and its required parameter derivatives through order six. The exact WKB residual polynomial and zero-incoming Duhamel bounds in RETARDED_RESPONSE therefore give
\(O(k^{-5})\) AE-subtracted stress remainders and parameter derivatives at fixed transformed time.

One cannot say the derivative of the **physical mode** has the old \(O(\omega^{-3/2})\) size: it contains \(fv_k'\), including a leading frequency phase. Instead compose the scalar stress remainder:
\[
\delta R_{\rm physical}=\delta\widetilde R+f\,\partial_\tau\widetilde R.
\]
ADVANCED_CUTOFF's independent time-shift remainder proof bounds the second term by \(Ck^{-5}\) as well. The common mode phase cancels from the scalar stress. The low means and fixed \(U_0\) are treated exactly.

Writing \(R_\rho=\rho_\infty-\rho_K\), \(R_p=p_\infty-p_K\), the result is
\[
\|R_\rho\|_\infty+\|R_p\|_\infty
+\|\delta_yR_\rho\|_\infty+\|\delta_yR_p\|_\infty
 \le C_y/K^2.                                                       \tag{L2}
\]
The constant depends on the stated, finite high-order direction seminorms and the actual analytic margin. It has not been numerically evaluated; no arbitrary high-frequency variation is claimed to have a small response.

## L3. All four response blocks and their contacts

At finite \(K\), vary the original action before setting \(N=1\):
\[
\Gamma_{u,K}=3V_0Na^2(S_K+E_K/2),\qquad
\Gamma_{N,K}=\tfrac32V_0a^2E_K .
\]
The source part equivalently has the physical vertex
\(\Gamma_u^{m}=NV_0a^4(3p-\rho)\),
\(\Gamma_N^{m}=-V_0a^4\rho\).
The gravitational and other common local terms cancel in the difference between the full and finite-cutoff sequences. Hence
\[
\Gamma_{u,\infty}-\Gamma_{u,K}=NV_0a^4(3R_p-R_\rho),\qquad
\Gamma_{N,\infty}-\Gamma_{N,K}=-V_0a^4R_\rho .
\]
At \(N=1\), differentiation in \(y=(z,\mu)\) gives the exact response differences
\[
\boxed{\begin{split}
(\mathcal H_\infty-\mathcal H_K)_u[y]
 &=V_0a^4\{3\delta_yR_p-\delta_yR_\rho
                  +(\mu+4z)(3R_p-R_\rho)\},\\
(\mathcal H_\infty-\mathcal H_K)_N[y]
 &=-V_0a^4\{\delta_yR_\rho+4zR_\rho\}.
\end{split}}                                                       \tag{L3}
\]
The \(\mu+4z\) and \(4z\) terms are metric-chain contacts. They would be lost by applying a noise-style congruence to the response.

For example L2–L3 give the explicit weak estimate
\[
\begin{split}
|\langle x,(\mathcal H_\infty-\mathcal H_K)y\rangle|
\le V_0\|a^4\|_\infty\{&
\|w\|_1[3\|\delta R_p\|_\infty+\|\delta R_\rho\|_\infty
+\|\mu+4z\|_\infty(3\|R_p\|_\infty+\|R_\rho\|_\infty)]\\
+&\|\nu\|_1[\|\delta R_\rho\|_\infty
                  +4\|z\|_\infty\|R_\rho\|_\infty]\}
 =O(K^{-2}).
\end{split}                                                        \tag{L4}
\]
Taking only one nonzero component in each test covers all four blocks. The retarded derivative is computed with the same incoming state, including the original AE loop, subtraction and finite contacts. We do not assign separate all-mode values to bare \(NN\) seagulls. Their combination in the physical action row is what has a limit.

Finite-cutoff backgrounds are not set on shell. The mean terms and differentiated finite Ward identity remain until the limit.

## L4. Same-source noise, positivity, and two-branch compatibility

For one metric test \(x=(w,\nu)\), the centered matter vertex is exactly
\[
X_K(x)=\delta p_K(f_p)+\delta\rho_K(f_\rho),\qquad
f_p=3V_0a^4w,\quad f_\rho=-V_0a^4(w+\nu).
\]
Thus, with stress ordering \((\rho,p)\) and metric ordering \((u,N)\),
\[
\mathsf L=V_0a^4\begin{pmatrix}-1&3\\-1&0\end{pmatrix},
\qquad \mathsf N_{\rm metric,K}=\mathsf L\mathsf N_{\rm stress,K}\mathsf L^T.
\]
TENSOR_NOISE supplies the **absolute** same-state stress matrix, including the annular zero-mode law, NOON low block, zero–shell correlations, and all high incoming vacuum modes. No independent density and pressure noises are introduced.

For \(S_j(f)=\sum_{\ell=0}^j{j\choose\ell}\|f^{(\ell)}\|_1\), set
\[
C_\rho(f)=\frac{8\rho_{\rm an}S_2(f)}{V_0A^4},\quad
C_p(f)=\frac{2S_3(f)}{V_0A^4},\quad
C_x=C_p(f_p)+C_\rho(f_\rho),\quad \rho_{\rm an}=10^{-25}.
\]
The original mode-pair bounds yield
\[
\boxed{|N_\infty(x,y)-N_K(x,y)|\le8C_xC_y/K,\qquad
\|X_\infty(x)-X_K(x)\|_2\le\sqrt{8/K}\,C_x.}                         \tag{L5}
\]
The diagonal missing-shell noise is nonnegative. Finite Gram matrices remain positive in the common GNS limit. Weak commutator data converge with them, while the real local response contacts remain in L3.

With \(x_\Delta=x_+-x_-\), \(x_\Sigma=(x_++x_-)/2\), the common finite-\(K\) CTP second data have the original convention
\[
\Gamma_K^{(2)}
 =\langle x_\Delta,\mathcal H_K^{\rm ret}x_\Sigma\rangle
                 +\frac i2N_K(x_\Delta,x_\Delta).
\]
The linear mean term must also be retained before the full on-shell limit. Equations L2, L4 and L5 prove convergence of that linear-plus-quadratic Taylor data, its positive imaginary part, and its two-branch normalization/reality identities. This does not establish an error bound for the finite-amplitude influence functional.

## L5. Anchored derivation and the gauge/contact check

The anchored subclass is a useful independent calculation, not a second scientific existence certificate. Impose \(f=\int\nu\), \(g=\int\mu\) compactly supported in the interior, so the lapse integrals vanish. Both unit-lapse endpoint identifications then really are the identity.

For the two-parameter coordinate change,
\[
t(\tau)=\tau-\epsilon f-\delta g+\epsilon\delta(\nu g+\mu f)+\cdots .
\]
The transformed scale has first derivative \(Q_x=w-hf\) and mixed derivative
\[
B(x,y)=h(\nu g+\mu f)+h'fg-w'g-z'f .
\]
Writing \(A_K=\Gamma_{u,K}\) at \(N=1\), and \(H_K\) for the unnormalized fixed-lapse \(u\)-action response, the anchored CTP data become
\[
\langle Q_\Delta,H_KQ_\Sigma\rangle
+\int A_K B(x_\Delta,x_\Sigma)
+\frac i2N_{uu,K}(Q_\Delta,Q_\Delta),
\]
in addition to \(\int A_KQ_\Delta\). In particular the \(NN\) contact obeys
\[
\int A_K[h(\nu g+\mu f)+h'fg]=-\int hA_K'fg.
\]
It is generally nonzero at finite cutoff.

An equivalent causal representative is
\[
\delta_y\Gamma_u=H_KQ_y+(A_Kg)',\qquad
\delta_y\Gamma_N(t)=\int_0^t[hH_KQ_y+A_Kz'+hA_K'g].
\]
Its initial variation is zero because the directions and preparation are unchanged near the initial slice. In the anchored weak quotient, the lapse row is only determined modulo a constant; this calculation does not supply a missing independent initial charge.

For \(x_f=(hf,f')\), \(Q_{x_f}=0\) and
\(B(x_f,y)=-f(z'-h\mu)\).
Thus the finite-\(K\) response has the precise off-shell contact
\(-\int A_K f(z'-h\mu)\), which vanishes only after the actual full on-shell limit. The centered noise gauge direction vanishes already at finite \(K\) by source conservation. These calculations check that the state, frame, mean and contact responsibilities have not been separated incorrectly.

The earlier potential-kernel proof also bounds this anchored subclass through
\[
\frac{3\|D_UQ_x\|_1r_\mu(D_UQ_y)}{2K^2}
 +2m_K\|(Q_x)'(Q_y)'\|_1+\|A_K\|_\infty\|B(x,y)\|_1
\]
and the same potential-noise tail. L4 is a stronger smooth-direction stress-row route; it does not assume that the coarser \(m_K=O(K^{-1})\) estimate was sharp.

## L6. Remaining boundary

The original-coordinate endpoint pairing is held fixed throughout this interior theorem. Directions that change the initial density, touch the boundary, change the canonical representation, or vary nonhomogeneous metric modes require their own complete data. The prepared proper-clock tests generally touch the initial slice and use PREPARED_LIMIT's combined domain instead.

We now have a consistent homogeneous two-branch response/noise limit on the actual mean history. A normal joint quantum geometry and its preparation have not been supplied by this external-history calculation.
