# Prepared source readouts through the actual advanced limit

## P1. Combine the source and boundary before taking a limit

Keep the actual two NOON-sign source states and the incoming zero-mode phase from PREPARED_READOUT. For any real \(q\in H^2(I)\) with \(q(T)=q'(T)=0\), that page constructs in the same incoming GNS representation
\[
R_K(q)=\int q\,\delta p_K-B_{i,K}(q)
      =\int[r_q\,\delta Q_K+w_q\,\delta H_{0,K}],
\]
\[
w_q=q/(3V_0a^4),\qquad r_q=w_q''+3hw_q'+Vw_q.
\]
The combined object converges to a bounded linear map
\(R:H^2_{\rm terminal}\to L^2(\rho)\).
Neither \(\delta Q_i,\delta D_i\), nor the sharp boundary subtraction, is asserted to have its own all-mode second-moment limit.

For \(q\in H^3\) with three terminal zero traces, its high-mode variance tail obeys the already explicit bound
\[
\begin{split}
{\cal T}_K(q)\le{}&
 \frac{9|a_q(0)|^2}{32K}
 +\frac{9\pi(1+T^2/2)}{16\omega_{K+1}^2}\|a_q'\|_2^2\\
&+\frac{81C_I^2}{8K}(\|r_q\|_1+\|w_q\|_1)^2,\qquad
a_q=r_q+Vw_q,\ C_I=10\mu .
\end{split}                                                        \tag{P1}
\]
All low-mode terms and zero–shell correlations are kept. This is an absolute variance tail of orthogonal missing high-shell outputs.

For a fixed \(F\in Y_-\), ADVANCED_CUTOFF supplies \(q_K\to q_F\) in \(H^3\), with uniform \(H^3\) control. Consequently
\[
\boxed{\|R_K(q_K)-R(q_F)\|_2
 \le C_R\|q_K-q_F\|_{H^2}+\sqrt{{\cal T}_K(q_K)}\longrightarrow0.}     \tag{P2}
\]
The second term is \(O(K^{-1/2})\); a rate for the first strong-convergence term has not been established. It would be incorrect to label the total error \(O(K^{-1/2})\).

## P2. Keep the legal source charge and its mixed blocks

The relevant endpoint charge is the already constructed combination
\[
H_{i,K}=\delta(H_{0,K}-V_iQ_K)_i,
\qquad \|H_i-H_{i,K}\|_2^2\le200\mu^2/K .
\]
It is not the unrenormalized sharp-time density. Define
\[
\Lambda(q)=-\frac{q(0)}{3V_0A^4h_i},\qquad
{\cal W}_{\lambda,K}(F)=R_K(q_K)+\lambda\Lambda(q_K)H_{i,K}.
\]
For each fixed real \(\lambda\) and fixed \(F\),
\[
{\cal W}_{\lambda,K}(F)\longrightarrow
{\cal W}_{\lambda}(F)=R(q_F)+\lambda\Lambda(q_F)H_i
                       \quad\hbox{in the same GNS Hilbert space}.   \tag{P3}
\]
In addition to P2, an explicit error is
\[
|\lambda|\,|\Lambda(q_K)-\Lambda(q_F)|\,\|H_i\|_2
+|\lambda\Lambda(q_K)|\,\sqrt{200}\mu/\sqrt K.
\]
The trace \(q(0)\) is continuous on \(H^2\), but its coefficient includes the very large \(1/h_i\). No smallness is inferred from the small background norm.

For any finite list of tests, the whole Gram matrix, symmetric covariances, and weak commutator expectations converge by Cauchy–Schwarz. This includes the source-charge mixed blocks. It does not prove a joint spectral measure, unique self-adjoint closures for all readouts, or a completely positive apparatus instrument.

## P3. The density residual is controlled without pretending finite K is on shell

For the \(\lambda=1\) boundary candidate, the finite-mode construction fixes the initial density defect to zero and has zero initial geometry and first-derivative traces. Let \(r_K=e_K-d_K^{\rm source}\) denote the linear density defect; the superscript distinguishes the source density from ADVANCED_CUTOFF's scalar norm bound \(d_K\).
The actual finite-mode Ward identity gives
\[
r_K'+hr_K=(2S_K-E_K)w_K',\qquad r_K(0)=0.
\]
It does not set \(E_K=S_K=0\).
For \(f\in Y_-\), put \(J_f(t)=\int_t^T e^{-U(s)}f(s)\,ds\).
Solving the first-order equation, exchanging the finite integrals, and integrating the geometry derivative by parts gives exactly
\[
\boxed{r_K(f)={\cal W}_{1,K}
 \big((2S_K-E_K)f-2e^US_K'J_f\big).}                                \tag{P4}
\]
The initial boundary vanishes because \(w_K(0)=0\), and the terminal one because \(J_f(T)=0\). The identity
\([e^U(2S_K-E_K)]'=2e^US_K'\)
uses the finite Ward equation.

The maps \({\cal W}_{1,K}:Y_-\to L^2(\rho)\) have a common finite norm \(C_W\), including the charge's \(1/h_i\) factor. Thus
\[
\|r_K(f)\|_2\le C_W\left[
 \|2S_K-E_K\|_\infty+
 \frac{2e^{2\varepsilon}}{\gamma}\|S_K'\|_\infty\right]\|f\|_{Y_-}
 =O(K^{-2})\|f\|_{Y_-}.                                             \tag{P5}
\]
This is an actual source-GNS weak defect estimate. It is not a new normal geometry state.

The predecessor's same fixed witness \(F_U\) obeys
\(\|{\cal W}_1(F_U)\|_2>e^{19000}\).
By P3, every sufficiently large \(K\) obeys
\(\|{\cal W}_{1,K}(F_U)\|_2>e^{19000}/2\).
Hence taking the inverse and source cutoffs consistently does not remove that candidate's large-readout rejection. The threshold is existential, not a newly computed numerical cutoff.

## P4. Proper-clock interface with lapse retained

For the background proper clock
\(\tau(t)=\int_0^t a(s)N(s)\,ds\) and smooth \(g\) supported strictly inside its proper-time interval, take
\(\delta u=w,\delta N=\nu\) at \(N=1\).
Since \(H_{\rm phys}\,d\tau=h\,dt\),
\[
\delta\tau(t)=\int_0^t a(w+\nu),\qquad
{\cal O}_g=\delta\int g(\tau)H_{\rm phys}\,d\tau
          =\int(F_uw+F_N\nu),
\]
\[
J_g(t)=\int_t^T h(s)g'(\tau(s))\,ds,\quad
F_u=-a g'(\tau)+aJ_g,\qquad F_N=aJ_g.
\]
Direct differentiation gives \(F_N'=hF_u\). Therefore a past-anchored gauge direction
\((w,\nu)=(hf,f')\), \(f(0)=0\), gives zero, including when \(f(T)\ne0\), because \(F_N\) vanishes near the future endpoint.

These tests generally do not vanish near the initial slice. They belong to the prepared \(Y_-\) interface, not automatically to INTERIOR_LAPSE's compact-interior test class. Setting \(\nu=0\) gives exactly the earlier proper-clock scale test. This is a mathematically specified readout functional; a local autonomous measuring device and its calibration have not been constructed.

## P5. A useful uniformity, with its boundary

Strong convergence plus a common operator bound implies convergence uniformly on every compact subset of \(Y_-\), by a finite-net argument. Thus P2–P3 are uniform over any family of readout tests precompact in \(Y_-\). For instance a fixed compact proper-time support and a uniform \(H^2\) bound on \(g\) give a bounded \(H^1\) family of \(F_u\) by the displayed multiplier/Volterra formula; the finite-interval Rellich compactness gives the required precompactness.

This does not give operator-norm convergence on the full \(L^2\) unit ball, a cutoff rate, or control for \(K\)-dependent increasingly rapid clocks. No extra automatic certificate is counted for this elementary corollary.
