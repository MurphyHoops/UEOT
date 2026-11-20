# Same-kernel conditional state, stress and fluctuations

Let \(B=(B_1,\ldots,B_m)\) be commuting future probe quadratures. Fix a finite Gaussian Lüders reader with positive noise matrix \(\nu\). For each actual latent \(p\) block of the CQ preparation, the evolved joint target/probe state is Gaussian; its mean and covariance are obtained with the exact same Green map from KINETIC_PROBE.md. The classical distribution of \(p\) is not included as if it were an intrinsic Gaussian variance.

Write \(b_p=E_pB\), \(S=\operatorname{Cov}_{\rm sym}(B,B)+\nu\),
\(c_a(x)=\operatorname{Cov}_{\rm sym}(X(x),B_a)\), and
\(d_a(x)=(1/i)[X(x),B_a]\). Completing the Gaussian square, including the noncommuting reader action, gives
\[
p(y|p)=N(b_p,S),\quad m_{p,y}=m_p+cS^{-1}(y-b_p),
\]
\[
C_{p,y}=C-cS^{-1}c^T+\tfrac14d\nu^{-1}d^T.
\]
For the commuting **out target algebra**, \(d=0\). For the probe, the last term is real reader backaction and cannot be deleted. Averaging over \(y\) restores
\(C_{\rm ns}=C+\tfrac14d\nu^{-1}d^T\). For a canonical pure Gaussian probe this reproduces a conditional uncertainty product exactly \(1/4\), independently checking the coefficient.

Update the actual latent measure by
\(\pi(dp|y)=p(y|p)\pi(dp)/\int p(y|p)\pi(dp)\).
The full conditional state is the mixture of these Gaussian blocks. It is generally not Gaussian. For the two smooth flags one instead integrates the same kernels with the weights \(e_\pm(y)\), without creating a fine record.

Each finite-record covariance difference is smooth and finite rank. Thus the conditional state is Hadamard for the specified incoming preparation. This is not a statement about arbitrary normal states, nor does a future conditional state become the actual premeasurement state when one formally evolves it backward.

## Renormalized target stress from the same kernels

Let \(B_T(f,g)\) denote the polarized classical stress bilinear, and \(L_T(m,c)=2B_T(m,c)\). With \(r=S^{-1}(y-b_p)\), \(K=S^{-1}\), the free-out target stress change within each block is
\[
\Delta t_{p,y}=
 \sum_a r_aL_T(m_p,c_a)
 +\sum_{ab}(r_ar_b-K_{ab})B_T(c_a,c_b).
\]
The state-independent free-out AE counterterms cancel in this difference. The interacting region needs the new renormalization conditions of RENORMALIZATION.md.

For each Gaussian block, the stress-noise kernel follows by Wick's rule: two cross pairings of the connected Wightman function, plus the terms bilinear in the mean and linear in that Wightman function, with the stress differential operators applied. The actual CQ noise is
\[
N_y=E_{\pi(\cdot|y)}N_{p,y}
       +\operatorname{Cov}_{\pi(\cdot|y)}(t_{p,y},t_{p,y}').
\]
The second term is essential. Applying Wick's rule to the entire CQ mixture would miss it.

The nonselective retarded covariance gives the same mean stress by coincidence limits. The probe block supplies its energy and correlations. After the interaction, a Gaussian Lüders reading adds the probe stress \(T[E h]/(4\nu)\) for one read quadrature; the corresponding noise follows from the same updated covariance. The reader's own/controller's stress is still a separate part of the total source.

## Conditional inference is not a causal gravity prescription

For one Gaussian block let \(q=(y-b_p)/S\). In a region spacelike to the interaction, the commutator vanishes, but the correlation \(c(x)\) need not vanish. There
\[
\Delta t_y=qL_T(m_p,c)+(q^2-1/S)T[c].
\]
Its average is zero. Its record covariance is exactly
\[
E_y[\Delta t_y(x)\Delta t_y(x')]
 ={L_T(x)L_T(x')\over S}
  +{2T[c](x)T[c](x')\over S^2}.
\]
Thus conditional expectations can change in a spacelike region even though the nonselective local state has not changed. This is ordinary conditional correlation, not a retarded local response.

Consequently a prescription that simply makes every such posterior expectation an immediately readable classical metric source has not established causality. It would need a complete causal measurement-and-feedback model, with the record physically available where it drives a source. For the actual bounded latent means, large-record quadratic terms persist and cannot be erased by merely mixing \(p\).

At the interacting quantum level, define \(O_\chi=-g_c\nabla\phi\cdot\nabla\psi\), including its required counterterm completion. The Ward identity has the structure
\(\nabla^\mu N_{TT,\mu\nu}=(\partial_\nu\chi)N_{O_\chi T}\).
The total source becomes transverse only when the controller noise and all cross terms are also included. The next closed system must use the same renormalized in-in functional for the mean equations, its retarded Hessian, and the full block noise of \((T,O_\chi)\).


For compact vector tests \(v\), supported away from the initial preparation boundary or with that preparation transformed as well, the centered joint Ward identity is
\[
\int[t_{ab}\nabla^av^b+o\,v^b\nabla_b\chi]=0.
\]
The block covariance of \((t,o)\) therefore has these test directions in its null space. A jointly Gaussian stochastic representation of this **second cumulant** satisfies \(\nabla^a\xi_{ab}=\zeta\nabla_b\chi\) distributionally; it reproduces these second moments, not the full generally non-Gaussian CQ stress statistics.

For an ungauge-fixed full in-in Hessian, \(K_{AB}R_v^B=0\) requires an on-shell total background. On the present off-shell preparation, an additional term proportional to the mean Euler equations remains. Contact/local response terms must come from varying the same action. Fixed-background c-number counterterms cancel in centered noise but change the mean and local response, so noise measurements alone do not fix the missing finite counterterm coefficients.
