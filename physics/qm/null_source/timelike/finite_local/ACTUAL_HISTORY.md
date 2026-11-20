# Actual short local poststate: a positive-time second-moment closure

The state in this certificate is the actual short local smooth-binary poststate, propagated through TRANSPORT.md. The initial \(U_0,M^2\), zero-mode CQ preparation, and incoming high state are fixed. Neither high modes nor zero/high correlations are replaced after a record. The two future residuals are the **full spatial averages** of the density and isotropic-pressure Einstein equations on a closed FLRW geometry, with the same positive proper-time window as FLUCTUATIONS.md.

This is stronger than the explicit product-reference benchmark in that earlier file. It is still not a local full-tensor Einstein solution: a localized cap measurement breaks spatial \(SO(4)\), and its off-diagonal spatial correlations must eventually source nonhomogeneous metric modes.

## A smooth short filter with a finite high-energy moment

Choose the time filter explicitly as
\[
t=u_{\pi/4}*u_{\pi/16}*\kappa,
\]
where \(u_\ell\) is the normalized uniform block of width \(\ell\), and \(\kappa\) is any fixed even nonnegative \(C^\infty_c\) probability bump of radius \(\pi/32\). This is exactly a member of the earlier time-filter contract: the inner convolution has radius \(\pi/16\). It retains temporal support \(3\pi/8\), all earlier source coefficients and locality bounds, and gives
\[
D_1=\|t'\|_1\le8/\pi,\qquad D_2=\|t''\|_1\le256/\pi^2<26.
\]
Consequently
\(\sum\omega^3|b_k|^2|\widehat t(\omega)|^2\le D_1D_2/V_0\).
This follows from
\(\omega^3\min(D_1^2/\omega^2,D_2^2/\omega^4)\le D_1D_2\), not an unverified differentiability claim about a bump.

## The exact nonselective high channel and its moments

The specified Gaussian pointer gives an exact random-Weyl nonselective high channel. Each field has a centered real displacement variable \(\xi\), with variance \(s=1/(4v_m)\), and the two fields' \(\xi\)'s are independent. The out displacement amplitudes obey
\[
|d_k|^2={\omega_k|b_k|^2|\widehat t(\omega_k)|^2\over2A^2}.
\]
The same displacement is propagated through the same preparation and future KG map; it is not replaced by an independent future displacement.

For either future normalized quadratic residual, its pullback has the form
\[
O=\sum_k[e_kN_k+\tfrac12(d_k^{\,O}a_k^2+\overline{d_k^{\,O}}a_k^{\dagger2})]+\text{constant},
\quad |e_k|+|d_k^{\,O}|\le K\omega_k,\quad K={46\lambda^2\kappa_b^2\over\pi^2}\le{46\lambda^2\over\pi^2}.
\]
The coefficient uses the transported energy bound \(69p\), whose strict margin is verified in TRANSPORT.md. Under a Weyl displacement, \(O\) changes by \(\xi L+\xi^2C\). Define
\[
E_1=s\sum\omega|d_k|^2\le{sD_1^2\over2A^2V_0},\qquad
F=s\sum\omega^2|d_k|^2(2n_k+1)
 \le{s(1+2n)D_1D_2\over2A^2V_0}.
\]
For two fields, the added \(L^2\) norm squared is at most
\(K^2(2F+8E_1^2)\): the Gaussian fourth moment gives 3 in each field, and the cross contribution between two fields gives the remaining 2. The actual thermal shells are included.

The smooth reader is complete, so \(\sum_b{\cal I}_b=\Phi\) exactly. For any positive branch operator \(X_b\),
\[
\sum_b\operatorname{Tr}{\cal I}_b(\rho)X_b
 \le\sum_b\operatorname{Tr}\Phi(\rho)X_b.
\]
Apply this to each branch's squared high residual. Two flags and two equations give the added vector bound
\[
\Delta_{\rm local}\le K\sqrt{8F+32E_1^2}<5\,10^{-12}.
\]
This is a genuine unbounded-stress second-moment estimate. Trace-distance gentleness alone would not justify it.

## Complete bound with the real correlations retained

Use an outcome-weighted Hilbert-space \(L^2\) norm and Minkowski, rather than assuming zero conditional covariance. With \(D_{\rm binary}\) from SMOOTH_BINARY.md, \(b_\rho,b_p\) from the full renormalized mean calculation, and \(\delta_{\rm prep}< (2/3)10^{-5}\lambda^2\),
\[
\begin{split}
\|({\cal C}_\rho,{\cal C}_p)/\bar G\|_{L^2}
\le{}&\sqrt2\,{\beta\over\mu}\sqrt{D_{\rm binary}}
 +\sqrt{(b_\rho+\delta_{\rm prep})^2+(b_p+\delta_{\rm prep})^2}\\
&+\sqrt2\,\lambda^2\sqrt{1600^2+8000^2}
 +K\sqrt{8F+32E_1^2}
 <7.6\,10^{-6}.
\end{split}
\]
The second \(\sqrt2\) is the price of two-branch positive domination for the high operator. The deterministic mean term has no such factor; the flag probabilities sum to one. No density/pressure cross covariance is set to zero. No zero/high conditional cross covariance is set to zero. The common normalization is positive on every branch.

The proper future interval is \(0\le t\le0.1/\lambda\), approximately \(10009\) in the model units. This is a different specified geometry and a much longer positive window than the old fast-mode short interval. Therefore the result is not a like-for-like experimental improvement over the old residual percentage.

## The remaining physical boundary

This closes one finite, checkable statement: the actual local instrument, its complete two-flag record, one lawful transported quantum state, and both spatially projected future residual moments are jointly controlled at fixed \(U_0,M^2\).

It does not close the controller stress during preparation, the pointwise \(0i\) and anisotropic \(ij\) equations, the retarded metric response and its fluctuations, or the existence of an exact nearby SCE solution. Those are the next physical tasks. A small residual alone is not an inverse-function or stability theorem for the higher-derivative semiclassical equations.
