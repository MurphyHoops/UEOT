# Source precision has a clock-resource contract

This is a new mathematical reflection gate after the actual single-ring calculation. It neither replaces that preparation nor constructs a new apparatus. **The Gamma counterexample and its equal-two-point claim compare only the isotropic uniform-angle radial preparations. They do not match the original actual input's nonzero first moments or anisotropic second moments, nor the separate two-center preparation matching that input.** Fix the same canonical reference, C, v, high state, and mean mu. Set r=v/C, L=1+sqrt(3)/4, mu=L+2r. The zero-mode pair has [Q_i,P_j]=i delta_ij.

## A normal-state counterexample to unrestricted single-ring optimality

Put X=P_1^2+P_2^2, alpha=1/(2v), and take an odd integer k>=1. In momentum representation define
\[
 \psi_k(P)=\sqrt{\frac{\alpha^k}{\pi\Gamma(k)}}\,
          X^{(k-1)/2}e^{-\alpha X/2}.
\]
Odd k makes this a polynomial times a Gaussian, hence a normalized Schwartz vector. Since d^2P=pi dX, X has the Gamma(k, rate alpha) law:
\[
 E X=k/\alpha,\quad \operatorname{Var}X=k/\alpha^2.
\]
For k>1, the identity
\[
 \nabla\psi_k=[(k-1)/X-\alpha]P\psi_k
\]
and E(1/X)=alpha/(k-1) give ||grad psi_k||^2=alpha. For k=1 the inverse moment is divergent and must not be used; direct differentiation instead gives alpha^2 E X=alpha. Rotational symmetry and reality then give
\[
 \langle Q_iQ_j\rangle=\alpha\delta_{ij}/2,\quad
 \langle P_iP_j\rangle=k\delta_{ij}/(2\alpha),\quad
 \operatorname{Cov}_{sym}(Q_i,P_j)=0.
\]

Let kappa=alpha C mu=mu/(2r), k_-=2 floor((kappa-1)/2)+1, and k_+=k_-+2. Mix the two vectors with w_+=(kappa-k_-)/2 and w_-=1-w_+. This rank-at-most-two density is positive and normal; its vectors need not be orthogonal. It has E k=kappa and Var(k)<=1. At each fixed original parameter choice, this is one fixed preparation, not a sequence of roots selected in time.

Its complete zero-mode two-point function equals that of the isotropic uniform-angle two-ring and single-ring preparations, with the same high state. This equality excludes the original actual nonzero-m, anisotropic-M input and its separately matched two-center alternative. Yet
\[
 V_{\Gamma}(S_0)=4r^2[\kappa+\operatorname{Var}(k)]
 \le 2rL+8r^2,
\]
approximately half the single-ring variance 4rL+4r^2. Thus the single-ring minimum is restricted to its stated Gaussian-displacement family. This mathematical counterexample uses k of order 10^11; no finite physical preparation protocol or calibrated reader for it has been constructed.

## The resource that changed

Use the self-adjoint dilation generator, on its usual closure from Schwartz space,
\[
 D=\tfrac12\sum_i(Q_iP_i+P_iQ_i)
   =i(P\cdot\partial_P+1),\qquad S_0=X/C.
\]
It obeys [D,S_0]=2iS_0. On psi_k,
\[
 D\psi_k=i(k-\alpha X)\psi_k,\quad
 E D=0,\quad V_k(D)=k,\quad
 \operatorname{Cov}_{sym}(D,S_0)=0.
\]
The Gamma mixture therefore has V_Gamma(D)=kappa=1+L/(2r).

For an original displaced Gaussian block, with P=p+xi and xi~N(0,v I_2),
\[
 D\psi_p=i[1-P\cdot(P-p)/(2v)]\psi_p.
\]
The variance of p.dot(xi)+|xi|^2 is v|p|^2+4v^2. Averaging any radial prior with E R=L gives
\[
 V_{\rm CQ}(D)=1+L/(4r),\qquad
 \operatorname{Cov}_{sym}(D,S_0)=0.
\]
The Gamma source improvement therefore comes with almost twice this clock variance. It preserves W_2, but not the fourth-order resource.

## A conditional bound beyond Gaussian mixtures

For every normal zero-mode state with finite Tr(rho D^2) and Tr(rho S_0^2), the weak commutator extends to the common form domain. One way to see the domain control is the log-radius unitary F(s,theta)=e^s psi(e^s,theta): D becomes i partial_s and S_0 becomes e^{2s}/C. Smooth compact annular functions are dense in their common graph norm. The weak identity extends by this density, and the mixed-state inequality follows by Hilbert-Schmidt Cauchy-Schwarz. This also applies to the reduced zero state of a normal entangled zero/high state. The Schrodinger-Robertson inequality gives
\[
 V_DV_S-\operatorname{Cov}_{sym}(D,S_0)^2\ge\mu^2.
\]
In particular, if the original V_D=1+L/(4r) is also fixed, the single-ring variance exceeds the general bound by only
\[
 (4rL+4r^2)-\frac{\mu^2}{1+L/(4r)}
   =\frac{4r^2L}{L+4r}<4r^2.
\]
This is a conditional quantum bound with an explicitly added resource constraint. Core does not impose that constraint, and the statement is not a claim about arbitrary mixed-state quantum Fisher information.

Free evolution or a known preparation shear changes D to D+c S_0. The determinant above, and
\[
 V_{D,\perp}=V_D-\operatorname{Cov}_{sym}(D,S_0)^2/V_S,
\]
are invariant under that shear. Carrying the covariance prevents a change of reference from masquerading as a resource improvement. It does not imply that D and S_0 are simultaneously readable without disturbance.

On the specified static reference, H_eta=X/(2A^2), so d<E D>/d eta=C mu/A^2. The observable
\[
 T_\eta=A^2D/(C\mu),\qquad T_p=A T_\eta
\]
has unit mean slope in conformal and proper time respectively, and
\[
 \Delta S_0\,\Delta T_\eta\ge A^2/C,\qquad
 \Delta S_0\,\Delta T_p\ge A^3/C.
\]
These are global zero-mode observable statements. A localized clock, its readout, causal distribution, preparation cost and gravitational source are still separate physical tasks. The single-ring source reduction was present before the new annulus reader, which cannot inherit the old low/high posterior feedback contract.

The present shift-symmetric source instrument is not also a clock reader. Its induced effects commute with every P_i and hence with K=X/2. If the unknown reference time is encoded only by exp(-i K theta/A^2), all these source-record probabilities are independent of theta. This follows directly by trace cyclicity and the commuting effects, for arbitrary initial target states. Reading the D-clock requires a distinct reference/readout contract and its source disturbance and apparatus ledger. The existing annulus does not provide it for free.

## A special mixed-state clock calculation, without observable mixture labels

For the Gamma candidate all components share alpha. With K=X/2,
\[
 D\psi_k=-2i\alpha(K-\langle K\rangle_k)\psi_k,\quad
 \{D,\rho_k\}=-2i\alpha[K,\rho_k].
\]
The latter identity is linear in rho and therefore holds for the nonorthogonal mixture without making k an accessible record. At the reference point of the conformal-time encoding exp(-i eta K/A^2), its symmetric logarithmic derivative and quantum Fisher information are
\[
 L_{\rm SLD}=D/(\alpha A^2),\qquad
 J_\eta=\kappa/(\alpha^2A^4).
\]
The reference D spectral measurement saturates that local information bound, with Var(T_eta)=1/J_eta. This special common-SLD argument is needed: the generic pure-state expression 4Var(K)/A^4 would instead overestimate this mixed-state QFI by Var(k)/(alpha^2A^4). The optimal local measurement away from the reference is correspondingly transported; no time-independent global optimality is claimed.

A specified Gaussian D instrument also gives an explicit disturbance benchmark. Let its measurement variance be v_read>0, with Kraus density proportional to exp[-(y-D)^2/(4v_read)]. Nonselectively this is a Gaussian mixture of exp(-i xi D), Var(xi)=1/(4v_read). The adjoint acts as
\[
 \Phi_D^*(S_0)=e^{1/(2v_{\rm read})}S_0,\qquad
 \Phi_D^*(S_0^2)=e^{2/v_{\rm read}}S_0^2.
\]
Thus this finite-precision clock measurement changes the original source law and cannot inherit the source-QND geometry/posterior budget. This is a global normal-state instrument benchmark, not a local-device construction or a universal disturbance formula for every possible clock instrument.

## One compatible global clock budget

A conditional tradeoff is not an exclusion of all useful clocks. As a specific zero-mode benchmark, start with the uniform single-ring input and choose v_read=100 V_D,CQ. After the Gaussian D readout, apply the fixed dilation exp(-icD), c=1/(4v_read), irrespective of the result. All results are retained. The random factor on S_0 is exp[-2(xi+c)], whose expectation is one. Hence the source mean is restored exactly while
\[
 V_{S,\mathrm{out}}=e^{1/v_{\rm read}}V_S
                  +\mu^2(e^{1/v_{\rm read}}-1)<1.58\,10^{-11}.
\]
More generally, the variance increment is at least mu^2/v_read. Restoring the mean does not restore the source law.

The readout y belongs to the pre-restoration reference D measurement. Its calibrated proper-time estimator A^3 y/(C mu) has reference standard deviation
\[
 \sigma_{T_p,\rm ref}={A^3\sqrt{V_D+v_{\rm read}}\over C\mu}<2.3
\]
in model units. This is a reference-point resolution, not a globally unbiased time observable on arbitrary backgrounds.

Nonselectively, all P_iP_j moments return to their input values, Q_iQ_j moments acquire the factor exp(1/v_read), and symmetric Q_iP_j is unchanged. The complete W_2 thus changes. For the minimal massless homogeneous zero modes, stress uses only P_iP_j; the high state remains the same and is still in product with the zero sector. The same exact static **mean** geometry remains valid. Replacing only V_S by the explicitly calculated V_S,out in STATIC_PREPARATION.md gives the full two-projection source-side bound
\[
 {\cal R}_{\rm after\ clock}<1.4\,10^{-6}
\]
on the same positive window. Its numerical upper end is approximately 1.3162e-6.

This is a consistent target-state and global-instrument budget, not a local apparatus or total-gravity completion. The Q covariance change is retained, no old conditional posterior or annulus performance is reused, and the controller work during readout/restoration is not included in the future target-only residual. The much longer positive window, approximately 10009 model units, does not convert this single reference reading into a completed physical clock history.

The restored static mean-SCE statement is nonselective. Individual D outcomes can have different source means; their complete weighted residual second moment nevertheless equals the nonselective quadratic expectation on the one prescribed geometry. No per-record exact mean solution is inferred.

For the future residual in this benchmark, choose a single static Cauchy origin t_star after the stipulated D readout and fixed restoration are complete. The time window is translated to lambda*(t_proper-t_star) in [0,0.1]. Any intervening free wait carries its Q/P shear; the covariance is not reset. This translation leaves source moments and the absolute high-mode Fourier bounds unchanged. The reported <2.3 resolution remains that of the reference D reading, not a new claim of a localized continuously running clock.
