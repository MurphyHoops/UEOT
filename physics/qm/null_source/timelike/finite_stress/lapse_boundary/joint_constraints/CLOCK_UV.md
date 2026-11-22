# JC21 — The bare compact clock gate has no direct fixed-coupling continuum profile

## Precisely which candidate is tested

Use the normal Fock/wave-packet clock representation and the actual spectral fields X_K in CLOCK_ACTUATOR. Keep a nonzero fixed g and the bare bounded function F_j(gX_K(x)), with F_j smooth and compactly supported. No Wick functional or interacting renormalized composite has been substituted. The following is a rejection of a direct continuum use of that bare gate, not a no-go theorem for all nonlinear clocks.

## 1. Strong zero limit of the bounded bare gate

Fix low modes through J>=1 and take a vector depending on finitely many clock modes, tensor the higher-mode vacuum. At a point x, the independent high-mode coordinate is a real Gaussian with variance
\[
 \sigma_{J,K}^2={1\over2V_0}\sum_{k=J+1}^K{k^2\over\sqrt{k^2-1}},
\]
where the massless zero mode is already among the low modes. The addition theorem makes the variance independent of x. Conditioning on all low-mode coordinates and changing variable in the Gaussian convolution gives
\[
 \|F(gX_K(x))\psi\|^2
 \le {\|F\|_{L^2(\mathbb R)}^2\over
              \sqrt{2\pi}|g|\sigma_{J,K}}\,\|\psi\|^2 .          \tag{1}
\]
The bound is independent of the low-mode coordinate and of the coherent clock mean t/g. Since sigma diverges, (1) tends to zero. Finite-cylinder vectors are dense, and ||F(gX_K)||<=||F||infinity uniformly. Therefore
\[
 F(gX_K(x))\longrightarrow0\quad\hbox{strongly}.
\]
For a smooth spatial smearing f, Minkowski's inequality and the same uniform bound prove strong convergence of integral f(x)F(gX_K(x)) dV to zero as well.

This does not license multiplying the strong limit through the unbounded fields Y_K Phi_K^2 or inferring that the entire Hamiltonian becomes free. Those products require their own domains and renormalization.

## 2. Actual high-mode scale and the alternative resource cost

For k>=2,
\[
 k\le {k^2\over\sqrt{k^2-1}}\le k+{1\over k}.
\]
The upper bound follows by squaring (1-t)^(-1/2)<=1+t for 0<=t<=1/4. Hence
\[
 {K(K+1)-J(J+1)\over4V_0}
 \le\sigma_{J,K}^2
 \le {K(K+1)-J(J+1)\over4V_0}
       +{{\cal H}_K-{\cal H}_J\over2V_0},
\]
and \(\sigma_{J,K}^2/K^2\to1/(4V_0)\).

One possible way to preserve the classical bare-profile approximation is to require \(g_K\sigma_{J,K}\to0\); the Lipschitz bound then controls F(t+g_K xi)-F(t). This sufficient condition forces g_K to zero. The clock kinetic cost \(V_0/(2g_K^2)\) consequently has no uniform upper bound.

More quantitatively, **if the declared clock-accuracy contract is**
\(g_K^2\sigma_{J,K}^2\le\delta_t^2\), then necessarily
\[
 E_{\rm clock,cl}\ge{V_0\sigma_{J,K}^2\over2\delta_t^2}
 \ge{K(K+1)-J(J+1)\over8\delta_t^2}.                            \tag{2}
\]
Equation (2) is a conditional resource lower bound for this bare point-clock comparison. It is not a universal energy-versus-information bound and does not follow merely from a positive binary gap.

The limit at fixed g already makes the reference mean bare gate tend to zero for every fixed t. A nonzero compact target profile cannot survive that unmodified fixed-g limit.

## 3. Two sharper diagnostics on the declared initial Gaussian family

For a fixed nonzero normalized bare profile, the classical accuracy
condition has a necessary version. Let t_* be a positive maximum point
of F_0, with maximum M. If along a subsequence the Gaussian clock width
a_K=|g_K| sigma_X,K is at least delta>0, then
\[
 {\mathbb E}F_0(t_*+a_K Z)
 \le M\{1-\Pr[|Z|>(.2+|t_*|)/\delta]\}<M .
\]
Thus even convergence at that maximum requires g_K sigma_X,K to zero.
Since sigma_X,K is asymptotic to K/(2 sqrt(V_0)), the clock energy
divided by K squared diverges. This statement concerns a fixed nonzero
or normalized program profile. If the program amplitude itself tends
to zero and only absolute source error is tested, the conclusion does
not follow.

The bounded strong-zero limit must not be pushed through the full
interaction. Put
\[
 L_F=\int_{\mathbb R}(F_0(s)^2+F_1(s)^2)\,ds>0 .
\]
At fixed nonzero g, the actual declared initial product Gaussian has
\[
 {\mathbb E}\sum_jF_j(gX_K)^2
 \sim {2\sqrt{V_0}L_F\over\sqrt{2\pi}|g|K},\qquad
 v_{\Phi,K}\sim {K^2\over4V_0}.
\]
The first asymptotic is dominated convergence of its explicit Gaussian
density on the compact profile support. The initial quartic mean is
therefore
\[
 \langle H_{\rm quartic,K}\rangle
 \sim {3|g|L_F\over32\sqrt{2\pi V_0}}K^3>0 .
\]
The cubic spatial mean is still exactly zero by integral Z=0.
This is a raw, unrenormalized interaction diagnostic. It neither proves
a renormalized theory impossible nor identifies a full Hamiltonian limit.

## 4. A singular body limit is different from a complete apparatus limit

For fixed program u in the declared ball, fixed finite comparison time,
and the same smooth encoding/readout, the point-variance bounds scale
as O(K^2). Consequently the proved Duhamel constants are
C_1,K=O(K^3), C_2,K=O(K^4). Taking a comparison sequence
g_K=o(K^-3) makes its actual reduced body density approach the prescribed
quadratic reference in trace distance. The latter has the already proved
actual full-field limit, so a reduced body process and bounded record can
survive this singular comparison.

This changes the bare coupling with K and sends the controller's mean
energy and complete energy-variance lower bound to infinity. It is not
the continuum limit of a fixed-g theory or a finite-resource apparatus.

There is a separate normal-state obstruction for this specific initial
recipe. At t_i=-1 the clock zero-mode packet has variance a=4 and means
qbar=-sqrt(V_0)/g, pbar=sqrt(V_0)/g. For two positive couplings its overlap
modulus is exactly
\[
 |\langle\chi_g,\chi_{\tilde g}\rangle|
 =\exp\left[-V_0\left({1\over8a}+{a\over2}\right)
                    (g^{-1}-\tilde g^{-1})^2\right].
\]
As g_K goes to zero these rank-one clock densities cannot be trace-norm
Cauchy: pairs arbitrarily far out in the sequence have arbitrarily
separated centers. A complete initial normal density limit would imply
a Cauchy clock marginal by contractivity of partial trace, so it fails
for this fixed packet recipe. A reduced body limit or a different
dressed/renormalized apparatus state family is not excluded.

## 5. Consequence for the completed finite-K construction

CLOCK_ACTUATOR and ACTUATOR_MEANS remain valid at every declared fixed K. Their constants and normal states do not themselves establish a continuum apparatus. For the bare gate just tested, taking K to infinity at fixed g loses the prescribed profile; shrinking g with K under the stated precision contract drives controller energy upward. Neither procedure supplies the missing renormalized local interaction, metric/source variation or total Ward/noise limit.

A next continuum candidate must explicitly define a renormalized composite F_ren(X), fix its new counterterms and initial state, retain the interaction/controller stress, and reprove programming and instrument bounds. The word “local” in the classical action does not replace this construction.
