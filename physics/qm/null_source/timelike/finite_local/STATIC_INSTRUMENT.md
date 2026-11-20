# A common static window after the actual local source instrument

This extends STATIC_PREPARATION.md to a real target-state change. Use either its uniform single-ring input or the explicit new two-center input matching the original actual A in INVARIANT_PREPARATION.md. Apply the same short weak Gaussian pointer coupling, then the complete new mid/out annulus reader. Keep every outcome and use one common static geometry a=A for all of them. There is no record-dependent geometry or new smooth preparation ramp.

## Fixed observable and complete-record convention

Both stress components use the same positive normalization G0=3/(2A^2). Choose an outcome-independent common static Cauchy slice eta_star **after** the short pointer pulse, the finite-probe h support when that realization is used, and the stipulated terminal-reader completion (and any stipulated record distribution). Put tau=lambda*(t_proper-t_proper,star). The normalized smooth positive window g is supported in this future tau interval [0,0.1], of proper duration 0.1/lambda. It is not the old pulse-centered eta=0 window. Translating the window only multiplies the high-mode Fourier factors by phases, so all absolute spectral and displacement bounds below are unchanged. All free waiting phases and zero-mode shear are retained; the terminal reader's physical implementation remains an assumption of the stated instrument.

Define
\[
 C_\rho=\overline{\rho}_g/G_0-1,\qquad
 C_p=\overline p_g/G_0+1/3,\qquad
 {\cal R}^2=\sum_b p_b\langle C_\rho^2+C_p^2\rangle_b .
\]
The pressure is not divided by its own smaller background magnitude. Because the geometry, window and operators are identical for every record, completeness gives this sum exactly as the nonselective target expectation. It does not imply that each conditional mean separately solves the same static mean-SCE.

The short test has zero integrated source charge. Its free-out nonselective channel preserves the full S_0 spectrum. Spatial integration makes all homogeneous-zero/high cross stress terms vanish as operators. The projected-observable difference therefore involves only the high-mode displacement, even though the actual conditional states can have zero/high correlations.

## Actual backaction on both complete quadratic observables

Write the normalized static high stress as sum[e_k a_k^dagger a_k+Re(d_k a_k^2)], with vacuum constants kept in the original renormalized mean. For density, e_k=omega_k/(3pi^2 A^2), d_k=0. For pressure, |e_k|=omega_k/(9pi^2 A^2) and |d_k|<=2omega_k/(9pi^2 A^2), since |g_hat|<=1. Thus for either component
\[
 |e_k|+|d_k|\le K_{\rm st}\omega_k,\qquad
 K_{\rm st}={1\over3\pi^2 A^2}.
\]

Use the same exact random-Weyl nonselective representation as ACTUAL_HISTORY.md. Its retained high displacement sums satisfy
\[
 E_1\le {s\|t'\|_1^2\over2A^2V_0},\qquad
 F\le {s(1+2n)\|t'\|_1\|t''\|_1\over2A^2V_0}.
\]
No old checker is executed: the already current source-bound values are read. For two fields, one stress component's actual perturbation has L2 norm squared at most K_st^2(2F+8E_1^2). Summing both components gives
\[
 \|\Delta(C_\rho,C_p)\|_2
 \le K_{\rm st}\sqrt{4F+16E_1^2}<2.9\,10^{-14}.
\]
The two components' covariance is not needed when defining the sum of their squared norms. There is no extra branch-domination factor because there is one common operator, rather than two feedback geometries.

Minkowski on the complete target/pointer state now yields
\[
 {\cal R}_{\rm actual\ local\ out}
 \le {\cal R}_{\rm single\ prior}
        +K_{\rm st}\sqrt{4F+16E_1^2}
 <1.4\,10^{-6}.
\]
All high modes, the actual pointer backaction and all reader outcomes are included. No high-state reset, conditional product assumption or trace-distance-to-stress bound is used.

## What this additional closure does and does not supply

This is a source-side common-geometry, positive-window certificate for the actual local poststate. The target nonselective mean has the small nonhomogeneous displacement stress already calculated in LOCAL_TENSOR.md; the prescribed static geometry is not an exact full tensor solution for that poststate. The nonzero local anisotropy, pulse Ward obligation and probe/reader/controller sources remain.

The finite kinetic field-probe bridge applies to this bounded finite Gaussian mixture with the same terminal annulus effects. Continuity and the strict margins give a single sufficiently small nonzero coupling for which both source-record TV>0.999 and the quiet input's target joint projected RMS<1.5e-6 hold on this fixed static future geometry. This is a common finite-coupling existence statement, not a computed coupling or device-energy feasibility result.

The global D-clock benchmark in CLOCK_RESOURCE.md is a separately specified protocol. It is not silently inserted before this local annulus certificate; composing both instruments requires carrying its changed actual state and rechecking the relevant record statistics.
