# The apparatus needs new finite renormalization data

For the finite kinetic probe, use \(g_c\) for the coupling, to avoid confusing it with the cosmological rate \(\lambda\). Define \(A_\chi=\Box\chi\), \(B_\chi=(\nabla\chi)^2\). The exact rescaled potentials are
\[
V_\pm={\pm g_cA_\chi\over2(1\pm g_c\chi)}
       -{g_c^2B_\chi\over4(1\pm g_c\chi)^2}.
\]
The sum is even in \(g_c\), and direct expansion yields
\[
\tfrac12\sum_\pm V_\pm^2
 ={g_c^2\over4}(\Box\chi)^2+O(g_c^4),\qquad
\sum_\pm V_\pm=-g_c^2[\chi\Box\chi+\tfrac12(\nabla\chi)^2]+O(g_c^4).
\]

In the convention \(D=-(\nabla^2+E)\), the four-dimensional heat-kernel coefficient contains
\((4\pi)^{-2}\operatorname{tr}[\tfrac12E^2+RE/6+\Box E/6]\), besides pure curvature. Here \(E_\pm=-V_\pm\). Therefore one target/probe pair contributes the new density
\[
{g_c^2\over(4\pi)^2}\left[
 {(\Box\chi)^2\over4}
 +{R\over6}\big(\chi\Box\chi+\tfrac12(\nabla\chi)^2\big)
 +{\Box\over6}\big(\chi\Box\chi+\tfrac12(\nabla\chi)^2\big)
 \right]+O(g_c^4).
\]
On a flat background with compactly supported \(\chi\), the total derivative integrates to zero. In zeta regularization \(W_s^{\rm pole}=-a_4/(2s)\), so the one-pair pole is
\(-g_c^2[8s(4\pi)^2]^{-1}\int(\Box\chi)^2\). The actual two-pair apparatus doubles this contribution.

This identifies a counterterm, not a failure of renormalization. Its finite coefficient \(c_\chi(\mu)\) needs a new normalization or matching condition. The old free-field AE scale \(\mu=1\) and vanishing added pure-curvature finite terms do not fix a term that vanishes at \(\chi=0\).

## Both sides of the Ward identity must change

For
\(S_{\rm ct}=c_\chi g_c^2\int\sqrt{-g}(\Box\chi)^2\), put \(F=\Box\chi\). Variation gives
\[
E_{\chi,\rm ct}=2c_\chi g_c^2\Box^2\chi,
\]
\[
T_{\mu\nu}^{\rm ct}=c_\chi g_c^2
 [4\nabla_{(\mu}F\nabla_{\nu)}\chi
   -g_{\mu\nu}F^2-2g_{\mu\nu}\nabla_\alpha F\nabla^\alpha\chi],
\quad
\nabla^\mu T_{\mu\nu}^{\rm ct}=E_{\chi,\rm ct}\nabla_\nu\chi.
\]
The symbolic script independently checks this identity on a nontrivial time-dependent flat profile: \(\rho_{\rm ct}/(c_\chi g_c^2)=\ddot\chi^2-2\dot\chi\dddot\chi\), and its time derivative agrees with the fourth-order controller force. Adding the stress term while leaving the controller equation unchanged would break the identity.

These terms preserve target/probe constant shifts and internal species covariance. They do not invalidate the local CP/QND measurement construction. They change the physical inputs needed for its gravitational completion.

The local heat-kernel coefficient is used only for renormalization structure. No global analytic Wick rotation of an arbitrary smooth compact pulse is assumed. It does not provide the real-time retarded or noise kernel. Those must come from the same renormalized in-in functional as the mean equations.

Source: D. V. Vassilevich, *Heat kernel expansion: user's manual*, arXiv:hep-th/0306138v3, Eqs. (2.2), (2.31), (4.28), and Sec. 2.3 on the Lorentzian local coefficients. The expansion and stress variation above are explicit computations for this apparatus action.
