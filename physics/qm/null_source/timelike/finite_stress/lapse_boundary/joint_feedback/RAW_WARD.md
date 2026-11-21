# Raw joint matter evolution and its exact energy Ward identity

This page concerns the original two minimally coupled massless fields at one fixed finite spatial cutoff \(K\), the original raw canonical variables, and the same complete joint evolution established in the predecessor. It does not replace a quantum expansion operator by its mean. The AE geometric terms, the continuum limit of joint geometry, and the apparatus stress remain separate.

## W1. Generator, frame, and observables

Put \(a=Ae^u\), \(\kappa>0\), and use a compact \(u\) interval with \(g_K(u)\ne0\). Remove the already fixed pure geometry phase \(S_g\) from the raw representation. As explained in WEIGHTED_EVOLUTION, this leaves the same raw source reduction, not a new source state. On the common compact-\(\kappa\), Schwartz-source test space the generator is
\[
 H_{\rm raw}(u)=H_G(u)+\kappa^{-1}H_s(a),\qquad
 H_G=\alpha A_\eta+d_0\kappa^{-1}+d_1\kappa+d_3\kappa^3,\quad
 \alpha=(2g_K)^{-1},
\]
\[
 A_\eta=-\partial_\kappa(\kappa^{-1}\partial_\kappa)
                  +(\eta-\tfrac34)\kappa^{-3},\qquad \eta\ge-\tfrac14.
\tag{W1}
\]
The declared Friedrichs principal domain and all the original \(d_j\), including the fixed nonzero \(U_0\), are retained. The full evolution is not assumed to transport raw strong operator domains.

For real modes, including both species and their \(k^2\) degeneracies, define
\[
 T=\sum_r\frac{P_r^2}{2a^2},\quad
 V=\sum_r\frac{a^2\omega_r^2\phi_r^2}{2},\quad
 H_s=T+V,\qquad \omega_k^2=k^2-1 .
\]
The zero modes have \(\omega_1=0\). The spatially averaged raw energy density and pressure are
\[
 \rho_s=\frac{H_s}{V_0a^4},\quad
 p_s=\frac{T-V/3}{V_0a^4},\qquad V_0=2\pi^2 .
\tag{W2}
\]
These are raw finite-cutoff source observables. Neither the finite vacuum energy nor its joint contribution has been silently removed.

## W2. Exact weighted source equation

For a normal joint density \(\varrho\), let
\[
 \sigma=\operatorname{Tr}_G\varrho,\qquad
 \tau=\operatorname{Tr}_G XX^\dagger,\qquad
 X=(\kappa^{-1/2}\otimes I)\varrho^{1/2}.
\tag{W3}
\]
When the indicated comparison form is finite, \(X\) is Hilbert–Schmidt, \(\tau\ge0\), and \(\operatorname{Tr}\tau=\langle\kappa^{-1}\rangle\). This sandwich definition avoids cyclically tracing an undefined unbounded product.

WEIGHTED_EVOLUTION proves the weak equation on the common form class and trace-norm \(C^1\) regularity on \(Q_6\):
\[
 \boxed{\sigma'=-i[H_s,\tau].}
\tag{W4}
\]
It does not set \(\tau=\sigma/h\). In particular the old prescribed-history equation \(\sigma_{\rm old}'=-i[H_s,\sigma_{\rm old}]/h\) is an additional relation, not a consequence of the joint action.

## W3. Energy conservation on the actual joint class

The exact identities
\[
 H_s'=-2T+2V,\qquad [H_{\rm raw},H_s]=0
\tag{W5}
\]
hold at a fixed \(u\). The second identity includes \(H_G\); it acts on the geometry tensor factor.

Here is a domain argument, rather than an unrestricted formal trace cancellation. Use the bounded source observable
\[
 Z_\Lambda=H_s(1+H_s/\Lambda)^{-1}.
\]
For finite \(K\), source graph norms of the positive quadratic \(1+H_s(a)\) and the fixed oscillator/zero-momentum energy are equivalent on a compact positive \(a\) interval. Thus \(Z_\Lambda\) and its resolvent preserve the common source comparison domains. They commute with the instantaneous complete generator on the common core and hence in the weak form identity. Their explicit derivative is the bounded-form resolvent sandwich
\[
 Z_\Lambda'=(1+H_s/\Lambda)^{-1}H_s'
                         (1+H_s/\Lambda)^{-1}.
\]
Since \(-2H_s\le H_s'\le2H_s\), the absolute expectation of this derivative is bounded by \(2\langle H_s\rangle\), uniformly in \(\Lambda\). The latter is continuous and bounded on compact intervals of the common energy evolution. The spectral monotone limit for \(Z_\Lambda\), form approximation for its derivative, and dominated convergence first give the integrated energy identity. Continuity of its right-hand side then gives
\[
 \frac{d}{du}\langle H_s\rangle=\langle-2T+2V\rangle,\qquad
 \boxed{\frac{d}{du}\langle\rho_s\rangle
              =-3\langle\rho_s+p_s\rangle.}
\tag{W6}
\]
The actual compact-\(\kappa\), Schwartz-source preparations satisfy every \(Q_p\) required here. The statement is not asserted for an arbitrary normal density without the stated energy/domain control.

For the free zero modes all bounded Borel functions of their raw momenta strongly commute with the source and geometry differential expressions, preserve the forms, and commute with the propagator by weak uniqueness. Their full momentum law is therefore conserved. Their stress still changes through the explicit powers of \(a\).

## W4. Pressure carries joint correlations

Define the finite-cutoff weighted dilation
\[
 D_\Omega=\sum_{r:\,k\ge2}\frac{\omega_r^2}{2}
                         (\phi_rP_r+P_r\phi_r).
\]
The canonical commutator gives
\[
 [T,V]=-iD_\Omega,\qquad
 i[H_s,T-V/3]=-\frac43D_\Omega .
\tag{W7}
\]
For a normal initial density of finite \(Q_6\) energy, the pressure identity holds throughout the compact interval. Here is the needed cutoff argument. Choose a smooth source spectral cutoff \(\chi_R(\lambda)\) and let \(O_R=\chi_RO\chi_R\), with \(O=p_s\) or \(\rho_s\). These bounded operators preserve \(Q_3\), so the weak product rule applies. The source ladder graph bounds give \(\|Of\|+\|O'f\|+\|H_sf\|\le C_J\|\lambda f\|\). Both \(\Psi(u)\) and \(\beta(u)=\kappa^{-1/2}\Psi(u)\) are continuous in \(D(\lambda)\) by E5. Write the commutator expectation as \(i(\langle H_s\beta,O_R\beta\rangle-\langle O_R\beta,H_s\beta\rangle)\). Graph approximation gives \(O_R\beta\to O\beta\), uniformly on the compact set of trajectory vectors in \(D(\lambda)\); the means and their explicit derivatives converge in the same way. The bounded cutoff identities therefore converge with their derivatives. The common-core canonical commutator extends by \(D(\lambda)\) form density. Hence
\[
 \frac{d}{du}\langle p_s\rangle
 =\frac{\langle-6T+\tfrac23V\rangle}{V_0a^4}
       -\frac4{3V_0a^4}\operatorname{Tr}(\tau D_\Omega).
\tag{W8}
\]
No global second inverse-\(\kappa\) moment is invoked. If the initial full source marginal is the actual rank-two thin state, its two support vectors are Schwartz. Every source-only \(\lambda^p\) expectation is then fixed and finite for every normal joint extension. Thus finite initial \(Q_3\) energy already implies finite initial \(Q_p\) energy for every finite \(p\); the pressure identity covers all such regular extensions, including entangled ones.

For a product initial preparation with the old raw source state and \(I_1=\langle\kappa^{-1}\rangle\), comparison with the old prescribed history yields
\[
 \left.\delta\langle p_s\rangle'\right|_0
  =-\frac4{3V_0A^4}(I_1-h_i^{-1})
                         \langle D_\Omega\rangle_{\rm old}.
\tag{W9}
\]
PRESSURE_WITNESS evaluates the last expectation on the actual transported incoming state. It also controls all joint extensions with the stated same geometry probability law; it does not replace the state by a static vacuum.

## W5. What this closes

The original joint source has a legitimate conservation law and an explicit pressure-feedback term. Conserved energy balance does not provide an autonomous evolution for \(\sigma\): the weighted state \(\tau\), and subsequently geometry currents, remain necessary. The finite-cutoff raw pressure result is not a theorem excluding every renormalized joint mean history, every clock, or every physical apparatus.
