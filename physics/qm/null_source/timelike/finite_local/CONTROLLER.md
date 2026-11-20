# The next physical closure: one constrained total-source history

The finite local state/moment certificate is now complete within its stated averaged geometry contract. Refining its already small readout error is not the main remaining task. The apparatus and local metric must satisfy one causal initial-value problem.

## A concrete sign test at the original initial geometry

Keep the original exact static mean geometry \(a=A,H=\dot H=0\), its original \(\mu\), and its fixed AE scheme. For an ideal long pure-\(P\) flag that leaves the high state unchanged,
\[
\Delta\rho_z=\Delta p_z={M^2(\mu_b-\mu)\over2A^6}.
\]
If the geometry is kept fixed, the extra source must obey
\(\rho_{\rm ctrl}=p_{\rm ctrl}=-\Delta\rho_z\).
For the high ring \(\mu_b>\mu\), this violates the null energy condition. It excludes a canonical classical positive-kinetic scalar, or an NEC fluid, **under this fixed-geometry and unchanged-high-state contract**.

The actual short pulse changes high modes, so the two-number NEC formula cannot simply be copied to it. A different rigorous bound does apply to its spatially averaged energy: the normal-ordered static high Hamiltonian is nonnegative in every normal state. At most the old thermal density \(4n\sqrt3/(\pi^2A^4)\) can be removed. Thus the required additional averaged energy satisfies
\[
\rho_{\rm ctrl}\le-
 \left[{M^2(\mu_+-\mu)\over2A^6}
       -{4n\sqrt3\over\pi^2A^4}\right].
\]
The bracket is strictly greater than \(0.1\,[3/(2A^2)]\). A nonnegative-energy classical controller alone cannot supply it while the old geometry stays fixed. Negative energy by itself does not prove negative NEC: the short-pulse pressure has additional pair terms, and its actual tensor must be calculated.

These are admission tests for specific contracts. They do not exclude a different common metric, a correctly constrained earlier correlated preparation, quantum negative energy, or a different total matter sector. Each alternative has its own state, energy and causal constraints to prove.

## Why a new branch cannot be pasted in for free

A jump from \(A\) directly to a different \(a_b(0)\) makes the induced spatial metric discontinuous. If only \(H\) jumps while \(a\) is continuous, the leading second-order Einstein equation
\(p=-\dot H-(3H^2+a^{-2})/2\) requires surface pressure \(-\Delta H\,\delta(t-t_0)\). This formula diagnoses the missing stress in the leading Einstein contract; it is not a thin-shell solution of the full higher-derivative AE semiclassical equations, where non-smooth curvature creates further distributional difficulties.

More generally, for \(T=\Theta(-f)T_-+\Theta(f)T_+\),
\[
\nabla_\mu T^{\mu\nu}
 =\delta(f)\,\partial_\mu f\,[T^{\mu\nu}]
\]
when both open pieces are separately conserved. Separate conservation does not imply conservation of the pasted history. Conditional inference about an entire history is different from physically switching histories after a measurement.

The smooth transport constructed here avoids distributional jumps. But defining \(T_{\rm req}=G/2-T_{\rm actual}\) on that prescribed metric is only an algebraic target: it does not establish that a specified controller realizes it.

## A minimal proposal that exposes the remaining inputs

One candidate is a dimensionless real controller \(\chi\) with
\[
S_\chi=-{M_\chi^2\over2}\int\sqrt{-g}
 [(\nabla\chi)^2+m_\chi^2\chi^2],\qquad
\kappa(\chi)=\kappa_{\max}\tanh\chi,\quad0<\kappa_{\max}<1,
\]
and interaction \(-\kappa(\chi)\sum_i\nabla\phi_i\cdot\nabla\psi_i\).
The saturation keeps both kinetic eigenvalues \(1\pm\kappa\) positive for all real \(\chi\), while preserving independent target/probe shifts. This is an explicit added model, not a result derived from Core.

For a prescribed c-number \(\chi\), the exact two Green kernels above still apply after replacing \(g_c\chi\) by \(\kappa\). An autonomous controller must instead evolve from its incoming Cauchy data and its coupled equation; an arbitrary compact pulse is not automatically a solution. One may seek a finite-window approximation to the desired pulse, but must bound its tails and resulting errors. Zero initial \(\chi,\dot\chi\) forces a zero solution only if that zero profile solves the complete driven equations; a coupled force cannot be omitted from a uniqueness argument.

If \(\chi\) is quantized, the nonlinear interaction is no longer Gaussian. The exact fixed-\(\chi\) kernels then require a controlled approximation, with an explicit effective-theory regime or another genuine non-Gaussian construction.

## Mean, response and noise must use the same action and state

Define the in-in influence functional by
\[
e^{i\Gamma_{\rm IF}[g_\pm,\chi_\pm]}
 =\operatorname{Tr}\big(U_{g_+,\chi_+}\rho_{\rm in}U^\dagger_{g_-,\chi_-}\big).
\]
The actual CQ prior, incoming probe covariances and all finite counterterms belong to this one functional. On the physical branch the mean equations are
\[
G_{\mu\nu}=2(T^\chi_{\mu\nu}+\langle T^{\rm fields}_{\mu\nu}\rangle_{\rm ren}
                     +T^{\rm ct}_{\mu\nu}),\quad
M_\chi^2(\Box\chi-m_\chi^2\chi)+O_\chi=0.
\]
Diffeomorphism invariance gives
\(\nabla^\mu\langle T_{\mu\nu}^{\rm fields+ct}\rangle=O_\chi\nabla_\nu\chi\).
The controller equation supplies the opposite divergence.

At second order use the retarded Hessian of this same functional and the full connected symmetrized noise block of \((T_{\mu\nu},O_\chi)\). Keeping only \(N_{TT}\), or supplying only classical mean work, does not close the fluctuating Ward identity. Gaussian measurement records enter through CP insertions for joint probabilities and physically available causal feedback, not an instantaneous replacement of the global source by a posterior.

The input contract still needs \(M_\chi,m_\chi,\kappa_{\max}\), incoming controller data and energy, the complete probe Hadamard/zero covariances, spatial/species references, the reader dynamics, and finite counterterm conditions including \(c_\chi\). If higher-derivative terms are treated as an effective theory, specify the cutoff and order reduction; if treated as fundamental, audit the additional degrees of freedom and stability. The initial geometry and extrinsic curvature must satisfy the constraints with **all** these sources.

A geometry-correlated prior is another possible research route, but it must be specified before reading: a positive normalized joint preparation, correct marginal source law, lawful states on each geometry, fixed parameters, and constrained common or explicitly different past histories. It cannot be manufactured afterward by choosing a convenient root for each record.


## No autonomous pulse from this particular zero mean-data preparation

For the candidate controller above, impose \(\chi=\dot\chi=0\) initially, an independent centered probe, and the fixed target/probe product input. At \(\chi=0\) the fields decouple and
\(\langle O_\chi\rangle=-\kappa'(0)\sum_i\langle\nabla\phi_i\rangle\cdot\langle\nabla\psi_i\rangle=0\).
Hence \(\chi\equiv0\) solves this complete deterministic mean controller equation. If its local Cauchy problem is unique, these data cannot produce the desired pulse. A nonzero incoming controller state, explicit driving, or appropriate initial cross correlations must be supplied. This is specific to the stated decoupled centered-probe data; it is not a theorem that arbitrary coupled zero-data controllers never move. The quantum force noise is already nonzero at this mean solution.


The finite renormalized controller coefficients are one set of physical inputs, fixed across both flags and the entire history. They cannot be tuned separately at each time or outcome to cancel a residual. A static-background work ledger provides a further necessary check:
\[
E_{\rm env,out}-E_{\rm env,in}
 =-\int\sqrt{-g}\,\langle O_\chi\rangle_{\rm ren}\,\partial_\tau\chi,
\]
with the same fields, interaction and counterterms included and the coupling off at the endpoints. An autonomous controller supplies the opposite energy change. The final target POVM does not determine this integral. No universal positive-work assertion is made for arbitrary thermal/excited probes.

The leading-GR junction discussion fixes only the second-order Einstein contract. A full AE initial-value comparison must also fix the additional normal curvature jets entering its local terms, or include them among the variables. The strict fixed-old-static-geometry sign test above fixes the entire geometry and is unaffected by this distinction.
