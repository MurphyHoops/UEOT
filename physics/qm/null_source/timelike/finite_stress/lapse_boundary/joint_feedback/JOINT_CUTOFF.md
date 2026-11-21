# Original joint generator: cutoff compatibility and an actual-source UV test

## J1. The same complete generator, with every declared counterterm

This page tests the original finite-\(K\) joint evolution after the resource closure in MIXED_RESOURCE. It does not substitute a simplified source or remove the dilation term. On the complete fixed-q, source-connection W-frame clock generator of RELATIONAL_DOMAIN R5 and ALL_SIGN_EVOLUTION,
\[
\bar H_K(u)=\alpha_K A_\eta+\kappa^{-1}H_{0,K}+{\cal D}_K
 +d_{0,K}/\kappa+d_{1,K}\kappa+d_{3,K}\kappa^3,\qquad
\alpha_K=(2g_K)^{-1}.                                             \tag{J1}
\]
The ordering is the fixed \(\eta\ge-1/4\) choice, with the already specified Friedrichs form
\[
A_\eta=-\partial_\kappa(\kappa^{-1}\partial_\kappa)
          +(\eta-3/4)\kappa^{-3}.
\]
Here \(\eta\) is an ordering label, not conformal time. \({\cal D}_K\) is the original field dilation and is essential below.

COEFFICIENT_WINDOW C1 gives, with \({\mathfrak h}_K=\sum_{k=1}^Kk^{-1}\),
\[
g_K(u)=G(u)-{\mathfrak h}_K/4,\quad
G(u)=\frac{19+15\ell_0+30u}{120},
\]
\[
C_{{\rm rad},K}=\frac{K(K+1)[K(K+1)-1]}4-\frac{{\mathfrak h}_K}8,
\]
\[
\begin{split}
d_{0,K}&=V_0a^4U_0-\tfrac32V_0a^2-u/8-c_{\rm an}-C_{{\rm rad},K},\\
d_{1,K}&=\tfrac32V_0a^2-g_K+K(K+1)/4+29/120,\\
d_{3,K}&=59/720-g_K/2 .
\end{split}                                                       \tag{J2}
\]
\(U_0\) and the AE convention remain fixed. On compact \(u\) intervals,
\[
\alpha_K=-2/\log K+O((\log K)^{-2}),\quad
d_{1,K}=K(K+1)/4+O(\log K),\quad d_{3,K}=O(\log K).                 \tag{J3}
\]
For sufficiently large \(K\), \(g_K<0\) throughout such an interval. In particular the cofinal subsystem \(K\ge131072\) keeps the existing compact \(u\) patch entirely on the negative branch; no passage through \(g_K=0\) is required. The finite-\(K\) complete evolution already covers that sign, but its form constants are not uniform in \(K\).

## J2. Exact cutoff intertwining fails on a bounded original observable

Let \(j_{LK}(A)=A\otimes I\) be the common incoming inclusion. Take real, nonconstant \(f\in C_c^\infty(0,\infty)\), a bounded geometry multiplication observable preserving the actual compact/Schwartz core. All terms of J1 except \(A_\eta\) commute with \(f\), so
\[
i[\bar H_L,j_{LK}f]-j_{LK}i[\bar H_K,f]
 =i(\alpha_L-\alpha_K)[A_\eta,f],                                \tag{J4}
\]
\[
[A_\eta,f]=-2\kappa^{-1}f'\partial_\kappa
           -\kappa^{-1}f''+\kappa^{-2}f'.
\]
For \(L>K\) on a common nonzero-\(g\) patch,
\(g_L-g_K=-\tfrac14\sum_{k=K+1}^Lk^{-1}\ne0\); J4 is a nonzero core operator. Therefore the complete finite-cutoff evolutions do not exactly intertwine this full bounded-observable net.

This is a weak derivative test on the common core, not a claim that the displayed unbounded derivation belongs to the norm generator of every bounded observable. Exact intertwining of the unitary evolutions would imply equality of these legitimate core derivatives, which is enough for the contradiction.

A second independent responsibility remains even if one were to alter the geometric coefficient: the difference contains \(\kappa^{-1}H_{0,(K,L]}\), whose commutator with geometry dilations depends on the added matter energy. A source-independent geometric counterterm cannot make that operator act on the added factor alone. No altered coefficient is adopted here.

Failure of exact cutoff compatibility does **not** rule out a renormalized continuum propagator. It establishes why the purely kinematic transported-algebra construction in COHERENT_TRANSPORT cannot itself supply dynamics.

## J3. Instantaneous current requires a growing geometry form budget

Define the symmetric current form
\[
B=\kappa^{-1/2}P_\kappa\kappa^{-1/2}
   =-i(\kappa^{-1}\partial_\kappa-\tfrac12\kappa^{-2})
\]
on its declared common core; no self-adjoint half-line \(P_\kappa\) is assumed. There is an exact identity
\[
i[A_\eta,f]=\{B,f'\}.
\]
Put \(r_\eta=1+\tfrac12\sqrt{1+4\eta}\). The Friedrichs ground-state representation is
\[
q_\eta[\Psi]=\int_0^\infty\kappa^{-1}
       \|\partial_\kappa\Psi-r_\eta\Psi/\kappa\|^2\,d\kappa.
\]
The real drift term drops out of the current, hence for normalized vectors, and by density sums for normal states,
\[
|\langle i[A_\eta,f]\rangle|
 \le2\|\kappa^{-1/2}f'\|_\infty\sqrt{q_\eta}.
\]
On the regular first-Ehrenfest class (including the actual smooth compact/Schwartz preparations),
\[
\left|\frac{d}{du}\langle f(\kappa)\rangle\right|
 \le \frac{C_f\sqrt{q_\eta}}{|g_K|},\qquad
C_f=\|\kappa^{-1/2}f'\|_\infty.                                  \tag{J5}
\]
Thus a uniformly bounded geometry form budget forces this **instantaneous** bounded-observable derivative to tend to zero. Maintaining a fixed nonzero value \(v_f\) requires
\[
q_\eta\ge g_K^2v_f^2/C_f^2=\Omega((\log K)^2).                     \tag{J6}
\]
This is not a theorem that a limiting trajectory is frozen: existence, convergence and differentiability of that trajectory have not been proved.

For the unbounded first moment, where its stronger Ehrenfest assumptions hold,
\[
\frac{d}{du}\langle\kappa\rangle=\frac{\langle B\rangle}{g_K}.
\]
Matching the old finite-slice rate \(\nu=h'_\eta/h\ne0\) therefore requires
\(\langle B\rangle=g_K\nu\), so its absolute current grows like
\(|\nu|\log K/4\).
The following optional lower bound uses the fixed mean \(m=\langle\kappa\rangle\).
Ground-state Cauchy–Schwarz gives
\(q_\eta m\ge r_\eta^2 I_1^2\), \(I_1=\langle\kappa^{-1}\rangle\),
and \(|\langle B\rangle|^2\le I_1q_\eta\). Eliminating \(I_1\) gives
\[
q_\eta\ge r_\eta^{2/3}|g_K\nu|^{4/3}m^{-1/3}.                    \tag{J7}
\]
All these norms and currents refer to the stated complete frame. In another canonical frame their operators and domains must be transported together; bounding an untransported bare derivative would omit the source and scalar connections.

## J4. Same actual incoming high modes at the finite slice

Fix the accepted initial slice \(u_i\), \(a_i\), \(h_i>0\), and the same incoming source as in ACTUAL_UV_BRIDGE. No example past is substituted. At every high real mode,
\[
q_k=v_k a_k+\bar v_k a_k^\dagger,\quad
\pi_k=(-i\Omega_k-c_k)v_k a_k+(i\Omega_k-c_k)\bar v_k a_k^\dagger,
\]
\[
v_k=e^{-i\vartheta_k}/\sqrt{2\Omega_k},\quad
\Omega_k=\omega_k/|F_k|^2,\quad
c_k=h_i+\Omega_k'/(2\Omega_k).
\]
The canonical momentum is the actual raw \(\pi=q'-h_iq\), not the instantaneous \(q'\). The exact Wronskian gives the displayed phase derivative. Here primes on q and Omega are conformal-time derivatives at the accepted slice, not derivatives in the u clock. ACTUAL_UV_BRIDGE U5 bounds the zeroth and first conformal-time derivatives of
\(|F|^2-1-V/(2\omega^2)\), and consequently
\[
\Omega_k=\omega_k+O(\omega_k^{-1}),\qquad
c_k=h_i+O(\omega_k^{-2}).                                        \tag{J8}
\]
All remainders below are uniform on a fixed compact geometry support
\(0<\kappa_{\min}\le\kappa\le\kappa_{\max}<\infty\).

Choose a normalized fixed \(\phi\in C_c^\infty(0,\infty)\), a fixed actual low-mode state with its finite moments, and the incoming high vacuum. Denote the resulting product-core input by \(\Psi_K\); for a mixed low state use its Hilbert–Schmidt purification. This class includes a fixed compact geometry preparation with the old exact high-source marginal. The latter is pure, so preserving it in any normal extension already forces the high vacuum to factor from geometry plus low modes.

## J5. A high-pair component survives the complete counterterms

In one real mode the terms \(\kappa^{-1}H_0+{\cal D}\) are
\[
\frac{\pi^2+\omega^2q^2}{2\kappa}+\frac{q\pi+\pi q}{2}.
\]
The coefficient of \(a_k^2\) is exactly
\[
b_k(\kappa)=e^{-2i\vartheta_k}
 \left[
 \frac{\omega_k^2-\Omega_k^2+c_k^2}{4\kappa\Omega_k}
 -\frac{c_k}{2\Omega_k}
 +\frac i2\left(\frac{c_k}{\kappa}-1\right)
 \right].                                                       \tag{J9}
\]
In particular,
\[
b_k(\kappa)=\frac i2e^{-2i\vartheta_k}(h_i/\kappa-1)
                  +O(\omega_k^{-1}).
\]
The \(-1\) comes from the original dilation term. Omitting it would give the wrong mismatch and miss its cancellation at the single classical value \(\kappa=h_i\).

Let \(P_{2,{\rm high}}\) be the orthogonal projection onto exactly two incoming high particles, leaving geometry and the low factor unrestricted. The high-shell terms of J1 are its only contributors on \(\Psi_K\). Each real mode contributes \(2|b_k|^2\), with \(2k^2\) real modes, and different mode pairs are orthogonal. Therefore
\[
\boxed{
\lim_{K\to\infty}
\frac{\|P_{2,{\rm high}}\bar H_K\Psi_K\|^2}{K^3}
 =\frac13\int|\phi(\kappa)|^2(h_i/\kappa-1)^2\,d\kappa>0.}          \tag{J10}
\]
The same statement holds for the corresponding Hilbert–Schmidt norm with a fixed normal low state. The positive constant cannot vanish for a normalized \(L^2(d\kappa)\) packet: support only at \(\kappa=h_i\) would have measure zero.

Scalar AE/geometric counterterms and the geometric derivative term do not create high source pairs, so they cannot cancel J10. This rules out convergence of these generators on this unchanged product core, including convergence after a mere scalar-energy subtraction. It is not a proof against convergence of time-integrated propagators on a different controlled domain.

## J6. The complete expectation has a separate positive leading mismatch

The exact per-real-mode vacuum expectations are
\[
\langle H_0\rangle
 =\frac{\Omega_k^2+c_k^2+\omega_k^2}{4\Omega_k}
 =\frac{\omega_k}{2}+\frac{h_i^2}{4\omega_k}+O(\omega_k^{-3}),
\]
\[
\langle{\cal D}\rangle=-c_k/(2\Omega_k)
 =-h_i/(2\omega_k)+O(\omega_k^{-3}).
\]
With the full two-field multiplicity, the shell contributions are
\(k^2\omega_k+h_i^2k/2+O(k^{-1})\) and
\(-h_i k+O(k^{-1})\). The original subtraction satisfies
\[
\sum_{k=2}^K k^2\omega_k-C_{{\rm rad},K}=O(1),
\]
because \(k^2\omega_k=k^3-k/2-1/(8k)+O(k^{-3})\), and J2 is exactly the sum of those first three terms from \(1\) to \(K\), up to a finite low-shell constant.

Consequently the **complete** fixed-core expectation, including \(\alpha_Kq_\eta\), \(d_0,d_1,d_3\), \(U_0\), the low modes and the dilation, obeys
\[
\boxed{
\lim_{K\to\infty}\frac{\langle\Psi_K,\bar H_K\Psi_K\rangle}{K^2}
 =\frac14\int|\phi(\kappa)|^2\frac{(\kappa-h_i)^2}{\kappa}\,d\kappa
 >0.}                                                           \tag{J11}
\]
Indeed the three quadratic pieces are
\(h_i^2\langle\kappa^{-1}\rangle/4\),
\(-h_i/2\), and \(\langle\kappa\rangle/4\). All remaining fixed-core terms are \(O(\log K)\) or smaller. If \(\langle\kappa\rangle=h_i\), the coefficient equals
\(h_i(h_i\langle\kappa^{-1}\rangle-1)/4>0\), making the same strict Jensen mismatch explicit.

A \(K\)-dependent geometry state with unbounded derivatives, or a preparation changing the high-source marginal, is not covered by this fixed-core expectation argument. A state-dependent subtraction of J11 would change the declared renormalization and is not adopted. J10 remains a different orthogonal-sector statement, not merely this expectation calculation.

## J7. What this next closure decides

Three concrete shortcuts have been tested and rejected: exact finite-cutoff dynamical intertwining, a uniformly bounded instantaneous geometry-current budget for a nonzero fixed target current, and convergence of the unchanged actual-source product-core generator/form under the original counterterms. Each rejection has its own stated domain and does not assert a universal no-go theorem.

A genuine joint continuum result now needs a specified common algebra/representation and a proof for the complete propagators in it. In the unitary approach one needs a strong Cauchy construction on a dense set, separately controlled adjoints/reverse propagation, and the same state/domain/preparation compatibility. The fixed-\(K\) evolution estimates and the fixed-background CTP response estimates do not imply these uniform conditions.

Oscillatory integration can change a generator-level UV estimate, so J10–J11 alone do not rule out that route. Conversely, a regular transported observable algebra alone has no such evolution theorem. This is the next precise acceptance question, not an assertion that physical unification has been reached.

## Verification responsibility

The independent checker verifies the original coefficient identities, the exact pair coefficient, multiplicity, actual asymptotic coefficients, commutator and form-root algebra. Frozen source texts and accepted actual-history bounds are source-bound inputs; no old mode/geometry ODE is run. The domain, positive-series and continuum arguments are analytic proofs above, with native independent review, not formal machine proofs or experimental tests.
