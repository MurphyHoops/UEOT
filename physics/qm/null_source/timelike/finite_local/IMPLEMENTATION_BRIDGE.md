# A finite field-probe bridge in stress moments

This closes a mathematical implementation gap beyond bounded-POVM convergence. It does **not** select a calibrated numerical coupling, impose a uniform device-energy budget, or solve total gravity.

Keep the original two target fields and their actual CQ preparation. Keep the two prescribed future preparation metrics and future windows from ACTUAL_HISTORY.md fixed throughout this argument. Use the finite kinetic target/probe interaction of KINETIC_PROBE.md, with small coupling \(g_c\). The terminal two-flag smooth probe reader is stipulated. For sufficiently small nonzero \(g_c\), an explicitly described normal Hadamard probe preparation gives the same target stress moments to arbitrary accuracy. In particular there exists a finite \(g_c\ne0\) for which the **two-target-field projected future RMS is below \(8\times10^{-6}\)**.

The proof concerns one complete instrument and state at each fixed \(g_c\), not parameters selected independently at different times.

## 1. The first Born observable is exactly the same short test

The actual short support is
\(K\subset\{|\eta|<3\pi/16,\ \operatorname{dist}(\Omega,N)<5\pi/24\}\).
Let \(q=Y_0\eta/A^2\). At \(\eta=0\), choose a free solution \(v\) with data
\((0,Y_0\chi_0/A^2)\), where \(0\le\chi_0\le1\), \(\chi_0=1\) on a cap of radius strictly greater than \(19\pi/48\), and its support lies inside a cap of radius \(\pi/2\). Finite propagation, both forward and backward, gives \(v=q\) on all of \(K\).

Let \(\vartheta\) rise from zero to one between \(7\pi/32\) and \(\pi/4\), and set \(h=\Box(\vartheta v)\). It is a future compact test, inside a cap of radius less than \(3\pi/4\). On \(K\), \(G^{\rm adv}h=-v=-q\). Choose the signed compact coupling
\[
\chi=-t\,b/Y_0.
\]
Then the exact first Born pullback is
\[
f_1=-R_\chi G^{\rm adv}h=R_\chi q
 =-Y_0A^{-4}\partial_\eta\chi=A^{-4}t'b=f.
\]
There is no replacement by a different long filter. The earlier positive-gain example did not require all later choices of \(\chi\) to be nonnegative. A small enough \(g_c\) keeps \(|g_c\chi|<1\).

The ideal short experiment and the field-probe experiment are compared on one common static Cauchy surface after the support of \(h\). Add the same finite free wait to the ideal protocol. The source law and phase-uniform energy/moment bounds are unchanged; the extra zero shear is retained. A later localized flag collection event and broadcast also belong to the same common schedule. The dynamics of that collection apparatus remain outside this theorem.

## 2. Adapt the probe to the exact pulled-back quadrature

The exact outgoing field algebra is
\[
Y_{\rm out}=\Phi(f_g)+\Psi(k_g),\qquad
X_{\rm out}(F)=\Phi(D_gF)+\Psi(F_gF),
\]
where \(f_g=g_cf+O(g_c^3)\), \(k_g=h+O(g_c^2)\), \(D_g=I+O(g_c^2)\), and \(F_g=O(g_c)\). These are the exact Green maps, with parity in \(g_c\); the remainder notation is used for estimates, not to truncate the state.

Set \(H_g=\Psi(k_g)\), and choose a smooth even canonical partner \(J_g\) with \([H_g,J_g]=i\). Prepare this mode independently of its symplectic complement with
\[
\operatorname{Var}H_g=g_c^2v_m,\quad
\operatorname{Var}J_g={1\over4g_c^2v_m},\quad
\operatorname{Cov}(H_g,J_g)=0.
\]
The complement has a uniformly smooth family of normal Hadamard covariances. Each nonzero \(g_c\) is a legitimate finite squeeze; the limit is not a finite-energy state.

For completeness, the adapted pair can be constructed by a finite-rank symplectic map. Choose a reference \(h,j_0\) with \(\sigma(h,j_0)=1\), and write
\(k_g=ah+bj_0+d\), \(d\in\{h,j_0\}^{\sigma}\). Here \(a=1+O(g_c^2)\), \(b,d=O(g_c^2)\). Apply, in order:

- scale \(h\mapsto ah,\ j_0\mapsto j_0/a\);
- \(x\mapsto x+\sigma(x,j_0)d/a-\sigma(d/a,x)j_0\);
- \(x\mapsto x+(b/a)\sigma(x,j_0)j_0\).

The composite sends \(h\) exactly to \(k_g\) and \(j_0\) to \(j_0/a\), is symplectic, and differs from the identity by a smooth even finite-rank \(O(g_c^2)\) map. Start with a pure Hadamard reference whose \(h,j_0\) mode is Gaussian and independent of its complex-structure complement; such a smooth finite mode and any finite squeeze preserve normality and Hadamard form. This specifies the probe family rather than assuming an arbitrary covariance can be squeezed independently.

## 3. The CCR fixes the backaction direction

Decompose the exact probe contribution as
\[
\Psi(F_gF)=a_g(F)H_g+b_g(F)J_g+\Psi(r_gF),
\]
where \(a_g,r_g=O(g_c)\). The outgoing target and probe commute. Since \(\sigma(k_g,F_gF)=b_g(F)\), this gives the exact identity
\[
b_g(F)=\sigma(D_gF,f_g).
\]
Thus \(b_g(F)/g_c=\sigma(F,f)+O(g_c^2)\). Define \(X_{\rm ptr}=H_g/g_c\), \(P_{\rm ptr}=g_cJ_g\). Their covariance is the fixed pure pointer covariance \((v_m,1/(4v_m))\), and
\[
X_{\rm out}(F)=\Phi(F)+\sigma(F,f)P_{\rm ptr}
  +O(g_c^2)\ {\rm terms}+O(g_c)\ {\rm complement\ noise},
\]
\[
Y_g=Y_{\rm out}/g_c=\Phi(f_g/g_c)+X_{\rm ptr}.
\]
Using the exact \(k_g\), rather than only its leading \(h\), is essential: it absorbs the potentially order-one amplified probe shear.

For one actual Gaussian block the finite-coupling kernels are explicitly
\[
V_g=C_s(f_g/g_c,f_g/g_c)+v_m,
\]
\[
c_g(F)=C_s(D_gF,f_g/g_c)+g_cv_m a_g(F),
\]
\[
C_g(F,G)=C_s(D_gF,D_gG)
 +g_c^2v_m a_g(F)a_g(G)
 +{b_g(F)b_g(G)\over4g_c^2v_m}
 +C_{\perp,g}(r_gF,r_gG).
\]
The means use the same actual \(p\). These formulas determine the full finite-coupling target/record state, including its backaction.

## 4. Why the ultraviolet limit controls stress moments

Ordinary trace-distance convergence would not suffice. The required stronger fact is joint smooth parameter dependence of the out Hadamard covariance difference.

After the \(\pm\) rescaling, the operators are \(\Box-V_\pm(g_c)\), with a fixed principal symbol and smooth potentials of common compact support. Parameter-dependent propagation gives joint wavefront control. On the common free-out region, the **combined** target marginal has the same target CCR. Its difference from the reference two-point function is symmetric. Its joint wavefront set is therefore constrained both by the positive Hadamard cone and, after transposition, the negative cone; they do not intersect. The difference is jointly smooth in \((g_c,x,x')\). Fixed principal symbol means there is no additional parameter cotangent singularity.

The adapted unsqueezed probe and target marginal are even in \(g_c\), so their smooth-kernel difference is \(O(g_c^2)\) in every compact \(C^r\) seminorm. One must combine target and probe ultraviolet terms before using this assertion, rather than claiming that each raw propagated vacuum term is separately smooth.

The amplified squeeze contribution is finite rank and satisfies
\[
{b_g(F)b_g(G)\over4g_c^2v_m}
 -{\sigma(F,f)\sigma(G,f)\over4v_m}=O(g_c^2).
\]
All removed reference-mode terms and small-variance terms are also smooth \(O(g_c^2)\). Hence the actual target kernel converges to the exact Gaussian-pointer kernel in this stronger topology.

The underlying parameter-dependent propagation result is available in A. Strohmaier, *An analytic approach to the stress energy tensor in quantum field theory*, arXiv:2508.00487v4, Sec. 4.3 and Appendix C. Its general second-order-operator framework applies here to fixed metric and smooth compact potentials. The covariance parity, adapted squeeze and instrument-specific moment conclusion are the present derivation.

## 5. Complete two-flag stress moments and finite nonzero coupling

The actual \(p\) prior is bounded and the thermal correction has only finitely many shells. The Gaussian block estimates are uniform in \(p\). Apply the same smooth radial effects to \(Y_g/\beta\); all outcomes remain in the two flags. Gaussian conditioning and uniform Gaussian tails permit the flag integrals without producing or deleting a fine record.

Propagate \(C_g,c_g,u_g,q_g\) through the same fixed branch KG maps and preparation metrics. Smooth-kernel convergence persists. Stress means use coincidence derivatives. Differences of the fourth-field expressions defining smeared stress second moments contain at least one \(O(g_c^2)\) smooth kernel, with the remaining factors fixed Hadamard distributions. Smooth compact stress tests therefore give finite continuous moments. The flag probabilities remain greater than 0.49 for small enough \(g_c\).

This proves convergence of the full outcome-weighted squared residual norm, including any small bias between the actual finite-coupling posterior mean and the fixed ideal branch geometry. The ideal upper bound is \(7.5008667861\,10^{-6}\), leaving squared margin greater than \(7.7\,10^{-12}\) below \((8\,10^{-6})^2\). Continuity provides a nonzero interval \(0<|g_c|<g_0\) in which the target-only projected RMS is below \(8\,10^{-6}\).

No numerical \(g_0\), convergence constant or finite calibrated coupling has been computed. This is a finite-coupling existence theorem, not a quantitative device setting.

## 6. The energy and total-gravity boundary survives

For this \(h\), the probe zero-charge commutator is
\[
[H_g,P_\psi]=i\alpha_h,\qquad
\alpha_h=-Y_0^2\int\chi_0\,d\Omega,
\quad |\alpha_h|>
 {\operatorname{Vol}B(19\pi/48)\over2\pi^2}>0.2989.
\]
The exact shift symmetry keeps this coefficient unchanged at finite coupling. Robertson gives the two probes' incoming positive zero-sector energy lower bound
\[
E_{\psi,0}^{(1)}+E_{\psi,0}^{(2)}
 \ge{\alpha_h^2\over4A^3g_c^2v_m}
 >{1.46\,10^{-13}\over g_c^2}.
\]
This is not a lower bound for the entire renormalized apparatus stress. It does prove that the increasingly accurate limit has no uniform finite zero-sector energy budget. Partial tracing the probes does not remove their gravitational source.

If a quantitative squared-residual error bound \(K_mg_c^2\) and a positive zero-sector probe energy budget \(E_*\) are later supplied, a necessary/sufficient-bound compatibility check includes
\(g_c^2\ge K_E/E_*\) and \(g_c^2\le\Delta_{\rm RMS^2}/K_m\), together with hyperbolicity and validity bounds. The constants and the total controller/reader sources must be obtained before claiming that these allowed intervals overlap.

The terminal reader, control-field counterterms, total constrained preparation and nonhomogeneous metric response remain open. The present theorem closes the target stress-moment bridge under its stated apparatus preparation and terminal-reader assumptions.
