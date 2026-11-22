# A finite local field probe, with its own remaining physical inputs

The ideal Gaussian pointer is not by itself a gravitational apparatus. Here is a separate finite-coupling field-probe candidate. This apparatus action is an explicit new modeling choice; it is not derived from Core, nor is its exact finite-coupling instrument identified with every ideal pointer instrument above.

For one target/probe pair take
\[
{\cal L}=-\tfrac12[(\nabla\phi)^2+(\nabla\psi)^2]
          -g_c\chi(x)\nabla\phi\cdot\nabla\psi,\quad
\chi\in C^\infty_c(K),\quad |g_c\chi|<1.
\]
The constant orthogonal \(\pm\) combinations have kinetic coefficients \(c_\pm=1\pm g_c\chi>0\). Rescaling by \(\sqrt{c_\pm}\) yields normally hyperbolic operators
\(Q_\pm=\Box-V_\pm\), \(V_\pm=\Box\sqrt{c_\pm}/\sqrt{c_\pm}\).
Thus finite-coupling causal Green operators exist. No small-coupling truncation defines the state.

Independent shifts of \(\phi,\psi\) give conserved Noether charges
\(\int_\Sigma n\cdot(\nabla\phi+g_c\chi\nabla\psi)\) and its partner. At both ends \(\chi=0\); hence \(P_\phi^{\rm out}=P_\phi^{\rm in}\) and \(P_\psi^{\rm out}=P_\psi^{\rm in}\). The uncoupled matter momentum is not constant inside the interaction.

## Exact pullback of a future probe measurement

Write \(R_\chi=\nabla_\mu(\chi\nabla^\mu)\), \(P=\Box\), and \(T=P I+g_c\sigma_xR_\chi\). The diagonal advanced Green operators for the original variables are
\(G_\pm=c_\pm^{-1/2}G_{Q_\pm}^{\rm adv}c_\pm^{-1/2}\).
For a future probe test \(h\), the exact incoming target/probe tests are
\[
f_g=-{g_c\over2}R_\chi(G_++G_-)h,\quad
k_g=h-{g_c\over2}R_\chi(G_+-G_-)h.
\]
Then \(\int f_g=0\), \(\int k_g=\int h\), and \(f_g\) is supported in \(K\). The observable is exactly
\[
Y=\beta_gP_\phi+H_\phi(f_g)+\Psi(k_g).
\]
The target \(Q\) coefficient vanishes, while \(\beta_g\) is odd in \(g_c\), and \(k_g\) is even. The true Gaussian noise includes the target high field, the full probe covariance, and the reader noise. No probe zero-mode uncertainty is omitted.

Nonzero source gain is not an abstract genericity assumption. On the old static geometry let \(\delta=\pi/32\), and choose a free solution \(v\) with zero initial value and velocity \(Y_0\chi_0/A^2\), where \(\chi_0=1\) on a cap of radius exceeding \(3\delta\) and is supported inside a cap of radius \(\pi/8\). For \(K\subset(\delta,2\delta)\) times a cap of radius \(\delta\), finite propagation gives \(v=q=Y_0\eta/A^2\) on \(K\). Let a time switch \(\vartheta\) rise between \(3\delta\) and \(4\delta\), and set \(h=\Box(\vartheta v)\). On \(K\), \(G^{\rm adv}h=-v\), so
\[
\beta_1=-\int\chi(\nabla q)^2
 ={Y_0^2\over A^2}\int\chi>0
\]
for \(\chi\ge0,\chi\ne0\). Consequently \(\beta_g=g_c\beta_1+O(g_c^3)\ne0\) at sufficiently small finite coupling. The test \(h\) is not trivial in the field quotient: \(\vartheta v\) is not compactly supported in time. A numerical choice of \(g_c\) and its calibrated gain are still to be provided.

## Representation, actual states and finite resources

Choose a pure quasifree Hadamard fiducial representation on compact \(S^3\), including a normal Gaussian zero mode rather than a nonexistent zero-frequency vacuum. Smooth potential evolution preserves Hadamard form. The covariance difference on a compact Cauchy surface is smooth and Hilbert-Schmidt in the one-particle topology, giving a unitary scattering implementer in this folium. The actual CQ mixture and the finite thermal shells are normal in it. A finite Gaussian reader changes the covariance by smooth finite-rank kernels, preserving Hadamard form. These statements do not assert that every normal state is Hadamard.

Normalize the read probe quadrature \(B\) so \([B,P_\psi]=i\). For the source-referred noise \(w=(W_0+\nu)/\beta_g^2\), with intrinsic \(W_0>0\) and Gaussian reader noise \(\nu>0\), Robertson gives \(W_0\operatorname{Var}P_\psi\ge1/4\). The positive probe zero-sector energy before reading is therefore at least \(1/(8A^3\beta_g^2w)\).

The specified Gaussian Lüders reader adds \(1/(4\nu)\) to \(\operatorname{Var}P_\psi\). Its final positive zero-sector energy is at least
\[
{1\over8A^3}\left({1\over W_0}+{1\over\nu}\right)
 \ge{1\over2A^3\beta_g^2w}
\]
per probe, and twice that for two probes. This is a positive zero-sector bound, not a lower bound for the entire renormalized device stress tensor.

An arbitrary probe-only Weyl displacement after reading can change device stress while leaving every target conditional map and every flag probability unchanged. Thus even the full target instrument, not merely its POVM, fails to determine the gravitational source of the device. A dilation, reader and controller model are essential.

## Exact causal kernels and the Ward responsibility

The retarded interacting field is \(X_\chi=(I-g_cG_T^{\rm ret}\sigma_xR_\chi)X_0\). It agrees with \(X_0\) outside \(J^+(K)\). Its nonselective covariance, mixed target/probe covariance, retarded response, and stress-noise kernels follow from this same linear map, with the actual incoming covariance.

Classically, on shell,
\[
\nabla^\mu T_{\mu\nu}^{\rm fields+int}
 =-g_c(\nabla\phi\cdot\nabla\psi)\,\partial_\nu\chi.
\]
The controller must carry the opposite force and work. At the quantum level the new \(\chi\)-dependent counterterms must be fixed before this identity is a renormalized stress identity; RENORMALIZATION.md makes one unavoidable term explicit.

For a homogeneous illustrative pulse, \(\kappa=g_c\chi(t)\), the exact zero-sector Hamiltonian is
\[
E_0={P_\phi^2+P_\psi^2-2\kappa P_\phi P_\psi\over
             2A^3(1-\kappa^2)}.
\]
Independent zero-mean probes give a mean proportional to \(1/(1-\kappa^2)\): it rises during the pulse and returns after it. This illustration is not the small-cap experiment; it demonstrates why equal in/out energy is not zero intermediate work.

References: Fewster–Verch measurement framework and its Gaussian implementation are discussed in Mandrysch–Navascués, arXiv:2411.13605v2, especially the finite-rank Hadamard appendix. The finite kinetic action, exact kernels, gain construction and energy inequalities here are explicit derivations for the stated model, not a claim that an asymptotic implementation theorem supplied a finite calibrated apparatus.
