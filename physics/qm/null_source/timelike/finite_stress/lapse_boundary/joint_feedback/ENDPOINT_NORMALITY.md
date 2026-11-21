# Canonical endpoint normality and the exact preparation-resource frontier

## E1. Fixed representation, same actual high modes

This page examines the canonical endpoint map already derived from the original action. It is a **passive representation change** unless the observables and state are deliberately changed. Loss of a normal marginal in a fixed limiting partition is not physical decoherence or loss of probability.

Use the common incoming Fock embedding and \(\mathcal H_G=L^2(\mathbb R_+,d\kappa)\). At the accepted finite initial slice the actual high-mode vacuum has
\[
q_{kmi}=v_k a_{kmi}+\overline v_k a_{kmi}^\dagger,\qquad
X_k=|v_k|^2=\frac{|F_k|^2}{2\omega_k},\quad\omega_k=\sqrt{k^2-1}.
\]
There are \(2k^2\) real oscillators per shell. ACTUAL_INVERSE's actual Jost bounds give, for \(k\ge3\),
\[
\frac1{4\omega_k}\le X_k\le\frac2{\omega_k};
\]
ACTUAL_UV_BRIDGE additionally gives
\[
\big||F_k|^2-1\big|\le8\mu/\omega_k^2,\qquad \mu<.1.                  \tag{E1}
\]
The source's high incoming marginal is exactly pure vacuum. Therefore every normal extension preserving that marginal factors the high vacuum from geometry plus the low source, even if those remaining parts are entangled.

Allow the full controlled map
\[
V_K(\kappa)=e^{i\theta_K\kappa}\,
 V_{{\rm low},K}(\kappa)\otimes
 \exp[i(\kappa-\kappa_*)Q_{3:K}],\qquad
Q_{3:K}=\tfrac12\sum_{k=3}^K\sum_{m,i}q_{kmi}^2 .                   \tag{E2}
\]
The low unitary is supported on the specified fixed low modes; it may be arbitrary and depend on \(\kappa,K\). Scalar phases and the fixed reference \(\kappa_*\) are retained. The bulk embedding and the geometry/source partition are fixed throughout the theorem. The overlap/normality arguments also allow any measurable controlled scalar phase in place of the displayed linear phase: it is absorbed into the remaining input, and the absolute high overlap is unchanged. No derivative claim is made for an arbitrary measurable phase.

## E2. Exact overlap and escape from every fixed normal target

For a Gaussian coordinate of variance \(X\),
\(\langle e^{idq^2/2}\rangle=(1-idX)^{-1/2}\).
Consequently the high-vacuum overlap is
\[
c_K(d)=\prod_{k=3}^K(1-idX_k)^{-k^2},\qquad
|c_K(d)|^2=\prod_{k=3}^K(1+d^2X_k^2)^{-k^2}.                       \tag{E3}
\]
For every nonzero \(d\), it tends to zero. One useful uniform bound for \(|d|\le D\) is
\[
|c_K(d)|^2\le
 \exp\!\left[-\frac{(K-2)d^2}{16(1+D^2/2)}\right].                  \tag{E4}
\]
It follows from \(k^2X_k^2\ge1/16\), \(X_k^2\le1/2\), and
\(\log(1+x)\ge x/(1+x)\).

Absorb the controlled low unitary and scalar phase into a normal geometry marginal \(\sigma_K\). The output geometry density is a trace-preserving completely positive Schur channel
\(\gamma_K=\Phi_K(\sigma_K)\), whose kernel is multiplied by \(c_K(\kappa-\kappa')\).
For each fixed finite-rank projection \(F\), its dual has Hilbert–Schmidt kernel
\(\overline{c_K(\kappa-\kappa')}F(\kappa,\kappa')\).
Dominated convergence, since the diagonal has Lebesgue measure zero, gives
\[
\|\Phi_K^*(F)\|_{\rm op}\le\|\Phi_K^*(F)\|_{\rm HS}\longrightarrow0.  \tag{E5}
\]
This is uniform over **all** normal input densities \(\sigma_K\), including varying ones.

Given a fixed normal trace-one target \(\gamma\), choose \(F\) with
\(\operatorname{Tr}F\gamma>1-\epsilon\). The probability bound gives
\[
D_{\rm tr}(\Phi_K\sigma,\gamma)
 \ge1-\epsilon-\|\Phi_K^*F\|_{\rm op},
\]
and hence
\[
\boxed{\lim_{K\to\infty}\inf_{\sigma\ {\rm normal}}
       D_{\rm tr}(\Phi_K\sigma,\gamma)=1.}                           \tag{E6}
\]
Every exact-high-vacuum output sequence escapes every fixed normal target; it has no trace-norm convergent subsequence to a trace-one normal density. The same conclusion for a fixed joint target follows by partial-trace contraction.

A distinct, weaker purity calculation is sometimes useful. If the input geometry probability density is fixed \(n\), then
\[
\operatorname{Tr}\gamma_K^2
 \le\iint n(\kappa)n(\kappa')|c_K(\kappa-\kappa')|^2d\kappa d\kappa'
 \longrightarrow0.
\]
It remains true if \(n_K\to n\) in \(L^1\), because the integral changes by at most \(2\|n_K-n\|_1\). For \(n\in L^2\) of support diameter at most \(D\), E4 bounds it by
\[
\min\left\{1,\,
4\sqrt{\frac{\pi(1+D^2/2)}{K-2}}\|n\|_2^2\right\}.
\]
We do **not** assert purity tends to zero for arbitrary varying inputs. The stronger distance theorem E6 does not need that false assertion.

## E3. Correlated high preparation and uniform tail tightness

Now allow arbitrary normal geometry–field inputs \(\rho_K\), including high-mode correlations. Let \(P_J\) project all incoming modes above \(J\) onto vacuum. If
\[
\sup_K\operatorname{Tr}\rho_K(1-P_J)\le\epsilon_J\longrightarrow0,
\]
then the output still has distance tending to one from every fixed normal geometry target.

Indeed, for \(p=\operatorname{Tr}\rho_KP_J>0\), set
\(\rho_K^J=P_J\rho_KP_J/p\).
Projecting a purification and normalizing gives overlap \(\sqrt p\), so
\[
D_{\rm tr}(\rho_K,\rho_K^J)\le\sqrt{1-p}.
\]
The modes above \(J\) in \(\rho_K^J\) are pure vacuum and factor from the rest. For fixed \(J\), E5 applies to their growing tail, regardless of the remaining correlations. Apply contraction, then take \(K\to\infty\), \(J\to\infty\), and \(\epsilon\to0\). When \(p=0\), use the trivial probability bound instead of defining the normalized compression.

Every **fixed** normal input is tail tight because \(P_J\uparrow I\) strongly. A uniformly bounded expectation of the **full** incoming \(H_{\rm exc}=\sum_{k\ge3,r}\omega_kN_{kr}\) is another sufficient condition. A bound only on the truncated \(H_{{\rm exc},K}\) does not by itself control modes above \(K\); E4 treats the truncated-energy problem independently. Thus merely allowing finite-energy correlated preparation does not automatically repair the fixed-frame continuum problem. No input-convergence assumption was used in the family statement.

There is also an exact compactness consequence. Any family converging in trace norm to a normal input in the common incoming Fock embedding is uniformly tail tight: use the limit's tail and trace-distance contraction for all sufficiently large indices, and \(P_J\uparrow I\) for the finitely many remaining inputs. Hence, if the endpoint geometry outputs converge in trace norm to a fixed normal target, the incoming family has **no trace-norm convergent subsequence** to a normal input in this embedding. This conclusion uses tail tightness, not the invalid inference that diverging energy alone prevents trace convergence. It allows a different representation or an algebraic non-normal limit; neither supplies joint dynamics automatically.

## E4. A sharper finite-cutoff resource inequality for arbitrary correlations

Define the high-mode incoming excitation budget
\[
H_{{\rm exc},K}=\sum_{k=3}^K\sum_{m,i}\omega_k a_{kmi}^\dagger a_{kmi},
\qquad E_K=\operatorname{Tr}\rho_KH_{{\rm exc},K}.                    \tag{E7}
\]
It excludes the zero and \(k=2\) blocks. It is not a total conserved Hamiltonian, renormalized gravitational source, apparatus work, or SI energy.

For any band \(B\subset\{3,\ldots,K\}\) of \(L\) shells, E3 gives
\[
|c_B(d)|^2\le(1+d^2/144)^{-9L}.                                    \tag{E8}
\]
To see the bound for all \(d\), use \(X_k>1/(4k)\) and the monotonicity of
\(x\log(1+a/x)\) in \(x>0\), with \(x=k^2\ge9\), \(a=d^2/16\).
Define for a fixed finite-rank geometry projection
\[
a_L(F)^2=\iint|F(\kappa,\kappa')|^2
 \left(1+\frac{(\kappa-\kappa')^2}{144}\right)^{-9L}
 d\kappa d\kappa'\longrightarrow0.                                 \tag{E9}
\]
The bound is uniform in the band's location.

Let \(P_B\) be the band's incoming vacuum projection and \(p_B=\operatorname{Tr}\rho_KP_B\). The normalized compression factors that band from arbitrary geometry and all other modes. All remaining controlled unitaries can be absorbed into this environment, since they commute with the band's controlled shear. The purification bound and E9 therefore imply
\[
q_K:=\operatorname{Tr}F\gamma_K\le a_L(F)+\sqrt{1-p_B}.              \tag{E10}
\]
This covers arbitrary correlations between different bands.

Partition the high shells into disjoint consecutive \(L\)-shell bands
\(B_j=\{3+jL,\ldots,2+(j+1)L\}\),
\(j=0,\ldots,m-1\), \(m=\lfloor(K-2)/L\rfloor\). In the incoming occupation basis,
\[
H_{{\rm exc},K}\ge\sum_j\omega_{3+jL}(1-P_{B_j}).
\]
Thus, with \(S_{K,L}=\sum_j\omega_{3+jL}\),
\[
\boxed{E_K\ge S_{K,L}[q_K-a_L(F)]_+^2,\qquad
       S_{K,L}/K^2\longrightarrow1/(2L)\quad(L\ {\rm fixed}).}       \tag{E11}
\]
For a fixed target \(\gamma\), a directly reviewable error/resource form is
\[
\boxed{D_{\rm tr}(\gamma_K,\gamma)\ge
 \left[\operatorname{Tr}F\gamma-a_L(F)-\sqrt{E_K/S_{K,L}}\right]_+.}   \tag{E12}
\]
It applies at finite \(K\) when \(S_{K,L}>0\).

If \(\gamma_K\to\gamma\) in trace norm, select \(F\) with \(\operatorname{Tr}F\gamma\ge3/4\), then a fixed \(L\) with \(a_L(F)\le1/4\). Equation E11 gives
\[
\liminf E_K/K^2\ge1/(8L)>0.                                       \tag{E13}
\]
Conversely \(E_K=o(K^2)\) forces every fixed finite-rank output probability to zero: first fix \(L\) in E11, then let \(L\to\infty\). It follows that
\[
D_{\rm tr}(\gamma_K,\gamma)\to1
\quad\hbox{for every fixed normal }\gamma.                         \tag{E14}
\]
The constants depend on the fixed target. For an extraordinarily narrow geometry packet, the required \(L\) may be extraordinarily large. This asymptotic theorem is not a numerical resource certificate at \(K=131072\), and it does not give one uniform positive constant for all moving target families.

## E5. Normal preparations attaining the quadratic order

The lower bound is not a claim that no input can produce a normal output. For any normal target \(\gamma\) with
\(0<M_2=\operatorname{Tr}\gamma(\kappa-\kappa_*)^2<\infty\), set
\[
\rho_{{\rm in},K}=V_K^\dagger
  (\gamma\otimes\rho_{\rm low}\otimes|\Omega_{\rm high}\rangle
                             \langle\Omega_{\rm high}|)V_K .
\]
Each input is a normal positive density, and its full output is exactly the fixed displayed product state.

For a single incoming oscillator,
\[
e^{idq^2/2}a e^{-idq^2/2}
 =(1-idX)a-id(\overline v)^2a^\dagger .
\]
The vacuum number after the inverse shear is \(d^2X^2\). Retaining both fields and the shell degeneracy gives the exact high budget
\[
E_{{\rm vac},K}=2M_2\sum_{k=3}^Kk^2\omega_kX_k^2.                  \tag{E15}
\]
In particular
\[
\frac{M_2}{8}\sum_{k=3}^Kk\le E_{{\rm vac},K}
                    \le16M_2\sum_{k=3}^Kk,
\qquad E_{{\rm vac},K}=\Theta(K^2).
\]
Together E13 and E15 establish the minimum **growth order**, within this precise representation and resource contract, for fixed finite-\(M_2\) targets. They do not determine an optimal universal coefficient.

These inputs change the complete raw high-source marginal and create geometry–high correlations. Normality alone does not give the evolution's \(Q_p\) or force domains; smooth compact geometry vectors, Schwartz low vectors, and smooth specified controls give a suitable finite-\(K\) common core. For general controls we claim normality only.

Nor are these usually compatible marginals of one raw infinite-field state. Adding a band and tracing it out multiplies the previous geometry kernel by that band's overlap. The preparation is selected for each cutoff. There is no automatic common normal input limit; E3 in fact excludes a fixed normal input producing the normal output limit. A local autonomous preparation action has not been constructed.

## E6. Exact optimum when only a pure geometry output is fixed

A stronger comparison can be solved exactly. Fix
\(\gamma=|\psi\rangle\langle\psi|\), with
\[
m=\langle\kappa-\kappa_*\rangle,\qquad
v=\operatorname{Var}_\psi\kappa\in(0,\infty).
\]
A normal joint state with this pure marginal must be \(\gamma\otimes\sigma\): positivity restricts its support to \(|\psi\rangle\otimes\mathcal H_{\rm source}\). Here the high output \(\sigma\) is **allowed to vary**; it is not fixed to the vacuum as in E5.

Rotate the notation of the incoming annihilator phase so that
\(q=\sqrt{2X}\,Q\), \([Q,P]=i\), and \(N=(P^2+Q^2-1)/2\).
The shear sends \(P\) to \(P-2dXQ\). Averaging the conjugated incoming number over the fixed geometry gives
\[
A_k=\tfrac12[(P-2mX_kQ)^2+(1+4vX_k^2)Q^2-1].
\]
It is unitarily equivalent to an oscillator with frequency
\(\Omega_k=\sqrt{1+4vX_k^2}\), and hence has lowest eigenvalue
\((\Omega_k-1)/2\). Mode or low-environment entanglement cannot beat the sum of these operator lower bounds. Therefore
\[
\boxed{E_{\min}(K,\psi)=
 \sum_{k=3}^K k^2\omega_k\,[\sqrt{1+4vX_k^2}-1].}                  \tag{E16}
\]
It is attained by the product of normalized chirped squeezed Gaussians
\[
g_k(Q)=(\Omega_k/\pi)^{1/4}
 \exp[-\Omega_kQ^2/2+imX_kQ^2],
\]
followed by the same inverse controlled dressing.

This is an exact finite-cutoff optimum for **pure geometry output fixed, high output free**. It does not match the old source, momentum or dynamical constraints by itself.

The actual, nonstatic Jost covariance fixes its leading coefficient. Put
\(C=8\mu\), \(B_0=1+C/8\), \(C_2=2C+C^2/8\). From E1 and
\[
\sqrt{1+x}-1=\frac x2-\frac{x^2}{2(\sqrt{1+x}+1)^2},
\]
together with \(k^2/\omega_k^3\le2/k\) and
\(0\le k^2/\omega_k-k\le1/k\), one obtains
\[
\left|E_{\min}-\frac v2\sum_{k=3}^Kk\right|
 \le [\,v/2+vC_2+v^2B_0^4/4\,]\sum_{k=3}^K1/k .
\]
Thus
\[
\boxed{E_{\min}(K,\psi)/K^2\longrightarrow v/4.}                    \tag{E17}
\]
This uses the actual incoming ultraviolet limit, not a replacement by a static vacuum. The simpler fixed-vacuum output has
\(E_{{\rm vac},K}/K^2\to(v+m^2)/4\).

If the already specified reference happens to equal the fixed target mean, \(m=0\), the optimized high output has squeeze
\(r_k=\tfrac14\log(1+4vX_k^2)=O(k^{-2})\).
The product-overlap tail converges because \(\sum k^2r_k^2<\infty\), so this output has a normal Fock limit. Its excitation expectation nevertheless grows as \((v^2/8)\log K\). Normality and finite energy are distinct requirements. No reference is reset for free, and no common normal input or joint constrained dynamics follows from this optional output observation.


### E6a. An exact mixed-target class: disjoint geometry supports

Let \(\gamma=\sum_{j=1}^r p_j|\psi_j\rangle\langle\psi_j|\), with a fixed finite number of normalized packets supported on pairwise disjoint measurable \(\kappa\)-sets \(I_j\), and \(v_j=\operatorname{Var}_{\psi_j}\kappa<\infty\). Then
\[
\boxed{E_{\min}(K,\gamma)=\sum_jp_jE_{\min}(K,v_j),\qquad
 \lim E_{\min}(K,\gamma)/K^2=\tfrac14\sum_jp_jv_j.}                  \tag{E18}
\]
This is an exact minimum over all normal joint outputs with that geometry marginal, including entangled ones.

To prove it, put \(P_j=1_{I_j}(\kappa)\) and \(H'_K=V_KH_{{\rm exc},K}V_K^\dagger\). The positive self-adjoint \(H'_K\) strongly commutes with every \(P_j\), since the map is controlled by \(\kappa\). A joint state with marginal \(\gamma\) is supported on \(P=\sum_jP_j\). Split the trace first for \(H'_K\wedge n\), then use monotone convergence:
\[
\operatorname{Tr}\rho H'_K=\sum_j\operatorname{Tr}P_j\rho P_jH'_K.
\]
Each normalized diagonal block has pure geometry marginal \(\psi_j\), so E16 applies. The normal mixture of those pure-target optimizers reaches all lower bounds at once. No added ancilla or independent record space is required. Disjoint **supports** are essential; Hilbert-space orthogonality alone is insufficient.

The coherent target \(\psi=\sum_j\sqrt{p_j}e^{i\theta_j}\psi_j\) has the same entire \(\kappa\) law, but is pure and pays E16 with
\[
v_{\rm total}=\sum_jp_jv_j+\sum_jp_j(m_j-\bar m)^2.
\]
Its leading resource exceeds E18 by one quarter of the between-packet variance. Thus a classical probability law or its total variance does not fix this quantum preparation cost.

For a fixed member of NEAR_RECOVERY, the central and remote conditional variances are \(\mu_2\delta m^2\) and \(\mu_2R^2/100\). Dephasing their superposition gives
\[
v_{\rm within}=\mu_2[(1-w)\delta m^2+wR^2/100],\qquad
v_{\rm between}=\delta h(R-h).
\]
The mixed and coherent target coefficients are respectively \(v_{\rm within}/4\) and \((v_{\rm within}+v_{\rm between})/4\).
The two target densities have trace distance exactly \(\sqrt{w(1-w)}\), although their leading resource coefficients differ by \(v_{\rm between}/4\). Small trace distance does not by itself control this unbounded-moment resource. This is a comparison of target states, not an actual decoherence mechanism.

Even the mixed cost remains large:
\(w>\delta h/R\) and \(R>h^{-2}/(5\delta)\) give
\(v_{\rm within}>\mu_2/(500h)\).
The comparison fixes one packet target selected at the original dynamical cutoff \(131072\); it is not a proved negative-\(g\) evolution across all cutoffs.

As a separate diagnostic in the original finite-\(K\) raw frame, dephasing these disjoint geometry packets while keeping the same old source preserves all \(\kappa\) functions and every legitimate finite initial product of local geometry differential operators and source operators: cross-support matrix elements vanish. This includes the already matched initial generator budget and the force gate. It does not prove equality of positive-time histories; compact bumps need not be analytic vectors. The endpoint **resource optimizers** change the conditional high source and do not automatically preserve those raw-frame initial data. The raw recovery state's transported geometry marginal need not be pure.

### E6b. General finite-rank mixed targets: a computable upper bound

For a fixed finite-rank \(\gamma=\sum_i\lambda_i|i\rangle\langle i|\), assume its range \(P\) is contained in \(D(\kappa)\). The second moment below is the full quadratic-form value \(\operatorname{Tr}\gamma\kappa^2\), not \(\operatorname{Tr}\gamma(P\kappa P)^2\).
Set \(A=P\kappa P\) and
\[
Y_{ij}=\frac{2\sqrt{\lambda_i\lambda_j}}{\lambda_i+\lambda_j}A_{ij},
\quad
C_\gamma=\operatorname{Tr}\gamma\kappa^2-\operatorname{Tr}\gamma Y^2.
\]
The variance convex-roof identity is \(C_\gamma=F_Q(\gamma,\kappa)/4\), in the standard convention \(F_Q=4\operatorname{Var}\kappa\) for pure states (Yu, arXiv:1302.5311, Eqs. 1, 4, 6, 8). We retain the full unbounded-observable form term when applying the finite-rank construction.

For completeness, \(\gamma Y+Y\gamma=2\sqrt\gamma A\sqrt\gamma\). Diagonalize \(Yy_j=\alpha_jy_j\), put \(p_j=\langle y_j,\gamma y_j\rangle\), and \(\psi_j=\sqrt\gamma y_j/\sqrt{p_j}\). This is an explicit ensemble of \(\gamma\), with average variance \(C_\gamma\). Any other finite or countable ensemble has vectors \(u_j=\sqrt{p_j}\gamma^{-1/2}\psi_j\), \(\sum|u_j\rangle\langle u_j|=P\). The Sylvester identity and Cauchy–Schwarz give
\(p_j\langle\kappa\rangle_j^2\le\langle u_j,Y\gamma Yu_j\rangle\);
summing proves minimality of this average variance.

Mixing the normal pure-target endpoint optimizers for the displayed ensemble gives an **attainable upper bound**
\[
E_{\rm upper}(K,\gamma)=\sum_jp_jE_{\min}(K,v_j),\qquad
\boxed{\lim E_{\rm upper}/K^2=C_\gamma/4=F_Q(\gamma,\kappa)/16.}       \tag{E19}
\]
For the explicitly restricted class of finite or countable mixtures of pure-geometry product outputs, this leading coefficient is optimal, even if the ensemble varies with \(K\): \(v_j\le\|\kappa P\|^2\) makes the logarithmic remainder uniform. The independent proof in [MIXED_RESOURCE.md](MIXED_RESOURCE.md) now supplies the matching lower bound for arbitrary normal entangled inputs, all normal finite-second-moment targets, and trace-convergent approximate outputs. E18 retains its stronger exact finite-cutoff equality for disjoint-support mixtures.

A fully continuous geometry example checks the otherwise easily lost form term. Let \(b(x)\) be an even smooth normalized bump, \(\mu_j=\int x^j|b|^2\), and \(m>\ell>0\). Put
\[
\phi_0(\kappa)=\ell^{-1/2}b((\kappa-m)/\ell),\qquad
\phi_1=x\phi_0/\sqrt{\mu_2},\qquad
\gamma=\lambda|\phi_0\rangle\langle\phi_0|
 +(1-\lambda)|\phi_1\rangle\langle\phi_1|,\quad0<\lambda<1.
\]
Then \(A=mI+\ell\sqrt{\mu_2}\sigma_x\) and
\(Y=mI+2\sqrt{\lambda(1-\lambda)}\ell\sqrt{\mu_2}\sigma_x\).
The optimal variance ensemble is
\(\psi_\pm=\sqrt\lambda\,\phi_0\pm\sqrt{1-\lambda}\,\phi_1\), each with weight \(1/2\), and both have variance
\[
C_\gamma=\ell^2\!\left[\mu_2(2\lambda-1)^2
 +(1-\lambda)(\mu_4/\mu_2-\mu_2)\right]>0.
\]
Its endpoint mixture has exact cost \(E_{\min}(K,C_\gamma)\), an upper bound for the unrestricted mixed problem. The omitted form term would be
\(P\kappa^2P-A^2=\operatorname{diag}(0,\ell^2(\mu_4/\mu_2-\mu_2))\);
discarding it falsely gives zero at \(\lambda=1/2\). These are actual smooth \(L^2(\mathbb R_+)\) packets, not a finite matrix substituted for the geometry.


### E6c. A lower bound for arbitrary finite-rank joint extensions

There is a further bound for an **exact fixed** finite-rank geometry marginal \(\gamma\); trace-approximating marginals with components outside its support are not covered by this leakage argument; E4 and MIXED_RESOURCE handle them. Let
\[
P=\operatorname{supp}\gamma\subset D(\kappa),\quad
A_0=P(\kappa-\kappa_*)P,\quad
T_0=(1-P)\kappa P,\quad
L=T_0^\dagger T_0=P(\kappa-\kappa_*)^2P-A_0^2,\quad
l=\operatorname{Tr}\gamma L .
\]
All compressed quantities are bounded matrices; the squared operators are understood as forms. In fact \(l>0\). Otherwise faithfulness of \(\gamma\) on \(P\) would force \(\kappa P\subset P\), producing an eigenvector in a finite-dimensional invariant subspace of multiplication by \(\kappa\), which has no normal eigenvectors.

For one real incoming oscillator, the endpoint-transformed annihilator is
\(a_V=a-iX(\kappa-\kappa_*)(a+a^\dagger)\).
On an output purification with support in \(P\), its inside and outside components are orthogonal:
\[
P a_V\Psi=b\Psi,\quad
(1-P)a_V\Psi=-iXT_0(a+a^\dagger)\Psi,\quad
b=(1-iXA_0)a-iXA_0a^\dagger.
\]
Thus the exact positive energy form is
\[
E_K=\sum_{\rm real\ modes}\omega[
 \langle b^\dagger b\rangle+2X^2\langle LQ^2\rangle],
\qquad Q=(a+a^\dagger)/\sqrt2 .                                    \tag{E20}
\]

The domain step matters. If the original input energy is finite, \(a_V\Psi\) is square integrable. Distributional projection gives \(b\Psi\) square integrable. A finite matrix diagonalization of \(A_0\) makes \(b\) a matrix of quadratic chirps of the ordinary oscillator annihilator. Each chirp preserves the closed oscillator form domain \(D(a)=D(a^\dagger)\). Hence \(a\Psi,a^\dagger\Psi\) exist and the orthogonal split is legitimate. Positive density sums and Hilbert–Schmidt closure extend it to normal states. An infinite energy satisfies the lower bounds trivially.

Inverting this finite shear gives
\[
a=(1+iXA_0)b+iXA_0b^\dagger,\qquad
n=\langle a^\dagger a\rangle
 \le(2+4X^2\|A_0\|^2)\langle b^\dagger b\rangle+2X^2\|A_0\|^2.
\]
Define
\[
S_K=\sum_{\rm real}\omega X^2,\quad R_K=\sum_{\rm real}\omega X^4,
\quad C_A=2+4\|A_0\|^2\sup_{k\ge3}X_k^2 .
\]
The output excitation is bounded by
\(E_{{\rm out},K}\le C_AE_K+2\|A_0\|^2S_K\).

A weighted Hilbert–Schmidt Cauchy–Schwarz estimate sharpens the force of E20. Put \(t=\langle LN\rangle\), \(l=\langle L\rangle\). Since \(L\) commutes with the oscillator,
\[
|\langle La^2\rangle|\le\sqrt{t(t+l)},\quad
\langle LQ^2\rangle=t+l/2+\operatorname{Re}\langle La^2\rangle
 \ge l/2-\sqrt{lt}\ge l/2-\sqrt{l\|L\|n}.
\]
Summing and applying Cauchy–Schwarz once more yields the finite-cutoff inequality
\[
E_K\ge lS_K-2\sqrt{l\|L\|R_K(C_AE_K+2\|A_0\|^2S_K)} .
\]
Splitting into \(E_K\ge lS_K\) and \(E_K<lS_K\) gives the simpler explicit form
\[
\boxed{E_K\ge
 [\,lS_K-2\sqrt{l\|L\|R_K(C_Al+2\|A_0\|^2)S_K}\,]_+.}             \tag{E21}
\]
This permits arbitrary entanglement in the output, not just the ensembles used for E19.

The actual Jost covariance gives
\(S_K=K(K+1)/4+O_{\rm history}(\log K)\), while
\(R_K\le64\sum_{k=3}^K1/k\). Therefore
\[
E_K\ge lK^2/4-O_{\gamma,\rm history}(K\sqrt{\log K}).
\]
Combining the explicit lower and attainable upper gives
\[
\frac l4\le\liminf\frac{E_{{\rm opt},K}}{K^2}
 \le\limsup\frac{E_{{\rm opt},K}}{K^2}\le\frac{C_\gamma}{4}.          \tag{E22}
\]
If \([\gamma,P\kappa P]=0\), then \(Y=P\kappa P\), \(C_\gamma=l\), and the global optimal leading coefficient is exactly \(l/4\). This includes maximally mixed states on a fixed finite-dimensional support and the overlapping-packet example with \(\lambda=1/2\), whose coefficient is
\(\ell^2(\mu_4/\mu_2-\mu_2)/8\).
E22 is a useful elementary finite-cutoff leakage bound. Its former noncommuting leading-order gap is closed by [MIXED_RESOURCE.md](MIXED_RESOURCE.md), which proves the sharp \(F_Q/16\) coefficient without a finite-rank restriction. The leakage argument here alone does not prove that stronger theorem.

## E7. A positive algebraic limit, and the exact representation change it requires

For the exact high-vacuum case, suppose the incoming geometry probability density \(n(\kappa)\) is fixed in \(L^1\). Arbitrary low controlled unitaries and scalar phases may still vary. Define the bounded geometry operators
\[
(M_s\psi)(\kappa)=\kappa^{is}\psi(\kappa),\qquad
(D_t\psi)(\kappa)=e^{t/2}\psi(e^t\kappa).
\]
They satisfy \(D_tM_s=e^{ist}M_sD_t\).
For \(t\ne0\), the output expectation has the bound
\[
|\operatorname{Tr}\gamma_K M_sD_t|
\le\int e^{t/2}|c_K((e^t-1)\kappa)|
       \sqrt{n(e^t\kappa)n(\kappa)}\,d\kappa\longrightarrow0.
\]
The majorant is integrable by Cauchy–Schwarz, while the overlap tends to zero at every \(\kappa>0\). At \(t=0\), the limit is
\(\int\kappa^{is}n(\kappa)d\kappa\).
These limits on finite Weyl sums are positive, normalized, and uniformly bounded; density extends them to a state on the concrete unital \(C^*\) algebra generated by \(M_s,D_t\).

The limiting state's dilation characteristic is \(1\) at \(t=0\) and \(0\) elsewhere. Its **own GNS representation** is nonregular and has no self-adjoint Stone generator for this dilation family. Indeed the vectors \(\pi(D_t)\Omega\) form an uncountable orthonormal set, so that GNS space is nonseparable. The original differential dilation generator on the original \(L^2(\mathbb R_+)\) remains self-adjoint; it has not ceased to exist.

Multiplication records retain \(n\), and probability is conserved. This is a precise singular algebraic limit, not an empirical dissipation process. The already proved normal differential-form dynamics cannot simply be transferred into this new representation. Constructing an action-derived constraint and evolution there would be a new task.

The same Weyl limit also holds for arbitrary correlated inputs with \(E_K=o(K^2)\) **and** \(\kappa\)-densities \(n_K\to n\) in \(L^1\). For fixed \(L\), disjoint bands in the upper half of the cutoff have energy weights of order \(K\); E7's budget supplies a band with \(1-p_B\le C L E_K/K^2\to0\). Its compressed density obeys \(n_B\le n_K/p_B\). The preceding Weyl expectation is then at most
\[
2\sqrt{1-p_B}+p_B^{-1}b_L(t;n_K),
\]
where \(b_L\) is the same integral with the overlap replaced by the square root of E8's envelope. Its change under \(n_K\to n\) is at most \(2\sqrt{\|n_K-n\|_1}\). First take \(K\to\infty\), then \(L\to\infty\); dominated convergence proves the claim for \(t\ne0\). The factor two in the gentle bound is necessary for a unitary expectation; projection probabilities in E10 have factor one. Energy control alone does not select a limiting \(\kappa\) law.

## E8. Outcome for the common-history goal

Three distinct conclusions must stay together:

1. Preserving the actual high incoming vacuum in the fixed canonical partition does not yield a normal all-mode geometry marginal after endpoint transport.
2. Allowing changed correlated preparations gives normal finite-cutoff outputs, with a sharp quadratic excitation growth order and the exact pure-target optimum above.
3. Neither those cutoff-dependent preparations nor the singular algebraic limit supplies the missing single normal joint state, its original constraints, and an autonomous preparation history.

All statements are within the declared representation, source and controlled map. Different representations, moving observable algebras, different high preparations, or changed interactions remain possible but need their own action, domain and state construction.
