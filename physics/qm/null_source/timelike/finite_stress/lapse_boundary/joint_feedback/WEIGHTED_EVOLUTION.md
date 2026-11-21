# Joint source evolution, higher energy domains, and the missing current

The spatial cutoff \(K\) remains fixed. The occupation cutoff is removed. This page extends the already constructed complete unitary evolution on a compact \(u\) interval where \(g_K\) has one nonzero sign. It keeps the original source, action, all \(d_j\), and the declared ordering \(\eta\ge-1/4\). It does not assume transport of raw snapshot strong domains.

## E1. Higher source moments belong to the same evolution

In the predecessor's lens and zero-dilation-removed frame put
\[
 \lambda=1+H_{\rm osc}+P_0^2/2\ge1,\quad S_p=\lambda^p,\quad
 Q_p=D(q_\eta)\cap D(y)\cap D(\lambda^{p/2}),\quad p\ge3
\]
for integer \(p\), with norm squared
\(T_p=q_\eta+\|y\psi\|^2+\langle\lambda^p\rangle\).
Here \(y^2=4\kappa_y^3/9\); the critical ordering uses the closed ground-state form rather than two separately divergent inverse-square terms.

ALL_SIGN_EVOLUTION's spectral-fiber inequalities remain
\[
 B\lambda I\le(c_0/4)q_\eta+(c_0/4)\langle y^2\rangle+C_B\lambda^3,\qquad
 Vm\le(c_0/4)\langle y^2\rangle+C_V ,
\]
where \(c_0=\min_J|\alpha|/b^2>0\),
\(C_B=2B^3/(\sqrt3c_0^2r_\eta^3)\),
\(C_V=2V^{3/2}/\sqrt{3c_0}\), and
\(r_\eta=1+\sqrt{1+4\eta}/2\).
Since \(\lambda^3\le\lambda^p\), the same comparison construction gives
\[
 F_p=\operatorname{sign}(g)H_{\rm diag}+
       (C_B+C_V+1)S_p
 \ge(3c_0/4)q_\eta+(c_0/2)y^2+S_p\ge1.
\tag{E1}
\]
The negative mixed term is strictly form-small in the positive geometry part, with its remainder absorbed by \(S_p\). Thus the form is closed with common domain \(Q_p\), uniformly equivalent to \(T_p\). Applying the same bounds to coefficient derivatives gives \(C^2\) form regularity and \(|F_p'|\le C_{J,p}F_p\). \(S_p,N,F_p,H_{\rm diag}\) strongly commute where asserted in the predecessor. The added \(S_p\) is a comparison quantity, not a physical source.

For completeness a sharper source commutator bound avoids a gratuitous factor equal to the number of modes. Matrix elements of \(D_{\rm osc}\) join occupation vectors \(m=n\pm2e_j\). Put \(\delta=2\omega_j\). Raising and lowering give, respectively,
\[
 \delta|D_{mn}|\le\omega_j(n_j+3/2),\qquad
 \delta|D_{mn}|\le\omega_j(n_j-1/2)\quad(n_j\ge2).
\]
Their sum in any row is at most \(3H_{{\rm osc},n}\le3\lambda_n\). Also \(\lambda_{\max}/\lambda_{\min}\le5\). The mean-value inequality and the row/column Schur test therefore yield
\[
 \left\|S_p^{-1/2}i[D_{\rm osc},S_p]S_p^{-1/2}\right\|
       \le C_p:=3p\,5^{p/2}.
\tag{E2}
\]
For \(p=3\), \(C_3=45\sqrt5<101\). This does not make the full evolution uniform in \(K\): its geometry coefficients and comparison constants still depend on \(K\).

The other source commutator is
\(i[D_{\rm osc},H_{\rm osc}]=\sum(\omega^2q^2-p^2)\), with absolute form bounded by \(2H_{\rm osc}\); its \(\kappa_y^{-1}\) multiple is controlled by the fiber inequality. Hence \(|i[\widehat H,F_p]|\le C_{J,p}F_p\).

The commutator is valid on the domain required by the abstract evolution theorem. Occupation bandwidth gives
\(\|D_{\rm osc}\psi\|_{Q_p}\le C_{d,p}\|(N+1)\psi\|_{Q_p}\).
As \(N+1\le\lambda\), \(F_p\ge\lambda^p\), and these operators strongly commute, this is controlled on \(D(F_p^{3/2})\). Cutoffs in \(N\) and zero-mode momentum commute with the comparison and converge in both \(F_p^{3/2}\) and \((N+1)Q_p\) norms. The diagonal terms cancel before passage to the limit. This extends the core calculation to the actual required bilinear form domain.

Ammari–Breteaux, Appendix C, Corollary C.4, now applies with \(S(t)=F_p\). Its conditions are a common positive form domain, a norm-continuous symmetric generator \(Q_p\to Q_p^*\), the derivative bound, and the just verified commutator bound on \(D(F_p^{3/2})\). It supplies a \(Q_p\)-preserving unitary evolution with trajectories \(C(Q_p)\cap C^1(Q_p^*)\). On \(Q_p\subset Q_3\), uniqueness in the already established \(Q_3\) class identifies this with the original evolution. No new dynamics has been selected.

The geometric lens preserves \(Q_p\) by its dilation and
\(q_\eta[e^{i\theta y^2/2}\psi]\le2q_\eta[\psi]+2\theta^2\|y\psi\|^2\).
Zero-mode dilation gives equivalent source weights. Full source dilation is bounded and strongly continuous on \(D(\lambda^{p/2})\): use (E2), the additional zero-mode bound \(2pS_p\), spectral regularization, and Gronwall. In the original raw identification
\[
 W^\dagger(e^{i\kappa Q}T_a)=e^{-iS_g}T_a.
\]
Thus, after removing this fixed pure geometry phase, raw \(Q_p\) norms are equivalent on the compact interval to the comparison norms. The phase does not preserve ordinary \(q_\eta\) by itself; its entire domain is conjugated. It commutes with source observables and \(\kappa\), so their reductions do not change. All actual compact-\(\kappa\), Schwartz-source N4/N6 preparations belong to every \(Q_p\).

## E2. Positive trace-class weighted reductions

Work in that phase-removed raw representation. In its fixed reference norm use $y=(2/3)\kappa^{3/2}$ and the corresponding fixed source reference weight $\lambda$; these norms are equivalent to the transported lens norms on the compact interval. The bound below uses this raw norm, not a literal identification of the moving lens coordinate. For a density purification \(\Psi\), define
\[
 \sigma=\operatorname{Tr}_{G,\rm ref}|\Psi\rangle\langle\Psi|,\quad
 \beta=\kappa^{-1/2}\Psi,\quad
 \tau=\operatorname{Tr}_{G,\rm ref}|\beta\rangle\langle\beta| .
\]
ORDERING_DOMAIN gives \(r_\eta I\le\sqrt{mq_\eta}\).
Since \(\kappa\le1+4\kappa^3/9=1+y^2\) and \(\lambda^3\ge1\),
\[
 I=\|\beta\|^2\le T_3/(2r_\eta).
\tag{E3}
\]
Therefore \(\kappa^{-1/2}:Q_3\to\mathcal H\) is bounded,
\(\tau\ge0\), \(\operatorname{Tr}\tau=I\), and \(\tau\) is continuous in trace norm. These definitions extend to every normal density of finite indicated comparison energy and do not depend on its purification.

For source Schwartz rank-one tests \(O\), the common weak equation gives
\[
 \frac{d}{du}\operatorname{Tr}(\sigma O)
       =\operatorname{Tr}\tau\,i[H_s,O].
\tag{E4}
\]
The raw source Hamiltonian has its actual explicit \(a(u)\) dependence. In a moving source frame, that dependence and its dilation must both be transported.

For \(Q_6\), apply the same fiber estimate with \(\lambda\) replaced by \(\lambda^2\):
\[
 \langle\kappa^{-1}\lambda^2\rangle
 \le\epsilon q_\eta+\delta\langle\kappa^3\rangle
                         +C_{\epsilon,\delta}\langle\lambda^6\rangle .
\tag{E5}
\]
Finite-mode oscillator ladder estimates, including the free zero momentum, give the operator graph bound
\(\|H_s(u)f\|\le C_J\|\lambda f\|\).
It is not inferred by squaring a form inequality. Thus
\(\gamma=H_s\kappa^{-1/2}\Psi\) and \(\beta\) are Hilbert-space continuous. The products
\(H_s\tau=\operatorname{Tr}|\gamma\rangle\langle\beta|\) and
\(\tau H_s=\operatorname{Tr}|\beta\rangle\langle\gamma|\)
are continuous trace-class operators. Integrating E4 and using separating finite-rank tests proves the Bochner identity
\[
 \boxed{\sigma(u)=\sigma(u_i)-i\int_{u_i}^u[H_s(v),\tau(v)]\,dv,\qquad
           \sigma\in C^1(J;\mathfrak S_1).}
\tag{E6}
\]
It applies to the actual preparations.

Writing \(\Delta=\tau-I\sigma\), with \(\operatorname{Tr}\Delta=0\), gives
\[
 \sigma'=-iI[H_s,\sigma]-i[H_s,\Delta].
\tag{E7}
\]
Neither \(I\) nor \(\Delta\) is determined by replacing \(\kappa\) by \(h\).
The \(Q_p\) results do not automatically supply \(\kappa^{-2}\) moments or global derivatives of \(I,\tau\).

## E3. Exact geometry density and current

Locally away from \(\kappa=0\), \(Q_3\) gives Hilbert-valued \(H^1\) regularity. Define the positive source-valued measure
\[
 d\mu_u(\kappa)=\operatorname{Tr}_{\rm ref}
       |\Psi(\kappa,u)\rangle\langle\Psi(\kappa,u)|\,d\kappa
\]
and the locally integrable trace-class current
\[
 {\cal J}_u(\kappa)=-i\alpha\kappa^{-1}\operatorname{Tr}_{\rm ref}
 \left(|\partial_\kappa\Psi\rangle\langle\Psi|
             -|\Psi\rangle\langle\partial_\kappa\Psi|\right).
\tag{E8}
\]
At the critical ordering, write
\(\partial_\kappa\Psi=D_\eta\Psi+r_\eta\Psi/\kappa\).
The extra real multiple cancels in E8, so the closed ground-state derivative suffices.

On compact geometry tests and source Schwartz finite-rank tests, the exact joint equation becomes
\[
 \partial_u\mu+\partial_\kappa{\cal J}
       =-i\kappa^{-1}[H_s,\mu],
\quad
 T_f'=\int f'{\cal J}\,d\kappa-i[H_s,T_{f/\kappa}],\quad
 T_f=\int f\,d\mu .
\tag{E9}
\]
No geometric endpoint flux has been assumed zero merely because a local equation was written.

A legitimate global regularization is \(f_R=R/(1+R\kappa)\). Its multiplication preserves \(Q_3\) by the ground-state product rule and E3; \(T_{f_R}\to\tau\) in trace norm. Moreover
\[
 \int\|{\cal J}\|_1d\kappa\le2|\alpha|\sqrt{q_\eta I},\quad
 \left\|\int f_R'{\cal J}\right\|_1
       \le2|\alpha|R^2\sqrt{q_\eta I},\quad
 \operatorname{Tr}T_{f_R/\kappa}\le RI .
\]
Hence the regularized weak equation is exact. The two terms on its right are not asserted to have separate limits as \(R\to\infty\). If higher moments and current integrability are independently supplied, the formal hierarchy
\[
 \tau_n'=-i[H_s,\tau_{n+1}]
                -n\int\kappa^{-n-1}{\cal J}\,d\kappa
\]
becomes valid on that stronger domain. Without those hypotheses it is only the cutoff equation E9 that is accepted.

The complete joint density gives an existing closed description:
\[
 i\partial_u\varrho(\kappa,\kappa')
 =(H_{G,\kappa}-H_{G,\kappa'})\varrho
 +\kappa^{-1}H_s\varrho-\kappa'^{-1}\varrho H_s .
\tag{E10}
\]
This is the distributional record of the already constructed unitary, not a replacement apparatus or clock.

## E4. Actual initial correlation growth

For the stated core product initial preparations, set
\(I_2=\langle\kappa^{-2}\rangle\) and
\(J_0=\langle i[H_G,\kappa^{-1}]\rangle\) at the initial slice. The complete-generator core Taylor calculation gives
\[
 \sigma'_0=-iI[H_s,\sigma],\quad
 \tau'_0=J_0\sigma-iI_2[H_s,\sigma],\quad
 \Delta'_0=-i\operatorname{Var}(\kappa^{-1})[H_s,\sigma].
\tag{E11}
\]
The actual bounded source witness \(B_s\) from NEGATIVE_RECOVERY has
\(\operatorname{Tr}\sigma i[H_s,B_s]=c_s>0\).
Thus \(\operatorname{Tr}B_s\Delta'_0=c_s\operatorname{Var}(\kappa^{-1})>0\).
POSITIVE_WINDOW proves a controlled positive interval, and CLOSURE_COUNTEREXAMPLE proves that even the same \(\sigma,\tau\), full \(\kappa\) law, and previously matched geometry means do not determine the next source jet.
