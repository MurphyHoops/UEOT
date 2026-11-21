# A complete domain interface and the remaining actual spectral gate

## B1. Keep history endpoints distinct from configuration-domain boundaries

The canonical history one-form
\(\Theta_{\rm hist}=P_u\,\delta u+P_\kappa\,\delta\kappa+\cdots\)
is already fixed by the original action and its endpoint transport. It is not a choice of self-adjoint boundary data for the operator on the \(u,\kappa,z\) **configuration domain**.

For MATTER_DOMAIN's \(S\), integration by parts on a finite box gives
\[
\begin{split}
\langle\psi,S^*\phi\rangle-\langle S^*\psi,\phi\rangle
={}&2i\left[\int\kappa a^2\bar\psi\phi\right]_{u_-}^{u_+}\\
&+\int\frac{a^2}{g}
 [\bar\psi D_\kappa\phi-\overline{D_\kappa\psi}\phi]_{\kappa_-}^{\kappa_+}\\
&+\sum_r\int[\bar\psi\,\partial_r\phi
                -(\partial_r\bar\psi)\phi]_{\partial z_r},
\end{split}                                                        \tag{B1}
\]
where \(D_\kappa=\partial_\kappa-iA_K\). The real potentials cancel.
For compact \(\kappa,z\) traces only, this is an incoming/outgoing flux form. Its \(u\)-boundary amplitudes are
\[
\Gamma_{\rm in}=(a_+\sqrt\kappa\,\psi_{u_+,\kappa>0},
                 a_-\sqrt{|\kappa|}\,\psi_{u_-,\kappa<0}),
\]
\[
\Gamma_{\rm out}=(a_+\sqrt{|\kappa|}\,\psi_{u_+,\kappa<0},
                  a_-\sqrt\kappa\,\psi_{u_-,\kappa>0}),
\]
and B1 divided by \(2i\) is the difference of their inner products.
A unitary rule \(\Gamma_{\rm out}=V_b\Gamma_{\rm in}\) cancels this restricted flux. It has **not** thereby supplied maximal self-adjoint trace data at every noncompact boundary. The next abstract interface supplies the complete domain instead.

The already known pure gauge
\(F_K=B_K\kappa-\mathfrak h_K\kappa^3/12\)
and \(M=e^{iF_K}\) remove \(A_K\) through
\(M^\dagger(P_\kappa-A_K)M=P_\kappa\).
They commute with the stated \(a,\Pi_g,J\). This is reused, not a new closure. The entire domain, state and observables must be transported; no all-mode strong limit of \(M\) is asserted.

## B2. An ordinary boundary triple from the original defect spaces

At reference defect points \(+i,-i\), fix a \(J\)-compatible unitary
\(U_{\rm ref}:N_+\to N_-\). Every \(f\in D(S^*)\) has a unique decomposition
\[
f=f_0+h+U_{\rm ref}k,\qquad f_0\in D(S),\quad h,k\in N_+.
\]
Define
\[
\Gamma_0f=h+k,\qquad \Gamma_1f=i(h-k).                              \tag{B2}
\]
They are continuous in the graph norm, jointly onto \(N_+\oplus N_+\), and their common kernel is \(D(S)\). Direct calculation yields the Green identity
\[
\langle f,S^*g\rangle-\langle S^*f,g\rangle
=\langle\Gamma_0f,\Gamma_1g\rangle
 -\langle\Gamma_1f,\Gamma_0g\rangle.                                \tag{B3}
\]
Thus this is a complete ordinary boundary triple. It is not an incomplete “boundary at infinity ignored” flux prescription.

Let \(K_{\rm ref}=JU_{\rm ref}\), an antiunitary conjugation on \(N_+\).
Then \(\Gamma_jJ=K_{\rm ref}\Gamma_j\).
All self-adjoint domains are parameterized by self-adjoint **linear relations**
\(\Theta\) in the boundary space:
\[
(\Gamma_0f,\Gamma_1f)\in\Theta .
\]
Relations, rather than only graphs of operators, include the Dirichlet case. The antiunitary symmetry is \(K_{\rm ref}\Theta K_{\rm ref}=\Theta\).
Changing \(U_{\rm ref}\) changes coordinates for the interface; it does not select a physical \(\Theta\).

## B3. A resolvent computation must include the actual boundary residual

Let \(R_D=S^*|_{\ker\Gamma_0}\). For \(\Im z\ne0\), define
\[
\gamma(z)=(\Gamma_0|_{\ker(S^*-z)})^{-1},\qquad
M(z)=\Gamma_1\gamma(z).
\]
The Green identity gives
\(\operatorname{Im}M(z)=(\operatorname{Im}z)\gamma(z)^*\gamma(z)\)
and
\(\Gamma_1(R_D-z)^{-1}=\gamma(\bar z)^*\).
Solving the boundary condition yields the exact Krein formula
\[
(R_\Theta-z)^{-1}=(R_D-z)^{-1}
 +\gamma(z)(\Theta-M(z))^{-1}\gamma(\bar z)^*.                       \tag{B4}
\]
It is a framework for the original operator; the actual \(\gamma,M,\Theta\) have not been computed or physically selected here.

A useful rigorous numerical interface uses a faithful trace-one density
\(\tau_*=\sum_{j\ge1}2^{-j}|e_j\rangle\langle e_j|\) for an orthonormal basis.
For \(z=\lambda+i\epsilon\), define
\[
p_\epsilon(\lambda)=\pi^{-1}
 \operatorname{Im}\operatorname{Tr}\tau_*(R_\Theta-z)^{-1}.
\]
If each approximate solution \(v_j\) actually belongs to \(D(R_\Theta)\), and
\(r_j=(R_\Theta-z)v_j-e_j\), then
\[
\left|p_\epsilon-\frac1\pi\operatorname{Im}
 \sum_{j=1}^M2^{-j}\langle e_j,v_j\rangle\right|
 \le\frac{\sum_{j=1}^M2^{-j}\|r_j\|+2^{-M}}{\pi\epsilon}.           \tag{B5}
\]
The bound is just the self-adjoint resolvent norm and the faithful tail. A small bulk differential residual without the stated boundary membership does not justify B5.

A strictly positive broadened \(p_\epsilon\) at finite \(\epsilon\) is not an absolutely continuous spectral certificate: atoms also produce positive Lorentzians. Passing to \(\epsilon\downarrow0\) with a controlled density is a separate unfinished computation.

## B4. The actual old-source radial gate

The desired old zero-mode radial energy law is the explicit absolutely continuous probability
\[
f_{\rm old}(\lambda)=\frac{
 (1-p)\varpi^2((\lambda/(2A^3)-e_0)/\sigma)
 +p\,\varpi^2((\lambda/(2A^3)-e_2)/\sigma)}
 {2A^3\sigma}.                                                     \tag{B6}
\]
It lives in the two original positive bounded bands. For a selected extension, let \(\nu_R\) be a maximal scalar spectral measure, for example
\(\operatorname{Tr}\tau_*E_R(\cdot)\), and let \(p_R(\lambda)\) be its absolutely continuous density.

A normal physical state with this **spectral law** exists exactly when
\(\mu_{\rm old}\ll\nu_R\). Since B6 is absolutely continuous, the missing mass is
\[
q_{\rm miss}=\int_{\{p_R=0\}}f_{\rm old}(\lambda)\,d\lambda .
\]
The infimum total-variation distance to normal attainable spectral laws is \(q_{\rm miss}\). Neither a nonzero band projection nor the broadened resolvent positivity in B5 proves \(q_{\rm miss}=0\).

The previous \(R_T=R-P_2^2\) construction has a Lebesgue spectral type because of its continuous free momentum. That does not determine \(R\)'s own radial law and cannot substitute for B6.

## B5. What finite-rank boundary changes can and cannot change

For two graph unitaries \(Q_0,Q_1\), a trace-class difference \(Q_1-Q_0\) gives a trace-class difference of their Cayley transforms and nonreal resolvents. The resolvent form of the Kato–Rosenblum theorem implies unitary equivalence of their absolutely continuous parts. Consequently the ac support up to Lebesgue null sets, and B6's \(q_{\rm miss}\), are unchanged within that class.

Thus the finite-rank phase change used by MATTER_DOMAIN can alter actual bounded/Dirac record probabilities while leaving this ac attainability gate unchanged. A record ambiguity and a spectral existence gate are different questions. This statement concerns trace-class **domain changes**, not every finite apparatus, every compact perturbation, or every new preparation.

The primary operator-theory source used here is Malamud–Neidhardt, arXiv:0907.0650, especially its boundary-triple framework and Theorem 4.1. The present original-operator application and domain bookkeeping are provided above, not supplied by that reference.

## B6. Conditional normal-state construction once the gate passes

A separable spectral representation can be decomposed into countably many orthogonal cyclic **reducing** subspaces \(\mathcal H_n\), generated by unit vectors \(\psi_n\). Choose positive weights \(w_n\) summing to one, and
\(\psi_*=\sum_n\sqrt{w_n}\psi_n\).
Because the subspaces reduce \(R\), its measure
\(\nu_{\psi_*}=\sum_nw_n\nu_{\psi_n}\)
is maximal. The vector need not be cyclic for the entire multiplicity space.

If \(\mu\ll\nu_{\psi_*}\), then
\[
\xi=\sqrt{\frac{d\mu}{d\nu_{\psi_*}}}(R)\psi_*
\]
is a legitimate normal unit vector with spectral law \(\mu\).
For the two disjoint old bands this supplies orthogonal \(\xi_0,\xi_2\) and a rank-two mixture with the desired radial law.

This is conditional on the **uncomputed actual spectral gate** and does not identify the old full bare source coherence, a free preparation, or the original geometry momentum budget. The next file supplies preparation bounds from an actually available physical input.
