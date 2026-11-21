# A correlated Gaussian candidate: normal bulk limit, divergent original constraint form

## C1. The candidate after the unchanged-source route fails

JOINT_CUTOFF rejected the direct unchanged actual-source product-core limit. This page explicitly allows a changed complete source and tests a correlated alternative. It uses the same complete R5 clock generator, ordering \(\eta\ge-1/4\), original counterterms, \(U_0\), and cutoff dependence.

Fix a compact geometry interval \([a,b]\subset(0,\infty)\), a normalized smooth compact profile \(g(\kappa)\), and **one** integer \(J\ge3\) with \(J^2>1+b^2\). All modes below \(J\), including the two zero modes, are retained in a fixed regular low state. A far packet with enormous \(b\) can require an enormous \(J\); this construction is not a numerical repair at the earlier cutoff \(131072\).

For each high real mode define
\[
\Omega_k(\kappa)=\sqrt{\omega_k^2-\kappa^2},\qquad
\chi_{k,\kappa}(q)=
 \left(\frac{\Omega_k}{\pi}\right)^{1/4}
 \exp[-(\Omega_k+i\kappa)q^2/2].
\]
Every finite-\(K\) joint vector below is compact-smooth in \(\kappa\) and Schwartz in its finitely many source coordinates. It belongs to the already specified finite-\(K\) form and weighted-energy classes. This is not a new claim that a moving full-field operator domain is a common core.

The exact source row is
\[
\kappa^{-1}H_0+{\cal D}
 =\frac{(p+\kappa q)^2+(\omega_k^2-\kappa^2)q^2}{2\kappa}.
\]
Thus \(\chi_{k,\kappa}\) is its normalized ground state, with energy
\(\Omega_k/(2\kappa)\). The direct high source pair term vanishes at fixed \(\kappa\).
This conditional line bundle is not invariant under the complete evolution: the geometric derivative acts on \(\chi_{k,\kappa}\).

## C2. The original source and scalar counterterms really cancel

Let \(\beta(\kappa)=1+\kappa^2\) and
\[
P_k(\kappa)=k^3-\beta k/2-\beta^2/(8k).
\]
With \(G(u)=C(u)/120\), \(g_K=G-{\mathfrak h}_K/4\), define the cutoff-independent retained coefficients
\[
D_0=V_0a(u)^4U_0-\tfrac32V_0a(u)^2-u/8-c_{\rm an},
\quad D_1=\tfrac32V_0a(u)^2-G+29/120,
\quad D_3=59/720-G/2.
\]
The interval endpoint \(a\) is distinct from the scale factor \(a(u)\).
The exact J2 identity is
\[
\frac{d_{0,K}}\kappa+d_{1,K}\kappa+d_{3,K}\kappa^3
 =\frac{D_0}\kappa+D_1\kappa+D_3\kappa^3
                  -\kappa^{-1}\sum_{k=1}^K P_k(\kappa).           \tag{C1}
\]
Hence the complete nonprincipal mean in this conditional state equals the fixed low contribution plus
\[
\frac{D_0}\kappa+D_1\kappa+D_3\kappa^3
-\kappa^{-1}\sum_{k<J}P_k
+\kappa^{-1}\sum_{k=J}^K
 [\,k^2\sqrt{k^2-1-\kappa^2}-P_k\,].                              \tag{C2}
\]
No extra counterterm has been introduced. The quartic, quadratic and logarithmic source pieces all cancel by the original coefficients.

There is a uniform actual remainder. Put \(\beta_{\max}=1+b^2\) and \(r=\beta_{\max}/J^2<1\). Taylor's theorem gives
\[
|k^2\sqrt{k^2-\beta}-P_k|
 \le\frac{\beta_{\max}^3}{16(1-r)^{5/2}k^3}.
\]
Thus the C2 tail after \(K\) is bounded uniformly by
\[
\frac{\beta_{\max}^3}{32a(1-r)^{5/2}K^2}.                         \tag{C3}
\]
The nonprincipal expectation has a finite limit on this class. This positive result alone does not include the geometric kinetic form.

## C3. The connection mean can be removed; its variance cannot

For one normalized real Gaussian,
\[
\langle\chi,\partial_\kappa\chi\rangle=-\frac{i}{4\Omega_k},
\]
and its projective derivative norm is
\[
\|\partial_\kappa\chi\|^2-
 |\langle\chi,\partial_\kappa\chi\rangle|^2
 =\frac{1+(\Omega_k')^2}{8\Omega_k^2}
 =\frac{\omega_k^2}{8(\omega_k^2-\kappa^2)^2}.
\]
Let \(\Phi_{\kappa,K}\) be the product over the \(2k^2\) real modes in \(J\le k\le K\). Its Berry coefficient and gauge-invariant metric are
\[
{\cal B}_K=\sum_{k=J}^K\frac{k^2}{2\Omega_k},\qquad
{\cal G}_K=\frac14\sum_{k=J}^K
          \frac{k^2(k^2-1)}{(k^2-1-\kappa^2)^2}.                 \tag{C4}
\]
Uniformly on the fixed interval,
\[
{\cal G}_K=K/4+O_{a,b,J}(1),\qquad
{\cal G}_K\ge(K-J+1)/4.                                          \tag{C5}
\]
Indeed each summand before the factor \(1/4\) differs from one by a positive \(O(k^{-2})\) term.

Choose \(\Theta_K'={\cal B}_K\), for example
\(\Theta_K=\frac12\sum_{k=J}^Kk^2\arcsin(\kappa/\omega_k)\)
up to a scalar constant. The joint high vector
\(\widetilde\Phi_{\kappa,K}=e^{i\Theta_K}\Phi_{\kappa,K}\) has zero Berry mean. On the full finite-\(K\) form domain the original geometry form is exactly
\[
q_\eta[g\widetilde\Phi_K]
 =q_\eta[g]+\int_a^b \kappa^{-1}|g(\kappa)|^2{\cal G}_K(\kappa)\,d\kappa
 =\frac K4 I_1+O(1),\quad
I_1=\int_a^b\kappa^{-1}|g|^2>0.                                  \tag{C6}
\]
The fixed low state contributes no divergent derivative term. C6 is the derivative cost of a correlated state, not an additional optional noise model.

For fixed real amplitude and any scalar phase, the right-hand side additionally contains the nonnegative weighted square of the phase derivative minus \({\cal B}_K\). Berry cancellation minimizes this form. On the negative-\(g_K\) branch it therefore maximizes, rather than minimizes, the complete generator expectation.

## C4. Full expectation: the candidate still fails the finite-form gate

By J3, \(\alpha_K=-2/\log K+O((\log K)^{-2})\). Combining C2 and C6 gives
\[
\boxed{
\lim_{K\to\infty}\frac{\log K}{K}
 \langle g\widetilde\Phi_K,\bar H_K\,g\widetilde\Phi_K\rangle
 =-\frac{I_1}{2}<0.}                                             \tag{C7}
\]
Thus the full expectation diverges even though the complete source-plus-scalar-potential part converges.

A different scalar phase cannot repair this divergence: it adds a positive amount to \(q_\eta\), whose coefficient is negative. With the same compact support and fixed low source, C5 also supplies a negative divergent upper bound independent of the choice of a normalized geometry amplitude, provided its form expectation is defined. No exact scaled limit is asserted for arbitrarily varying amplitudes.

If one restores a prescribed nonzero instantaneous \(\kappa\) rate \(\nu\) using the additional phase
\(\exp[i(g_K\nu)\kappa^2/2]\) on a real amplitude of mean \(m\), the added form is \((g_K\nu)^2m\), and its energy contribution is \(g_K\nu^2m/2=O(\log K)\). It does not change C7.

This rejects this conditional-ground-state family's finite complete-constraint-form route with the original counterterms. It is not a claim that negative energy alone makes a normal state illegal, or that all other correlated preparations and strong propagator limits are impossible.

## C5. Nevertheless a normal bulk joint state limit can be constructed

The original source connection is
\[
W_K=\exp i[S_{g,K}(\kappa)+\kappa Q_K],\qquad
S_{g,K}'=A_K
=-K(K+1)/4-(1+\kappa^2){\mathfrak h}_K/4 .
\]
The high shear in \(W_K\) removes the phase \(-i\kappa q^2/2\) from each conditional Gaussian. The resulting high amplitudes are the real frequency-\(\Omega_k(\kappa)\) vacua. The fixed low transformation is retained as a smooth controlled finite-mode factor.

First choose the regular no-chirp bulk \(q,p\) Fock reference of frequencies \(\omega_k\). The real-vacuum squeeze parameter is
\[
r_k(\kappa)=\tfrac12\log(\Omega_k/\omega_k)
          =\tfrac14\log(1-\kappa^2/\omega_k^2)=O_b(k^{-2}).
\]
For \(L>K\), the high-vacuum overlap is
\[
\langle\varphi_{\kappa,K},\varphi_{\kappa,L}\rangle
 =\prod_{k=K+1}^L(\cosh r_k)^{-k^2}.
\]
Using \(\log\cosh r\le r^2/2\) gives
\[
\sup_{\kappa\in[a,b]}
 \|\varphi_{\kappa,L}-\varphi_{\kappa,K}\|^2\le C_{b,J}/K.         \tag{C8}
\]
The limiting Fock vector depends continuously on \(\kappa\).

The residual scalar phase \(\Xi_K=S_{g,K}+\Theta_K\) also has a limit. Its derivative is
\[
\Xi_K'=
-\sum_{k<J}\left(\frac k2+\frac{1+\kappa^2}{4k}\right)
+\sum_{k=J}^K
 \left[\frac{k^2}{2\Omega_k}-\frac k2-\frac{1+\kappa^2}{4k}\right].
\]
The bracket is uniformly \(O(k^{-3})\). Choose the single common normalization prescription \(\Xi_K(\kappa_{\rm ref})=0\); this changes only the global scalar phase at each cutoff. Then \(\Xi_K\) and \(\Xi_K'\) converge uniformly, with \(O(K^{-2})\) tails. Consequently
\[
\Psi_{{\rm bulk},K}
 =g(\kappa)e^{i\Xi_K(\kappa)}
  [\,W_{{\rm low}}(\kappa)\chi_{\rm low}\,]\otimes
  \varphi_{\kappa,K}
\]
converges in the **fixed bulk tensor Hilbert space**, with norm tail
\(O(K^{-1/2})\). Its normal pure densities converge in trace norm. A fixed normal low mixture is handled by purification and trace contraction.

The reference can be related to the actual quiet-history bulk Jost Fock by one fixed unitary identification. Here the canonical bulk momentum is \(p=q'\), with
\(v=e^{-i\omega t}F/\sqrt{2\omega}\). The Bogoliubov coefficient of the static bulk annihilator is
\[
\beta_k=\frac{i e^{i\omega t}\overline{F_k'}}{2\omega},
\qquad |\beta_k|\le2\mu/\omega_k^2 .
\]
Thus \(\sum 2k^2|\beta_k|^2<\infty\). Choosing positive tail-vacuum overlaps gives convergence of the product transformations on finite-particle vectors, and then a fixed Fock unitary. The raw momentum \(q'-h_iq\) would instead contain \(O(h_i/\omega)\) mixing and is not this identification.

This normal bulk state is not a trace-normal limit of the raw chirped inputs. There is no contradiction with ENDPOINT_NORMALITY's fixed raw-partition exclusion, and no full-field unitary \(W_\infty\) is claimed.

## C6. Why normality does not cure the original covariant form

In the bulk the original derivative is
\(P_\kappa-(A_K+Q_K)\), with the same domain transport. On the state in C5 the scalar cancellation removes the **mean** of \(Q_K\), but leaves
\[
Q_K-\langle Q_K\rangle_\kappa .
\]
Its high conditional variance is
\(\sum_{k=J}^K k^2/(4\Omega_k^2)\).
The real-amplitude derivative adds
\(\sum k^2\kappa^2/(4\Omega_k^4)\); together they are exactly \({\cal G}_K\).
Replacing the covariant derivative by a bare derivative would delete this divergence and change the original constraint.

The distinction is now explicit: a positive normal bulk joint state limit exists for this candidate, while its prescribed complete constraint form has no finite limit. No Hadamard/microlocal condition for the full joint geometry family, original mean-history recovery, full pressure/force match, momentum constraint, or autonomous preparation is established by normality.

This candidate changes the original complete incoming source and its momentum correlations. Its success at conditional source diagonalization and its normal bulk limit cannot be combined with the earlier old-source \(\Pi_g\), pressure or curvature budgets without recalculation. The next accepted preparation must pass those physical gates and the complete continuum dynamics together.

## C7. Review led to a mean repair, with a divergent second-moment bound

The preceding rejection concerns the conditional ground family. It must not be enlarged into a claim that no nearby normal preparation can match even one clock mean. Here is a concrete counterexample using the same existing fields.

In one real mode of shell \(K\), replace the conditional ground by the normalized \(n=1\) Hermite eigenstate with the same \(\Omega_K(\kappa)\) and chirp. Give that branch its own Berry-canceling scalar phase. Its source energy increases by \(\Omega_K/\kappa\), its Berry coefficient by \(1/(2\Omega_K)\), and its projective metric by \(\omega_K^2/(4\Omega_K^4)\). Average uniformly over the \(2K^2\) possible high real modes, preserving the shell's spatial symmetry. Denote this normal branch mixture by \(\rho_{1,K}\) and the ground branch by \(\rho_{0,K}\). Their complete clock-mean gap is exactly
\[
\Delta E_K=
 \int|g|^2\frac{\Omega_K}{\kappa}\,d\kappa+
 \alpha_K\int\kappa^{-1}|g|^2\frac{\omega_K^2}{4\Omega_K^4}\,d\kappa
 =K I_1+O(K^{-1})>0.                                             \tag{C9}
\]
Every branch has the same \(\kappa\) probability law and Berry-flat current.

For any specified finite real target \(E_*\), define at all sufficiently large cutoffs
\[
p_K=\frac{E_*-E_{0,K}}{\Delta E_K},
\qquad \rho_K=(1-p_K)\rho_{0,K}+p_K\rho_{1,K},
\]
where \(E_{0,K}\) is the full ground expectation in C7. Then
\[
0<p_K<1,\quad p_K\sim\frac1{2\log K},
\qquad \operatorname{Tr}\rho_K\bar H_K=E_* .                       \tag{C10}
\]
This is one explicit cutoff rule for an initial mean, not a time-dependent selection of histories or a preparation derived from an autonomous action.

Parity makes the odd excited sectors orthogonal to the all-even ground sector, including after the original controlled \(W_K\). Therefore
\(D_{\rm tr}(\rho_K^V,\rho_{0,K}^V)=p_K\to0\).
The repaired family has exactly the same normal bulk state limit as C5.

Its clock fluctuation is nevertheless unbounded. Each finite-cutoff branch lies in the compact/Schwartz snapshot operator domain through second order. The exact mixture-variance identity gives
\[
\operatorname{Var}_{\rho_K}(\bar H_K)
\ge p_K(1-p_K)(\Delta E_K)^2,
\]
and therefore
\[
\boxed{\liminf_{K\to\infty}
 \frac{\log K}{K^2}\operatorname{Var}_{\rho_K}(\bar H_K)
 \ge \frac{I_1^2}{2}>0.}                                         \tag{C11}
\]
No negative component variance was discarded. This is an actual finite-cutoff normal-state construction, not a classical independent-noise replacement for its joint dynamics.

The covariant geometry form still grows as \(K I_1/4\); the rare excitation changes that leading term by a vanishing amount. Thus normal state convergence and exact agreement of one mean do not provide common form or clock-second-moment control.

The variance in C11 is **not** automatically the residual variance of the full constraint \(P_u+\bar H_K\): an actual joint constraint solution may have correlations with the clock momentum. Those correlations, the complete finite-slice density, pressure/curvature equations and real preparation must still be constructed. Similarly a bare canonical \(\Pi_g\) divergence cannot be compared with a frozen finite-cutoff target; its same-action counterterms and reference must use the same \(K\). No unsubtracted canonical-momentum divergence is used here as a no-go result.

## C8. Its actual initial geometry curvature is also controlled

Use the complete finite-\(K\) second-Ehrenfest identity in GEOMETRY_CURVATURE on these compact/Schwartz initial vectors. Write
\(I_3=\int\kappa^{-3}|g|^2>0\) and
\(J_3=\int\kappa^{-3}\|\partial_\kappa\Psi_K\|^2\).
The fixed-profile Berry-flat ground and rare-shell mixture satisfy
\[
J_3=K I_3/4+O(1).
\]
Their kinetic contribution to the second geometry derivative is therefore
\(-2K I_3/(\log K)^2+o(K/(\log K)^2)\).
The finite ordering \(I_5\) term and the explicit \(\alpha_K'\) current term are smaller on this scale.

The ground source-force brace has a uniform bound. Hellmann–Feynman for the exact conditional source eigenstate gives
\[
\frac{\langle H_{0,K}\rangle+d_{0,K}}{\kappa^3}
-\frac{d_{1,K}}{\kappa}-3d_{3,K}\kappa
=-\kappa^{-1}\partial_\kappa {\cal V}_{K,\rm ground}(\kappa).
\]
The C2 remainder and its \(\kappa\) derivative have uniformly summable tails on the fixed interval, so this brace is \(O(1)\). A single \(n=1\) high mode adds exactly
\(\omega_K^2/(\kappa^3\Omega_K)\).
With \(p_K\sim1/(2\log K)\) and \(2\alpha_K\sim-4/\log K\), that addition contributes another
\(-2K I_3/(\log K)^2\). Consequently, for derivatives in the \(u\) clock at the initial slice,
\[
\lim\frac{(\log K)^2}{K}\langle\kappa\rangle''_{\rm ground}
=-2I_3,\qquad
\boxed{\lim\frac{(\log K)^2}{K}\langle\kappa\rangle''_{\rm repaired}
=-4I_3.}                                                        \tag{C12}
\]
The mixture weights are selected once at the initial slice and held during evolution; no time-dependent retuning contributes to this derivative.

These are initial-jet conclusions. A positive Taylor window exists for each finite cutoff on the already proved regular class, but no common positive window or uniform Taylor remainder has been established. Divergent derivatives alone do not rule out a propagator limit with an initial layer.

For a real fixed profile, the Berry-flat initial \(\kappa\) current is zero. The optional \(g_K\nu\) phase in C4 can restore a nonzero finite-cutoff rate and leaves C12's leading coefficient unchanged, but its \(\log K\)-dependent geometry phase generally destroys the fixed normal bulk limit in C5. That phase cannot be added while claiming all previously passed gates remain unchanged.

## C9. A rare phase mixture also restores a nonzero initial current

The failure of the single global phase in C8 is not a universal current obstruction. A second normal mixture restores the initial current while retaining the C5 state limit.

Take the fixed profile \(g\) real. At the initial slice choose once
\[
r_K=(\log K)^{-2},\qquad b_K=g_K(u_i)\nu/r_K,\qquad
T_K=e^{ib_K\kappa^2/2}.
\]
Apply the same channel
\[
{\cal P}_K(\rho)=(1-r_K)\rho+r_KT_K\rho T_K^\dagger
\]
to both the \(n=0\) and the isotropic \(n=1\) branches. For each Berry-flat branch the cross term vanishes. The phase adds exactly \(b_K\) to \(\langle B\rangle\), \(b_K^2m\) to \(q_\eta\), and \(b_K^2I_1\) to \(J_3\), where \(m=\langle\kappa\rangle\). Consequently
\[
\langle B\rangle=r_Kb_K=g_K(u_i)\nu,\qquad
\left.\frac d{du}\langle\kappa\rangle\right|_{u_i}=\nu.            \tag{C13}
\]
The same \(\kappa\) probability law is retained. Since \(T_K\) commutes with the original controlled \(W_K\), the bulk trace distance introduced by this mixture is at most \(r_K\to0\), regardless of the large phase.

Its added form budget is \(r_Kb_K^2m=O((\log K)^4)\), and its added complete mean is
\[
\alpha_Kr_Kb_K^2m=\frac{g_K(u_i)\nu^2m}{2r_K}
 =O((\log K)^3)=o(K/\log K).
\]
This addition is identical in the two source sectors. Thus their gap C9 is unchanged. Recompute \(p_K\) in C10 using this new ground-sector mean. For sufficiently large \(K\), the resulting normal four-component preparation has **simultaneously** the same \(\kappa\) law, the specified initial rate \(\nu\), the specified clock mean \(E_*\), and the same normal bulk limit. Both mixing probabilities and the phase are fixed at the initial slice, not reset during evolution.

Its variance bound C11 remains valid by grouping the two source sectors. The added force from the rare phase is \(O((\log K)^2)\), below the \(K/(\log K)^2\) scale, so its initial curvature still has the repaired limit \(-4I_3\) in C12. Hence for any fixed smooth target history with finite initial second derivative, this candidate fails that second-jet match for all sufficiently large cutoffs. It cannot equal that target's \(C^2\) mean history on a positive interval starting at this slice.

This statement supplies neither a numerical usable cutoff nor a uniform time window. It also illustrates why normal-state convergence does not control unbounded currents or energies without uniform integrability. No autonomous action has been supplied for either mixture, and the physical initial constraint, full feedback and calibrated readout remain separate gates.

## Verification responsibility

The new script checks the exact conditional Gaussian eigen-equation, its connection and projective metric, all retained counterterm cancellations, uniform-tail Taylor algebra, phase/current cost and leading factors. The product-state convergence, common-domain analysis and failure of the complete form are analytic proofs above, independently reviewed. No original mode/geometry ODE or predecessor science module is executed.
