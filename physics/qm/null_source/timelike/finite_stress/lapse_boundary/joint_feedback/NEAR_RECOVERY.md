# Arbitrarily small source first-jet error, with explicit geometric cost

## N1. Question and unchanged physical inputs

The strict inverse-moment obstruction in the predecessor does not imply a positive uniform lower bound over all normal geometry preparations. Here we construct a family on the **same** negative-\(g\), finite-\(K=131072\) raw generator and the same actual incoming thin source. The ordering \(\eta\ge-1/4\) is selected once and is not changed along the family. All constants and derivatives below are at the accepted quiet initial slice \(u=0\). The clock is \(u=\log(a/A)\), not proper time.

Use \(h=h_i>0\), \(h<e^{-19980}\), \(|h'_\eta|<1\), and the predecessor bounds
\[
\alpha=(2g)^{-1}=-b_0,\quad 3<b_0<4,\quad
0<d_3<1,\ d_3>.14,\quad 0<d_1<e^{30},\quad
D=\operatorname{Tr}\sigma H_s+d_0,\quad |D|<e^{60}.
\]
The requested geometric momentum satisfies \(|\Pi_{\rm target}|<1\).
The generator, after the already specified pure geometry phase is removed, is
\[
H=\alpha A_\eta+(H_s+d_0)/\kappa+d_1\kappa+d_3\kappa^3.
\]
Its domain, source marginal, raw-to-bulk transformation, and all source-dependent terms are the ones in the predecessor, not a substitute Hamiltonian.

Let \(b\) be the normalized even smooth bump supported in \((-1,1)\) used by the predecessor; write \(J=\int|b'|^2<200\) and \(\mu_2=\int x^2b^2<1\). Integration by parts and Cauchy–Schwarz give \(J\mu_2\ge1/4\), hence \(J\ge1/4\).

## N2. One normal preparation for each tolerance

Given \(\theta>0\), put
\[
\delta=\min(1/64,\theta/8),\qquad \epsilon=\sqrt\delta,\qquad m=(1-\delta)h.
\]
The central packet is
\[
\psi_c(\kappa)=(m\epsilon)^{-1/2}
 b\!\left(\frac{\kappa-m}{m\epsilon}\right);
\]
the remote packet \(\psi_R\) has mean \(R\), width \(R/10\), and the same bump, with \(R\ge1\). Their supports are disjoint. Choose
\[
w=\frac{\delta h}{R-m},\qquad
\psi_g=e^{ib_{\rm geo}\kappa^2/2}
 \left(\sqrt{1-w}\,\psi_c+\sqrt w\,\psi_R\right),
\qquad b_{\rm geo}=g\,h'_\eta/h.
\]
The joint state is \(|\psi_g\rangle\langle\psi_g|\otimes\sigma\). It is normal, has the unchanged rank-two source marginal, and lies in every finite-\(p\) comparison form domain. The smooth compact geometry support is strictly separated from \(\kappa=0\) for each member. The source vectors are the actual finite-mode Schwartz vectors.

The identities
\[
(1-w)m+wR=h,\qquad
\langle\kappa\rangle'_u=2\alpha\langle B\rangle=2\alpha b_{\rm geo}=h'_\eta/h
\]
hold exactly, because the phase contributes $\theta'/\kappa=b_{\rm geo}$ to $B$, while its kinetic-form cost is $b_{\rm geo}^2\langle\kappa\rangle=b_{\rm geo}^2h$. No parameter is selected again at later times.

Let \(I_1=\langle\kappa^{-1}\rangle\). Evenness gives
\[
i_c=\mathbb E(1+\epsilon X)^{-1}
=\mathbb E(1-\delta X^2)^{-1}\in[1,(1-\delta)^{-1}],
\qquad i_l=\mathbb E(1+X/10)^{-1}<2.
\]
Using \(I_1=(1-w)i_c/m+w i_l/R\), \(w<2\delta h/R<\delta\), and \(h\ll1\), one obtains uniformly for every \(R\ge1\)
\[
\boxed{\quad \delta/2<hI_1-1<4\delta\le\theta/2.\quad}                 \tag{N1}
\]
For example the lower bound follows already from
\((1-w)/(1-\delta)-1=(\delta-w)/(1-\delta)\), with \(w<\delta/4\).
The upper bound is bounded by
\((1-\delta)^{-2}-1+2hw/R<4\delta\).
The strictness is consistent with Jensen: no member is a point mass in \(\kappa\).

For the product initial state the legitimate weighted evolution is
\[
\sigma'_u=-iI_1[H_s,\sigma],
\quad
(\sigma_{\rm old})'_u=-i h^{-1}[H_s,\sigma].
\]
Consequently
\[
\sigma'_u-(\sigma_{\rm old})'_u=(hI_1-1)(\sigma_{\rm old})'_u.           \tag{N2}
\]
The relative trace-norm error and the relative error of any nonzero bounded first-jet witness are strictly positive but less than \(\theta/2\). This is a constructive approximation, not exact recovery.

## N3. The complete initial momentum constraint has a root

Write
\[
q_c=m^3q_\eta[\psi_c]
=\delta^{-1}\!\int\frac{|b'|^2}{1+\epsilon X}
 +(\eta-\tfrac34)\!\int\frac{b^2}{(1+\epsilon X)^3},
\]
and similarly \(q_l=R^3q_\eta[\psi_R]\). Since \(\eta-\tfrac34\ge-1\),
\[
\frac1{6\delta}\le q_c<\frac{230}{\delta}+2|\eta-\tfrac34|,
\qquad q_l<23000+2|\eta-\tfrac34|.
\]
The lower bound uses \(\epsilon\le1/8\), \(J\ge1/4\), and
\((2/9)/\delta-2\ge(1/6)/\delta\) for \(\delta\le1/64\).
The cubic shape coefficients satisfy \(t_c=1+3\delta\mu_2<2\) and \(1\le t_l<2\).

Define
\[
Q=1000/\delta+10|\eta-\tfrac34|+10>q_c+q_l+1,
\qquad R_{\rm up}=10\sqrt{Q/\delta}\,h^{-2}.
\]
The full generator expectation is
\[
F(R)=-b_0\left[(1-w)q_c/m^3+wq_l/R^3+b_{\rm geo}^2h\right]
       +D I_1+d_1h+d_3T_3,
\]
\[
T_3=(1-w)t_cm^3+w t_lR^3.
\]
This includes the source energy, \(d_0,d_1,d_3\), the ordering form, and the preparation phase. In particular the phase contribution \(b_{\rm geo}^2h\) is not silently discarded.

The bounds above give
\[
F(1)\le-3q_ch^{-3}+2e^{60}h^{-1}+e^{30}h+2h^3+4\delta h<-1.
\]
For every \(R\ge1\),
\[
F(R)\ge-5q_ch^{-3}-8\delta q_l h/R^4-4b_{\rm geo}^2h
       -2e^{60}h^{-1}+.14\delta hR^2 .
\]
At \(R_{\rm up}\), multiplication by \(h^3\) yields
\[
h^3F(R_{\rm up})\ge
14Q-5q_c-.0008\,\delta^3q_lh^{12}/Q^2
      -4b_{\rm geo}^2h^4-2e^{60}h^2>1.
\]
Here \(b_{\rm geo}^2h^4=g^2(h'_\eta)^2h^2<h^2\).
Continuity therefore supplies a root \(F(R_*)=-\Pi_{\rm target}\). Selecting, for example, the least root in this fixed compact interval specifies the initial preparation once. The original common weak unitary then evolves this state.

## N4. Costs and the failure of a sharp normal limit

The same estimates at any such root imply
\[
R_*>\frac{h^{-2}}{5\delta},\quad
T_3>\frac{h^{-3}}{24\delta},\quad
q_\eta[\psi_g]>\frac{h^{-3}}{12\delta},
\]
\[
\frac{\delta^{3/2}h^3}{10\sqrt Q}<w<10\delta^2h^3,
\]
\[
\frac1{6h}<\operatorname{Var}\kappa
 <2h^2+\frac{30\sqrt{Q\delta}}h,\qquad
\operatorname{Var}(\kappa^{-1})\le\frac{10\delta}{h^2}.                  \tag{N3}
\]
For completeness, the lower \(R_*\) bound follows by combining \(F(R_*)\in(-1,1)\) with the negative central form term: the positive source and linear terms are negligible after multiplication by \(\delta h^3\), so the positive cubic term must exceed a fixed multiple of \(1/(\delta h^3)\). Since \(T_3<2h^3+4\delta hR_*^2\), the displayed conservative constant follows. The same balance gives the stated \(T_3\) bound. The lower variance follows from \(w(R_*-h)^2\), using \(w>\delta h/R_*\), \(R_*\gg h\), and the lower radius. Upper bounds use \(R_*\le R_{\rm up}\); inverse variance uses the central width \(\epsilon m\), the shift \(m-h=-\delta h\), and the remote weight.

For explicit cost margins, $Z(h)=h^3+2e^{60}h^2+e^{30}h^4+2h^6<1$ and $q_c>10$. The root equation gives $4\delta hR^2>q_c/h^3$, hence $R>(1/2)\sqrt{q_c/\delta}h^{-2}>h^{-2}/(5\delta)$. It also gives $d_3T_3>3q_c/h^3-1-2e^{60}/h-e^{30}h$, which proves the displayed cubic cost. The remote conditional second moment is below $(3/2)R^2$, yielding the constant $30$ in the variance upper bound. For the inverse variance, $h^2\operatorname{Var}(\kappa^{-1})\le\mathbb E(h/\kappa-1)^2$; its central contribution is at most $\delta/(1-\sqrt\delta)^4<2\delta$, and the remote one is below $w<\delta/4$. This is stronger than the stated $10\delta$ bound.

Thus making the source first-jet error arbitrarily small drives large higher geometric moments. This family is not a controlled small-fluctuation geometry. Although the geometry probability measures converge weakly to a delta mass at \(h\) as \(\delta\downarrow0\), no trace-one normal geometry density has that \(\kappa\) distribution; there is no trace-norm normal limit with that law. A decreasing rare-tail probability does not control the high-moment budget.

The separate force calculation in GEOMETRY_CURVATURE proves more: these preparations fail the target geometry's next derivative. The present construction is not a proposal to bypass that result.

## N5. A genuine positive source-error window

Let \(L=\|(\sigma_{\rm old})'_u(0)\|_1>0\). Both the actual coupled evolution and the old finite-mode source evolution admit the core Taylor estimates proved in POSITIVE_WINDOW. Let their common interval be \(0\le t\le T_0\), and choose
\[
C_2=\tfrac12\|\sigma''_u(0)-(\sigma_{\rm old})''_u(0)\|_1
       +(C_{\rm joint}+C_{\rm old})T_0<\infty.
\]
Then
\[
D_{\rm tr}(\sigma_{\rm joint}(t),\sigma_{\rm old}(t))
 \le\theta L t/2
\]
for
\[
0<t\le T_\theta=\min\{T_0,\theta L/(2C_2)\},
\]
with the usual interpretation when \(C_2=0\). This follows from (N2), \(D_{\rm tr}=\|\cdot\|_1/2\), and the second-order remainder bound. The interval depends on the actual preparation; no lower bound uniform in \(\theta\), no proper-time laboratory duration, and no recovery of the geometry history is asserted.

## Verification and source identity

The companion script checks exact packet moment identities, uniform rational shape estimates, the scaled momentum-bracket margins, and the actual frozen coefficient ranges. It does not compute a new mode or geometry ODE, select a root numerically, or formalize the analytic existence theorem. Predecessor source and quiet-history certificates are read only as JSON/text. The construction was independently reviewed by native agents A and B; that is not external peer review.
