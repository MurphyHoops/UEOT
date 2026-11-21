# The original scalar-clock boundary completion is not uniquely selected

## M1. Original operator, not a comparison clock model

This page uses MATTER_CLOCK and SYMMETRIC_CLOCK's **original** constraint, on their bounded \(u\)-configuration interval \(J_g\) away from \(g=0\), with \(\kappa\in\mathbb R\) and the declared ordering zero. It is a different deparameterization from the positive-\(\kappa\) \(u\)-clock evolution; the two are not silently identified.

Remove the two free zero-mode momenta from the original constraint and close the remaining symmetric differential operator \(S=\overline{\bar R_0}\) on its actual compact smooth core \(D_0\). In the predecessor notation,
\[
\bar R_0=-\{\kappa a^2,\Pi_g\}
 -\frac{a^2}{g}(P_\kappa-A_K)^2
 -\sum_r p_r^2-a^4\sum_r\omega_r^2\phi_r^2-2a^2V_{\rm geom}.
\]
The antiunitary \(J\psi(u,\kappa,z)=\overline{\psi(u,-\kappa,z)}\) commutes with \(S^*\), and the proven deficiency indices are \((\infty,\infty)\). All geometry, AE, source and \(U_0\) terms in this operator are kept.

For each specified self-adjoint realization \(R_Q\), the original constraint is the already constructed bounded positive congruence
\[
C_Q=\tfrac12a^{-1}(P_1^2+P_2^2-R_Q)a^{-1}.
\]
Its Abel rigging map, not an arbitrary physical norm, identifies the positive radial band sector with
\(E_I(R_Q)\mathcal H_{g,{\rm osc}}\otimes L^2(S^1)\).
The angular factor is an existing pair of zero-mode momenta, not an added memory.

## M2. Explicit ambiguity respecting the same antiunitary symmetry

For real \(\lambda\) and \(\epsilon>0\), let
\[
N_\pm=\ker(S^*-\lambda\mp i\epsilon).
\]
A unitary \(Q:N_+\to N_-\) defines
\[
D(R_Q)=D(S)\dotplus\{x+Qx:x\in N_+\}.
\]
The symmetry condition is \(QJQ=J\). The Cayley transform is
\[
W_Q=(R_Q-\lambda-i\epsilon)(R_Q-\lambda+i\epsilon)^{-1}
    =V\oplus(-Q),
\]
where \(V\) is the partial Cayley transform on \(N_+^\perp\).
There is no eigenvector at \(1\): the range of \(I-W_Q\) contains a nonzero scalar multiple of the dense domain \(D(S)\). Thus
\[
R_Q=\lambda+i\epsilon(I+W_Q)(I-W_Q)^{-1}.
\]

Take a unit vector \(x\in N_+\), choose its phase so that
\(\alpha=\langle x,Jx\rangle\in[0,1)\), and put \(y=Jx\).
Choose a \(J\)-adapted extension with \(Qx=y\), and another with \(Q'x=-y\), keeping the other adapted basis columns unchanged. Both satisfy the same antiunitary condition. Then
\[
W_Q-W_{Q'}=-2|y\rangle\langle x|,\qquad
\|(R_Q-\lambda+i\epsilon)^{-1}-(R_{Q'}-\lambda+i\epsilon)^{-1}\|
 =1/\epsilon.
\]

The common bounded spectral record
\[
B_Q=\epsilon^2[(R_Q-\lambda)^2+\epsilon^2]^{-1}
    =\tfrac12(I-\operatorname{Re}W_Q)
\]
has, in the same \(J\)-real unit vector
\(\psi=(x+y)/\sqrt{2+2\alpha}\), probability difference
\[
\langle\psi,(B_Q-B_{Q'})\psi\rangle=(1+\alpha)/2\ge1/2.              \tag{M1}
\]
Since \(J\)-real \(D_0\) is dense, the same record difference is greater than \(1/2-\delta\) on a suitable common compact test vector.

For every \(\phi\in D_0\), the differential operator preserves \(D_0\), so
\(R_Q^n\phi=R_{Q'}^n\phi=S^n\phi\) for every finite \(n\).
Thus all those moments and initial jets agree although a bounded record can differ. The spectral theorem also gives
\[
\|e^{-itR_Q}\phi-e^{-itR_{Q'}}\phi\|
 \le 2|t|^n\|S^n\phi\|/n!,\qquad n=1,2,\ldots .
\]
This is a statement about the auxiliary self-adjoint group parameter. It is not a proper-clock or apparatus prediction until a domain has been selected.

## M3. Two nonzero, different projections exist on the actual positive bands

For every nonempty bounded open **set** \(I\subset\mathbb R\), there are two \(J\)-compatible self-adjoint extensions whose \(E_I\) projections are both nonzero and different. This includes the finite union of the two old positive bands. The proof uses only boundedness of \(I\) and a neighborhood of a point contained in \(I\); a smaller interval's projection difference is not assumed to imply the union's difference. The two extensions can moreover be chosen to differ by a rank-one boundary phase.

Let \(\mathcal H_s\) be the closed span of all \(\ker(S^*-z)\), \(\Im z\ne0\). For any extension \(R_Q\), the bounded invertible defect transport
\[
T_{z,w}=I+(z-w)(R_Q-z)^{-1}
\]
maps \(\ker(S^*-w)\) onto \(\ker(S^*-z)\). Thus each nonreal resolvent preserves \(\mathcal H_s\) (the case \(z=w\) follows by continuity); its adjoint also preserves it, so \(\mathcal H_s\) reduces every extension. The identity
\(D(S)=D(R_Q)\cap D(R_{-Q})\) shows it reduces \(S\). The complementary restriction has zero defects and is self-adjoint. The restriction \(S_s\) on \(\mathcal H_s\) is \(J\)-invariant and retains the nonzero deficiency spaces.

Suppose every \(J\)-compatible extension has zero \(E_I\) projection on \(\mathcal H_s\). Choose \(\lambda\) in the interior of \(I\). The gap around \(\lambda\) gives a positive lower bound for
\(\|(S_s-\lambda)f\|/\|f\|\), so \(S_s-\lambda\) is injective with closed range. It cannot be onto: if it were, \(\ker(S_s^*-\lambda)=0\), and solving
\((S_s-\lambda)x=(S_s^*-\lambda)y\) for each \(y\in D(S_s^*)\) would imply \(y=x\in D(S_s)\), making \(S_s\) self-adjoint. Thus there is a nonzero real defect at \(\lambda\). Choose a \(J\)-real \(y\) in it. Its von Neumann decomposition at fixed reference \(\pm i\) has the form
\(y=f_0+x_++Jx_+\), with \(x_+\ne0\); otherwise \(y\in D(S_s)\) would contradict injectivity. A \(J\)-adapted graph unitary sending \(x_+\) to \(Jx_+\) puts \(y\) in its extension domain and makes \(\lambda\) an eigenvalue. This contradicts the zero band projection. Some \(J\)-compatible \(Q_0\) therefore has
\(P_0=E_I(R_{Q_0})|_{\mathcal H_s}\ne0\).

At reference \(\pm i\), define the defect-space conjugation \(K_0=JQ_0\) on \(N_+\). For every unit \(K_0\)-real vector \(x\), \(Q_0x=Jx\). Let
\[
Q_{\theta,x}=Q_0[I+(e^{i\theta}-1)|x\rangle\langle x|].
\]
These graph unitaries remain \(J\)-compatible. Their Cayley transforms obey
\[
W_{Q_{\theta,x}}-W_{Q_0}
 =-(e^{i\theta}-1)|Jx\rangle\langle x|.
\]
This is a rank-one change tending to zero in norm. Choose \(q\in C_c^\infty(I)\) with
\(q(R_{Q_0})|_{\mathcal H_s}\ne0\). Norm-resolvent continuity and continuous functional calculus for \(q\) ensure that
\(E_I(R_{Q_{\theta,x}})|_{\mathcal H_s}\ne0\) for sufficiently small phases, uniformly in \(x\) because the displayed norm difference is \(|e^{i\theta}-1|\).

Assume every such sufficiently small rank-one phase change has the same band projection \(P_0\). Then \(P_0\) commutes with \(W_{Q_0},W_{Q_{\theta,x}}\), their rank-one differences and their adjoints. Products show commutation with
\(|x\rangle\langle x|\) and \(|Jx\rangle\langle Jx|\) for every \(K_0\)-real \(x\). Commutation with \(|Jx\rangle\langle x|\) gives the same eigenvalue, either zero or one, on \(x,Jx\). A \(K_0\)-real orthonormal basis and its pairwise real sums show that this scalar is the same on all of \(N_+\) and \(N_-\). Defect transport with \(R_{Q_0}\), which commutes with \(P_0\), propagates it to every nonreal defect space and then all of \(\mathcal H_s\). Since \(P_0\ne0\), \(P_0=I\) there.

The extension's spectrum on \(\mathcal H_s\) is then contained in the bounded **closure** of \(I\), so its restriction is bounded. A closed dense restriction of a bounded operator has full domain, making \(S_s\) self-adjoint, a contradiction. At least one explicit small rank-one phase change therefore has a nonzero band projection different from \(P_0\). The two full original extensions have different nonzero projections, with the self-adjoint complementary part unchanged.

This establishes domain ambiguity in the original positive spectral sector. It proves neither that a selected domain passes the old absolutely continuous spectral gate nor that a boundary completion is physically selected.

## M4. A common original Dirac observable distinguishes physical outputs

The ambiguity can be read after the actual original rigging, not only through the auxiliary Lorentzian record. For a kinematic test \(f\), write \(f_a:=a f\) and \(\widehat f_a:=\mathcal F_2(a f)\), where \(\mathcal F_2\) Fourier-transforms the two original zero-mode coordinates. For common annular radial tests with
\[
\widehat f_a(p)=\sum_j q_j(|p|^2)\psi_j,\qquad
q_j\in C_c^\infty(I),\quad \psi_j\in D_0,
\]
the predecessor rigging gives \(T_Q f=\sqrt\pi\sum_jq_j(R_Q)\psi_j\).
Let \(a_Q(f,g)=\langle T_Qf,T_Qg\rangle\).

For the two different nonzero band projections in M3, these positive forms cannot be proportional on the common test space. If \(a_Q=c\,a_{Q'}\), smooth approximants with \(q_n^2\to1_I\), followed by dense polarization, give
\(E_I(R_Q)=cE_I(R_{Q'})\). Nonzero projections force \(c=1\), contrary to M3. Select a common \(g\) with both squared norms positive, and \(f\) with different ratios.

Choose smooth orthonormal angular functions \(e_0,e_1\), supported in \(|\theta|<\pi/4\), in the existing two-zero-mode Fourier-polar factor. The single kinematic test
\(F=f\otimes e_0+g\otimes e_1\)
gives normal physical rays
\[
\xi_Q=\frac{T_Qf\otimes e_0+T_Qg\otimes e_1}
 {\sqrt{a_Q(f,f)+a_Q(g,g)}} .
\]
The **same** kinematic bounded operator
\[
B_{\rm kin}=I_{g,{\rm osc}}\otimes\mathcal F_2^{-1}
 (I_{\rm radial}\otimes|e_0\rangle\langle e_0|)\mathcal F_2
\]
strongly commutes with \(a,R_Q,P_1^2+P_2^2\) and hence with each original \(C_Q\). It preserves the smooth annular tests and intertwines the rigging. Its physical probabilities are
\[
p_Q=\frac{a_Q(f,f)}{a_Q(f,f)+a_Q(g,g)}
 \ne
\frac{a_{Q'}(f,f)}{a_{Q'}(f,f)+a_{Q'}(g,g)}.
\]
The angular support also lies in the earlier scalar-clock bridge sector. No identification of the two entire physical Hilbert spaces is needed to compare this common original observable.

The two outputs use different, still-unselected self-adjoint boundary completions. They are not contradictory predictions of one completed physical model. This common Dirac record is nonlocal; it is not a constructed detector.

## M5. Consequence

The action's differential expression, its compact core, the original rigging prescription, and the declared antiunitary symmetry do not yet select a unique physical boundary completion. BOUNDARY_INTERFACE supplies a complete way to parameterize and test the missing data. SPECTRAL_PREPARATION then separates normal spectral existence from preparation from a specified input. None of these logical distinctions is a new Core theorem or a completed old-source recovery.
