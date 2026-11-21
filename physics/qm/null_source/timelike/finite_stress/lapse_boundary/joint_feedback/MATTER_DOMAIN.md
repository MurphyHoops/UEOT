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

## M3. Two nonzero, different positive-band projections exist

A whole positive bounded band cannot be declared physically irrelevant for every allowed domain. More precisely, for every nonempty bounded open interval \(I\), there are two \(J\)-compatible self-adjoint extensions for which \(E_I(R_Q)\) are nonzero and different. A finite union of such intervals is handled by selecting an interior interval.

Here is a proof specialized to the already present symmetric operator. Let
\(\mathcal H_s=\overline{\operatorname{span}}\{\ker(S^*-z):\Im z\ne0\}\);
its orthogonal complement is the self-adjoint part. The standard defect transport
\[
T_{z,w}=I+(z-w)(R_Q-z)^{-1}
\]
maps \(\ker(S^*-w)\) onto \(\ker(S^*-z)\). It shows that \(\mathcal H_s\) reduces every extension. The identity
\(D(S)=D(R_Q)\cap D(R_{-Q})\)
then shows it reduces \(S\). Its restriction is a nonzero simple symmetric operator, and it is \(J\)-invariant.

Suppose all the band projections on this simple part were zero. For \(\lambda\) strictly inside \(I\), every extension has a spectral gap at \(\lambda\), so \(S_s-\lambda\) is bounded below and has closed range. If it were onto, solving
\((S_s-\lambda)x=(S_s^*-\lambda)y\)
would imply \(D(S_s^*)=D(S_s)\), contradicting simplicity and its nonzero defect. Thus \(\ker(S_s^*-\lambda)\ne0\). Select a nonzero \(J\)-real member \(y\). In its von Neumann decomposition, the negative defect component is \(Jx_+\); choosing a \(J\)-adapted \(Q\) with \(Qx_+=Jx_+\) puts \(y\) in its extension domain. That extension has eigenvalue \(\lambda\), a contradiction. Some band projection is therefore nonzero.

Choose such an extension \(Q_0\). A smooth compact spectral function in \(I\) is nonzero on it; norm-resolvent continuity under small \(J\)-adapted boundary phases preserves nonzero band projection nearby. Suppose all nearby band projections were the same \(P\). Phase variations along each real vector of the adapted defect conjugation imply that \(P\) commutes with the corresponding rank-one defect maps, their adjoints and their products. Hence \(P\) is the same scalar \(0\) or \(1\) on the positive and negative defect spaces. Defect transport extends that scalar to \(\mathcal H_s\). Since \(P\ne0\), it must be \(I\) on the simple part.

But then the extension's spectrum on that part is contained in bounded \(I\), so it is a bounded self-adjoint operator there. Its closed dense restriction \(S_s\) would also have full domain, making \(S_s\) self-adjoint, again a contradiction. There must be a nearby nonzero, different band projection.

This proof establishes domain ambiguity in the original positive spectral sector. It does **not** prove an absolutely continuous spectral density on either old-source band.

## M4. A common original Dirac observable distinguishes physical outputs

The ambiguity can be read after the actual original rigging, not only through the auxiliary Lorentzian record. For common annular tests with
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
