# Boundary matching is a genuine domain choice, with an exact raw-source bridge

This entry follows the complete finite-K scattering result at g_K=0.
It distinguishes a unitary identification of asymptotic data, an actual
self-adjoint domain of the relational operator, and an action-selected
physical boundary law. The first two are constructed. The last remains open.

## B1. All asymptotic identifications and the logarithmic convention

Let A_epsilon^ell map a normal reference slice vector on side epsilon
to its asymptotic profile, with
\[
 {\cal A}_\epsilon^\ell\chi_i=
 \mathop{\rm s-lim}_{u\to u_c^\epsilon}
 e^{\,2iA_\eta\log(|u-u_c|/\ell)}W^\dagger\chi(u).           \tag{B1}
\]
G_ZERO_BOUNDARY proves that both maps are unitary. The zero-mode frame
has a strong identity limit and commutes with A_eta, so no residual
source dilation is missing in B1.

Every unitary M from the left profile Hilbert space to the right one
defines a reference-slice unitary
\[
 T_M=({\cal A}_+^\ell)^\dagger M{\cal A}_-^\ell.             \tag{B2}
\]
It does not produce a strong continuous state at u_c in the original
slice representation; G_ZERO_BOUNDARY excludes that limit.

Changing the common convention ell to exp(c)ell sends A_epsilon to
exp(-2icA_eta)A_epsilon. The same physical map T_M is retained if
\[
 M\longmapsto e^{-2icA_\eta}M e^{2icA_\eta}.                 \tag{B3}
\]
Covariance under convention changes alone imposes no commutation.
Only the additional requirement that M itself be unchanged under every
such change implies strong commutation with A_eta. In the Hankel
representation, the geometry spectrum is simple, A_eta=k², and that
restricted class is precisely
\[
 M=\int_{k>0}^{\oplus}M(k)\,dk,
\]
with M(k) a measurable source-Hilbert-space unitary almost everywhere.

Even preserving the complete profile-source marginal for every input
does not make this choice unique: every M(k)=exp(if(k)) I_source,
with f real measurable, does so. For a concrete distinguishability test,
take two orthogonal smooth geometry spectral packets in disjoint
intervals E,F and the same normalized source vector s. Choose a smooth
phase equal to pi on E and zero on F. Identity matching sends
(f_E+f_F)s/sqrt(2) to itself, while phase matching sends it to
(-f_E+f_F)s/sqrt(2). The outputs are orthogonal normal states.
Both choices preserve the A_eta spectral law and the full profile-source
marginal. Their right-slice images remain orthogonal.
No finite unbounded-moment claim follows merely from wave-operator
surjectivity.

## B2. These choices can be realized as relational self-adjoint domains

Fix reference points u_i^- and u_i^+ and set
P(u)=U_bulk(u,u_i^epsilon) on the corresponding side of u_c.
This is a strongly measurable unitary fiber multiplier on
L²(R_u;H_slice). No value at the single point u_c is needed.

For any unitary J:H_slice->H_slice, let D_J=-i partial_u on the two
half-lines with H¹ regularity and trace condition f(u_c+)=J f(u_c-).
Multiplication by J on the right half-line conjugates the standard
self-adjoint full-line momentum to D_J. Thus D_J is self-adjoint,
has zero kernel and spectrum R. Define
\[
 {\cal L}_J=P D_J P^\dagger.                               \tag{B4}
\]
It is self-adjoint. On joint compact/Schwartz tests supported away
from u_c, the already proved weak dual Bochner identity gives
partial_u(P^\dagger phi)=P^\dagger phi'+iP^\dagger H_formal phi
as an H-valued derivative. Therefore L_J extends the same formal
P_u+H_rel, with no assumed original snapshot-domain transport.

The profile matching M corresponds to
J=(A_+^ell)^\dagger M A_-^ell. Thus B2 is more than a pair of states
arbitrarily written next to each other: it gives a family of distinct
self-adjoint relational domains. Kernel L_J is still zero on the
kinematic L²(du) space, while its slice-normal distributional solutions
are nonzero. This is the usual distinction between kinematic
eigenvectors and physical solution data.

No self-adjointness or equivalence of the original lapse constraint is
inferred through the unbounded kappa congruence. Nor does B4 repair the
singular division by g at the action level.

## B3. A raw-phi source marginal does have a normal boundary limit

The source label in B1 is initially the profile-frame tensor factor.
There is, however, an exact finite-K canonical bridge. Let T_a be the
unitary finite-mode coordinate dilation from original phi to q=a phi:
(T_a psi)(q)=a^(-n/2)psi(q/a). The original raw-phi density at a physical
slice is obtained from the bulk density by T_a^\dagger exp(-i kappa Q).
Since W=exp(i S_g(kappa)) exp(i kappa Q), and the first factor is purely
geometric, partial trace gives exactly
\[
 \rho_{\phi,\rm raw}(u)=T_{a(u)}^\dagger
          {\rm Tr}_{\kappa}[W^\dagger\rho_{\rm bulk}(u)W]T_{a(u)}.
                                                                  \tag{B5}
\]
The physical slice weight sqrt(kappa) commutes with this transformation.

The full scattering approximation extends to trace class by finite-rank
approximation. Partial trace is trace-norm contractive, and the free
Z acts only on geometry. Also a(u)->a_c is finite and T_a is strongly
continuous, hence acts trace-norm continuously on normal densities.
It follows that
\[
 \rho_{\phi,\rm raw}(u)\longrightarrow
 T_{a_c}^\dagger {\rm Tr}_{\kappa}\rho_{\rm as}\,T_{a_c}
 \quad\hbox{in trace norm}.                               \tag{B6}
\]
Thus joint geometry escapes every bounded kappa region while the
complete original-phi source marginal has a normal limiting density.
Preserving profile-source marginals on both sides does preserve this
raw-phi boundary marginal, because a_c is the same on both sides.

This is not preservation of the bulk q,p bare marginal, of the full
finite-u source history, or of every unbounded stress moment. Trace-norm
convergence controls bounded observables and spectral probabilities;
convergence of unbounded moments needs its own uniform-integrability
bound. The full joint state still has no normal boundary limit.

Surjectivity lets one pull a product profile state with any chosen
normal raw-phi boundary marginal back to a normal reference-slice state.
This is an existence statement in the declared physical slice Hilbert
space. It supplies neither the old geometric moments nor a local
autonomous preparation or an all-field limit.

## B4. Actual charge matching must use the transported observables

For self-adjoint source/geometric slice charges C_epsilon, define their
profile spectral projections by
E_epsilon^as(Delta)=A_epsilon E_Cepsilon(Delta) A_epsilon^\dagger.
Preserving their complete laws for every input is equivalent to
\[
 M^\dagger E_+^{\rm as}(\Delta)M=E_-^{\rm as}(\Delta)
 \quad\hbox{for all Borel }\Delta.                          \tag{B7}
\]
An untransported source tensor factor cannot replace B7.

There is one exact conditional restriction. If M strongly commutes
with A_eta and preserves the spectral projections of a profile charge
C_s, it commutes with their joint spectral projections. Every spectral
law of F(A_eta)-C_s, its zero-constraint probability and any legitimate
second-moment residual are unchanged. Phase entanglement such as
M(k)=exp[i f(k) C_s] can change coherences while leaving those joint
probabilities unchanged. This is not an Einstein-CTP no-go theorem:
A_eta has not been identified with the required physical boundary charge.

For any bounded profile-source observable B_s, scattering also gives
the genuine asymptotic dressed observable
\[
 \mathop{\rm s-lim}_{u\to u_c^\epsilon}
 U(u_i,u)W(I\otimes B_s)W^\dagger U(u,u_i)
 =A_\epsilon^\dagger(I\otimes B_s)A_\epsilon .
\]
It equals a corresponding bare-observable statement only where the
canonical transport justifies that identification.

## B5. The original g=0 action has not selected a matching law

The pre-Legendre action contains g(u) chi_acc²/2 and
Phi_kappa=P_kappa-A_K-Q=g chi_acc. A finite classical acceleration
trace implies Phi_kappa tends to zero at u_c. It does not license
replacing the entire quantum evolution with an extra constraint
Phi_kappa Psi=0 on an open time stratum.

In particular one must vary before setting g=0:
D(g chi_acc)=g D chi_acc+(Dg)chi_acc, with Dg=kappa/4, and the
u variation retains g' chi_acc²/2. These terms need not vanish there.
The original degenerate crossing variation and its allowed boundary
densities still require a separate construction.

If one nevertheless imposes the stronger raw finite-slice condition
Phi_kappa Psi=0, W^\dagger Phi_kappa W=P_kappa forces W^\dagger Psi
to be constant in kappa. Its physical norm integral kappa||Psi||² dkappa
diverges unless the vector is zero. This diagnoses that additional
condition; it is not a proof that the action requires it or a selection
of M. The next task is a same-action mixed boundary/charge map with its
physical domain, rather than another arbitrary unitary matching.
