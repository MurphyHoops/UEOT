# A scalar-matter clock: self-adjoint constraint and positive normal solution space

This is a separately declared finite-K quantization sector. It uses the
original zero mode T=phi_1 as a clock, the original square ordering
eta=0, kappa on the whole real line, and a bounded open u interval
J_g=(u_-,u_+) whose closure avoids g_K=0. The artificial u-patch boundary
is now a boundary in geometric configuration space. It is not the old
physical time boundary. No equivalence to the positive-kappa u-clock
quantization, no unique boundary law, and no old-state embedding is assumed.

## M1. Derivation from the original phi action

Return to the original lapse action and its phi-coordinate one-form.
Pi_g is the pure geometric canonical momentum from GEOMETRIC_MOMENTUM.
Write p_r=-i partial_phi_r and choose T=phi_1, P_T=p_1. The same formal
constraint before division by kappa is
\[
 {\cal C}=P_T^2/(2a^2)+C_{\rm rest},\qquad
 C_{\rm rest}=\kappa\Pi_g+{(P_\kappa-A_K)^2\over2g}
 +\sum_{r\ne1}\left({p_r^2\over2a^2}
             +{a^2\omega_r^2\phi_r^2\over2}\right)+V_{\rm geom},
\]
\[
 A_K=B_K-\mathfrak h_K\kappa^2/4,\quad
 V_{\rm geom}=d_0+d_1\kappa^2+d_3\kappa^4.                  \tag{M1}
\]
The other zero mode has omega=0. The same d0,d1,d3 include all counterterms
and the frozen nonzero U0; nothing is borrowed from an independently
reselected history. The source-dependent connection in q coordinates
has disappeared through the actual coordinate/endpoint transformation,
not through deleting source terms.

In H_rest=L²(J_g du x R d kappa x R^(n-1) dphi) define on the dense
smooth compact test space D0
\[
 R_0=-2a C_{\rm rest}a
 =-\{\kappa a^2,\Pi_g\}-{a^2\over g}(P_\kappa-A_K)^2
 -\sum_{r\ne1}p_r^2-a^4\sum_{r\ne1}\omega_r^2\phi_r^2
 -2a^2V_{\rm geom}.                                      \tag{M2}
\]
It is symmetric. The original wavefunction is Psi=a Phi and
\[
 2a\,{\cal C}(a\Phi)=(P_T^2-R_0)\Phi.                      \tag{M3}
\]
M3 is a congruence, not a unitary equivalence. Extending eta kappa^-3
from the old clock would introduce an additional singular constraint
term at kappa=0, so this entry makes no claim for that extension family.

## M2. Existence and actual nonuniqueness of self-adjoint extensions

The antiunitary conjugation
(J psi)(u,kappa,z)=overline{psi(u,-kappa,z)}
has J²=1 and preserves D0. Under it Pi_g and kappa both change sign;
P_kappa is fixed because reflection and conjugation each reverse it;
A_K is even; the other momenta occur squared. Hence J R0=R0 J.
It commutes with the closure S of R0 and its adjoint and exchanges
N_+=ker(S*-i) with N_-=ker(S*+i).

This alone proves equal deficiency indices. In fact both are infinite.
Put b=kappa a². The u part is i(2b partial_u+b').
Smooth functions F_+(u),F_-(u) with endpoint values (0,1) and (1,0),
respectively, times compact kappa packets away from zero and Schwartz
source packets belong to D(S*). For these vectors the boundary form is
\[
 { \langle\psi,S^*\varphi\rangle-\langle S^*\psi,\varphi\rangle\over2i}
 =\left[\int\kappa a^2\overline\psi\,\varphi\,d\kappa\,dz\right]_{u_-}^{u_+}.
                                                                  \tag{M4}
\]
Choose arbitrarily many disjoint kappa packets supported in kappa>0.
The F_+ subspace is positive definite for M4; F_- is negative definite,
with arbitrarily large finite dimensions. D(S) lies in the radical.
The von Neumann decomposition of D(S*)/D(S) has positive and negative
indices dim N_+ and dim N_-, so both are infinite (countably so by
separability). This proves nonuniqueness; it does not merely fail to
prove uniqueness.

Choose any orthonormal basis e_j of N_+. The map
U_def(sum c_j e_j)=sum c_j J e_j is a **linear** unitary N_+->N_-;
it is not the antilinear J itself. Every unitary N_+->N_- supplies a
self-adjoint extension R_U with
D(R_U)=D(S) dotplus (I+U_def)N_+ and
R_U(f+x+U_def x)=Sf+i x-i U_def x.
No explicit deficiency basis or physically preferred U_def is computed.
The primary extension theorem is used only in its general mathematical
role; the present operator is not the separable bipartite model of that
reference.

## M3. Both spectral signs occur in every extension

For a normalized compact test psi0 supported in kappa>0, put
psi_n=e^(inu)psi0. Directly from M2,
\[
 \langle R_U\rangle_{\psi_n}
 =\langle R_0\rangle_{\psi_0}-2n\langle a^2\kappa\rangle_{\psi_0}.
                                                                  \tag{M5}
\]
All these vectors lie in every extension. Thus every extension has
spectrum unbounded in both directions. Its positive spectral subspace
is nonzero. There exists at least one finite band
E=1_[lambda0,lambda1](R_U) not equal to zero with
0<lambda0<lambda1<infinity. A particular preassigned band is not
guaranteed nonempty. This spectral construction has not determined the
old source or geometry marginal in that band.

## M4. The original kinematic constraint also has a self-adjoint realization

On L²(R_T) tensor H_rest, use the joint spectral calculus to define
K=P_T²-R_U. It is self-adjoint on the domain
integral (k²-lambda)² d||psi(k,lambda)||²<infinity.
This domain allows cancellation and must not be replaced by the
intersection of the two separate operator domains.

Because J_g is bounded, B=a^-1 is bounded, self-adjoint and boundedly
invertible. Therefore
\[
 C_U={1\over2}B K B,\qquad
 D(C_U)=\{\Psi:B\Psi\in D(K)\}                              \tag{M6}
\]
is self-adjoint and extends the original formal C on compact tests.
For completeness, in the adjoint-domain test put z=B x.
Bounded invertibility makes ||x|| and ||z|| equivalent, so
x-><K Bx,By> is bounded precisely when By belongs to D(K*).
This gives (BKB)*=BK*B on exactly the displayed domain. The same
invertibility gives closedness. M6 is not a unitary conjugation.

The kinematic kernel is zero. In the joint spectral representation
the mass shell {k²=lambda} has Lebesgue k measure zero for every lambda;
Fubini therefore gives ker K=0, hence ker C_U=0.
Nevertheless 0 is in the continuous spectrum. Choose a positive
spectral point lambda of R_U, R_U spectral packets near lambda and
P_T Fourier packets near +sqrt(lambda). Their product gives normalized
approximate-zero vectors for K. Multiplication by a and renormalization
transports them to approximate-zero vectors for C_U with uniformly
bounded norm factors. Self-adjointness and the empty kernel imply
continuous, rather than residual or point, spectrum at zero.

Consequently a physical normal state below is normal on the physical
solution space. It is not a trace-one kinematic density supported on
a nonexistent zero eigenspace.

## M5. A positive scalar-clock solution space and an explicit rigging form

Fix one extension and a nonzero band E as above. On H_E=E H_rest put
Omega=sqrt(R_U)|_HE. It is bounded, strictly positive and boundedly
invertible. Positive P_T=-i partial_T solutions have the sign
\[
 (S\xi)(T)=a\,e^{+i(T-T_0)\Omega}(2\Omega)^{-1/2}\xi,\quad \xi\in H_E.
                                                                  \tag{M7}
\]
The plus phase is essential. The original-variable conserved current is
\[
 (\Psi_1,\Psi_2)_{\rm phys}
 =-i\int a^{-2}\{\overline\Psi_1\,\partial_T\Psi_2
                   -(\partial_T\overline\Psi_1)\Psi_2\}\,du\,d\kappa\,dz.
                                                                  \tag{M8}
\]
On M7 it equals <xi1,xi2>. It is not the flat norm of Psi or simply
integral a^-2 |Psi|².

Here is a direct, positive constraint-annihilating rigging construction.
For clarity set T0=0. Use
Phi_test=Cc∞(R_T x J_g x R_kappa x R^(n-1)_z).
It is contained in D(C_U) and invariant under the differential C;
multiplication by a and a^-1 also preserves it. Define the Bochner map
\[
 {\cal T}_C f=(2\Omega)^{-1/2}
    \int_{\mathbb R}e^{-i\Omega T}E[a f(T)]\,dT,\qquad
 \eta_C(f,g)=\langle{\cal T}_C f,{\cal T}_C g\rangle.         \tag{M9}
\]
There is no 1/sqrt(2pi) in this time integral. With the unitary Fourier
convention the map has an overall sqrt(2pi).
Then <S xi,f>_distribution=<xi,T_C f>, and M8 has exactly the same
normalization as M9. Integration by parts twice, using
a C f=K(a^-1 f)/2 and E R_U=Omega² E, proves T_C C f=0.
The form is positive and Hermitian.

Its range is dense in H_E. Take a nonnegative unit-integral compact
smooth time test h supported sufficiently near zero that its Fourier
transform has no zero on [sqrt(lambda0),sqrt(lambda1)].
The corresponding bounded spectral multiplier is invertible on H_E;
a D0=D0 and E D0 is dense. Thus the completion of
Phi_test/ker T_C is precisely H_E. Density, rather than surjectivity of
the compact-test range, is all that is needed.

For any trace-one normal density rho0 on H_E,
rho_T=e^(+i Omega(T-T0))rho0 e^(-i Omega(T-T0)) is normal and trace-norm
continuous. The original solution kernel is
a(2Omega)^-1/2 e^(i Omega(T-T0))rho0
 e^(-i Omega(T'-T0))(2Omega)^-1/2 a.
This gives a definite normal physical history and a positive tested
constraint solution in the declared sector.

M5a below identifies the positive-band Abel group average of the selected
original C_U. The full refined-algebraic observable intertwining axiom
for general geometry/source readings is not claimed.
Time translation/P_T polynomials intertwine as their band multipliers.
General geometry/source readings need their transported physical
observables and an actual instrument; a raw |Psi|² marginal is not
automatically that probability.

## M5a. Abel group averaging of the actual bounded-congruence constraint

This also connects the direct rigging to the chosen original C_U, in a
precise frequency-test sector. Let I=(r0,r1) be a bounded open interval
with 0<r0<r1 and E_I=1_(I²)(R_U) nonzero. It may be chosen to contain
the closed band used above. Use Fourier tests with k in I and compact
smooth geometric/source coefficients:
Phi_I=F_T^-1[Cc∞(I) tensor D0]. They are Schwartz, not compact, in T.
They are C-invariant and dense in this positive clock-momentum sector.
Use M9 with E_I; its completed range is E_I H_rest. Open-band endpoints
are excluded explicitly rather than silently discarding spectral atoms.

With the unitary time-Fourier convention and B=a^-1, the fiber resolvent is
\[
 (C_U(k)-i\varepsilon)^{-1}
 =2a\,(k^2-R_U-i\varepsilon D)^{-1}a,\qquad D=2a^2.          \tag{M10}
\]
D is bounded positive and boundedly invertible; it need not commute
with R_U. Put V_epsilon(t)=exp[t(iR_U-epsilon D)].
The bounded-perturbation Volterra construction and
partial_t||V_epsilon(t)psi||²=-2epsilon<D> give a contraction semigroup.
Duhamel gives ||V_epsilon(t)-exp(itR_U)||<=epsilon||D||t.
Thus, for a smooth compact scalar h(E),
\[
 A_\varepsilon(E)=(E-R_U-i\varepsilon D)^{-1}
 =i\int_0^\infty e^{-itE}V_\varepsilon(t)\,dt,
\qquad
 \int h(E)\operatorname{Im}A_\varepsilon(E)dE
       \longrightarrow\pi h(R_U)                         \tag{M11}
\]
in operator norm. Indeed the difference of the integrated Laplace
representatives is bounded by epsilon||D|| times
integral_0^infinity t |integral h(E)e^(-itE)dE| dt, which is finite.
Fourier inversion and spectral calculus identify the limiting imaginary
part. Real and imaginary parts of h give the general sesquilinear case.

For finite simple Fourier tests apply M11 to
h(E)=overline{fhat_j(sqrt(E))}ghat_l(sqrt(E))/(2sqrt(E)).
Changing variables E=k² proves, with exactly the M9 normalization,
\[
 \boxed{\lim_{\varepsilon\downarrow0}{1\over2}
 \int_{\mathbb R}e^{-\varepsilon|s|}
 \langle f,e^{isC_U}g\rangle\,ds
       =\langle{\cal T}_{C,I}f,{\cal T}_{C,I}g\rangle.}      \tag{M12}
\]
Equivalently, (1/pi)Im(C_U-i epsilon)^-1 has limit
eta_C,I/pi on these tests. The factor 1/2 in M12 is a fixed normalization,
not a claim of a pointwise or operator-norm limit of delta(C_U).

The gauge orbit of the tests can also be included rigorously.
Let Phi_G=span{exp(isC_U)f:f in Phi_I,s real}.
For Q_epsilon=epsilon/(C_U²+epsilon²), Cauchy--Schwarz and
|exp(itx)-1|<=|tx| give
\[
 |\langle f,Q_\varepsilon(e^{itC_U}-I)g\rangle|^2
 \le\langle f,Q_\varepsilon f\rangle\,
                         \varepsilon t^2\|g\|^2\longrightarrow0.
\]
Hence the limiting form is gauge invariant and well defined on Phi_G,
with T_G(sum exp(is_jC_U)f_j)=sum T_C,I f_j. If two such presentations
give the same kinematic vector, positivity of the limiting form shows
that they give the same physical vector. Phi_G is both C-invariant and
gauge invariant. No compact coordinate support for its gauge translates
or convergence of the raw Bochner formula on every translate is assumed.

This is a bounded-congruence, selected-extension, positive-band Abel
result. It is not a theorem for arbitrary unbounded lapse rescalings.
The full observable algebra and the equivalence with the earlier
u-clock quantization still need their own domains and intertwiners.

## M6. What has and has not been recovered

The original action supports these finite-K self-adjoint constraint
realizations and nonzero positive normal solution spaces. The choice of
clock, whole-line kappa sector, artificial u patch, extension and band
are explicit additional quantization data. They have not been selected
by Core or by an apparatus.

The old thin bare source has a two-sided P1 distribution. A one-sided
clock input can be constructed at source level in ANGULAR_CLOCK_INPUT,
but that source construction has not been shown to lie in the image
of M7/M9 with the required old finite-u marginal. Nor has the original
mean geometry or pure geometric momentum budget been recovered.
The old positive-kappa u-clock obstruction is therefore not bypassed
by silently changing Hilbert space and inner product.

The next physical acceptance question is joint: an action-derived
choice of domain/extension, an explicit same-source state in its
physical image, the relational observables for its prepared slice,
and the complete source/geometry/device evolution. Existence of the
abstract band is one rigorous prerequisite, not that whole result.
