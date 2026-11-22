# JC18 — A fixed autonomous clock actuator: normal finite-mode construction and full cost

## Decision and scope

There is a surviving nonlinear autonomous model which programs the same eight compact source profiles through its initial state. At each fixed spectral cutoff it has a self-adjoint Hamiltonian, normal initial state, conserved complete energy law and a controlled approximation of bounded records. A concrete K=64 example retains a positive binary record. Its controller energy is enormous in model units, its finite-cutoff dynamics is not exactly local, and it does not yet repair the eight actual unbounded constraint means. A four-dimensional continuum device, its metric response, and a self-consistent gravitational background remain open.

This is a new input/apparatus model. No old AQ or AP apparatus is silently replaced, no success outcomes are discarded, and no continuum theorem is inferred from a finite-dimensional construction.

## 1. First reject the insufficient single free program

A minimal massive controller Y of mass M, with mean \(g\langle Y\rangle=q(t)Z\), obeys
\[
 q''+(M^2+3)q=0
\]
before backreaction. Thus a nonzero compact pulse h=epsilon b+zeta b' cannot be its free mean. Let L=partial_t^2+(M^2+3). For any free solution q on an interval containing the support,
\[
 \|q-h\|_2\ge {\|Lh\|_2^2\over\|L^2h\|_2}>0
\]
when h is nonzero. This follows by testing q-h against L^2h, integrating by parts with flat boundary data, and Cauchy--Schwarz. Merely reducing the coupling does not remove this fixed-program floor. Supplying an external forcing Lh/g would introduce another source with its own stress.

## 2. A single Hamiltonian for all eight program parameters

Keep the conformal doublet with \(\Phi_+=(\phi+\psi)/\sqrt2\), masses squared +/-r and unit ESU. Add a **minimal massless** scalar X and two minimal mass-one scalars Y_0,Y_1. The X zero mode is a normal Gaussian wave packet, not a nonexistent massless oscillator vacuum.

Using the same b as LOCAL_PREPARATION, fix once and for all
\[
 F_0(s)={b(s)\over\cos2s},\qquad F_1(s)={b'(s)\over\cos2s}
 \quad (|s|<.2),
\]
and extend both by zero. The denominator stays positive; b and every endpoint derivative are flat, so F_j are smooth compact functions. Define the time-independent local interaction potential
\[
 V_{\rm int}={g\over2}[Y_0F_0(gX)+Y_1F_1(gX)]\Phi_+^2
       +{g^2\over4}[F_0(gX)^2+F_1(gX)^2]\Phi_+^4.                \tag{1}
\]
Neither epsilon nor zeta appears in this Hamiltonian.
Units here use the declared fixed mass/radius scale. If a fixed mass scale
M_* is restored, the cubic is (g M_*/2) sum Y_j F_j(gX/M_*) Phi_+^2,
the quartic is (g^2/4) sum F_j(gX/M_*)^2 Phi_+^4, and Y has mass M_*.
The F arguments are scalars; no external coordinate clock occurs in the
action. M_* is a fixed parameter, not a metric-dependent coupling.

At the chosen initial time t_i, put the controllers in coherent/wave-packet data whose free means are
\[
 X_{\rm cl}=t/g,\quad
 Y_{0,\rm cl}=(\boldsymbol\epsilon\cdot Z)\cos2t/g,\quad
 Y_{1,\rm cl}=(\boldsymbol\zeta\cdot Z)\cos2t/g .
\]
The free Y dipole frequency is two. Along these means the quadratic body source in (1) is exactly
\[
 s_{\rm ref}(t,x)=[b(t)\boldsymbol\epsilon+b'(t)\boldsymbol\zeta]\cdot Z.
\]
This equality defines a reference evolution. At finite g the full interacting controller does not remain a free coherent state.

## 3. Stability, self-adjointness and a legitimate initial density

Pointwise,
\[
 {Y_0^2+Y_1^2\over2}+V_{\rm int}
 ={1\over2}\sum_{j=0}^1[Y_j+\tfrac g2F_j(gX)\Phi_+^2]^2
       +{g^2\over8}\sum_{j=0}^1F_j(gX)^2\Phi_+^4\ge0.             \tag{2}
\]
The body masses on this fixed ESU have positive oscillator gaps. At common finite field cutoff K, all fields in (1) are the same truncated coordinate fields. The complete bare positive Hamiltonian is a Schrödinger operator on a finite-dimensional Euclidean configuration space, with real smooth nonnegative potential and standard kinetic energy. All potential derivatives grow at most polynomially, because every derivative of F_j is bounded.

Essential self-adjointness on compactly supported smooth functions follows, for example, from Shubin, arXiv:math/0007019, Theorem 1.1: the configuration space is complete, the magnetic potential is zero, the positive potential is locally square integrable and its negative part is zero. Its unique closure equals the Friedrichs realization. This is an application in finite mode space, not a construction of an interacting four-dimensional quantum field.

Schwartz functions lie in the domain of every power: the differential expression maps Schwartz space into itself, cutoff approximation identifies it with the maximal self-adjoint domain, and induction gives the claim. The initial normal product of the X zero-mode Gaussian, its higher-mode vacuum, the Y coherent states, and the AP body vacuum therefore has all finite-K total energy moments. The exact unitary preserves the complete Hamiltonian spectral law between the externally specified encoder/readout interventions.

## 4. Whole-joint approximation, including controller fluctuations

Use the moving Weyl frame of the free controller means. The reference vector is the free X/Y fluctuation state tensor the **actual** prescribed quadratic-pulse body state.
For this vector-norm comparison the finite-K reference Hamiltonian has
the same static additive constant as the autonomous Hamiltonian, with
the source-only time-dependent scalar counterterm phase explicitly
removed. That known phase does not affect its density, covariance or
instrument predictions. If it were left in the reference vector,
an extra scalar residual would have to be included in (3). Put xi=X-X_cl and upsilon_j=Y_j-Y_j,cl. The quadratic-source residual is
\[
 g\sum_j\upsilon_jF_j(t+g\xi)
 +\sum_j\cos2t(\mathbf v_j\cdot Z)
               [F_j(t+g\xi)-F_j(t)],\qquad
 (\mathbf v_0,\mathbf v_1)=(\epsilon,\zeta).
\]
The functional-calculus inequality
\(|F_j(t+g\xi)-F_j(t)|\le |g|\,\|F_j'\|_\infty|\xi|\)
is valid for the self-adjoint point field at fixed K. No factorization between xi and F_j(xi) is assumed. Controller/body factors are independent in the reference vector.

Let T be the total comparison time, \(v_\Phi,v_X,v_Y\) be uniform pointwise variance/moment envelopes in that reference, and set M_j=||F_j||infinity, L_j=||F_j'||infinity. Minkowski's inequality and Gaussian fourth/eighth moments give the Duhamel bound
\[
 \delta_K(g)\le |g|C_{1,K}+g^2C_{2,K},                            \tag{3}
\]
\[
 C_{1,K}={\sqrt3 V_0T v_\Phi\over2}
 [\sqrt{v_Y}(M_0+M_1)+
      \sqrt{v_X}(\|\epsilon\|L_0+\|\zeta\|L_1)],
\]
\[
 C_{2,K}={\sqrt{105}V_0T v_\Phi^2\over4}(M_0^2+M_1^2).
\]
Here delta bounds the norm difference of complete normalized pure vectors; it also bounds their trace distance. The reference remains in the domain needed for Duhamel by its finite-mode Gaussian moments. The same argument applies piecewise through the common encoding unitary; small displacement means can be included in v_Phi. A subsequent identical complete CPTP instrument contracts trace distance.

This is a finite-K, finite-time bound. It neither controls an unbounded stress observable by itself nor supplies a uniform ultraviolet limit. Its use is analogous to the coherent-frame Duhamel estimates in Hepp, Commun. Math. Phys. 35 (1974) 265, equations (2.15)--(2.20); that paper's field examples do not prove a four-dimensional limit for (1).

## 5. Explicit K=64 example and retained record

Choose
\[
 K=64,\ t_i=-1,\ t_{\rm encode}=\pi,\ t_{\rm read}=\pi+3,\ T<8,
 \quad \eta=10^{-13},\quad g=10^{-40},\quad \|u\|\le10^{-16}.
\]
Use the scaled reader sigma=1/(10 eta), and the same common program for the two code signs.

The bump estimates \(I>5/7,\ \|w'\|_\infty<11/5\) give
\[
 \|a\|_\infty<14,\ \|a'\|_\infty<308,\ \|a'\|_1<28,
\]
\[
 \|b\|_\infty<14,\quad\|b'\|_\infty<308,\quad
 \|b''\|_\infty<8624.
\]
Since cos(2s)>.9 and |sin(2s)|<.4 on the support,
\[
 M_0<16,\ M_1<343,\ L_0<357,\ L_1<10^4.                          \tag{4}
\]
For a clock zero-mode initial position variance a=4,
\[
 v_X\le{a+T^2/(4a)\over V_0}
       +{1\over2V_0}\sum_{k=2}^{64}{k^2\over\sqrt{k^2-1}}<65,
\]
\[
 v_Y={K(K+1)\over4V_0}<55,\quad
 \sigma_{\Phi,K}^2={1\over2V_0}\sum_{k=1}^{64}{k^2\over\sqrt{k^2+1/5}}.
\]
The actual reference source amplification is bounded by e^(2 L), with
\(L\le29\|u\|/\sqrt{1.2}\); the cap-code displacement is tiny. The safe even-moment envelope \(v_\Phi<60\) covers the entire reference, including the code. Equations (3)--(4) give
\[
 C_{1,64}<4\,10^7,\quad C_{2,64}<2\,10^{11},\quad
 \delta_{64}(10^{-40})<5\,10^{-33}.                              \tag{5}
\]

The mean-transfer kernel is state independent. With cap gradient bound 22/5, its actual spectral tail at elapsed time 3 satisfies
\[
 |\mu-\mu_K|\le{(22/5)^2\over(K+1)^2-1}
 \left[{3\over8(K+1)^2}+{\sqrt5\over16(K+1)^3}\right].
\]
This follows by differentiating sin(3 sqrt(k^2+s))/sqrt(k^2+s) in s, and using the cap gradient bounds on both high-mode tails. At K=64 the upper bound is 4.091371517744365e-7, so the independently recomputed continuum lower bound gives mu_K>3.3864e-5. The new reference covariance is the one bounded in PREPARED_RECORD, not an imported AQ covariance.

The reference complete binary probability difference exceeds 2.70e-30. For each code sign the full state error is at most delta, so the actual instrument's difference is at least d_ref-2 delta:
\[
 \boxed{d_{\rm actual,K=64}>2.69\,10^{-30}.}                     \tag{6}
\]
All outcomes, the full controllers, and the body are retained. Finite spectral cutoff does not have exact spacelike locality, so (6) is not called a local continuum experiment. Nor is it claimed measurable with available apparatus.

## 6. Full energy and noise accounting

The free classical controller energy is
\[
 E_{\rm controller,cl}={V_0\over2g^2}
 (1+\|\epsilon\|^2+\|\zeta\|^2).
\]
For (5) this is below 1.01e81. To obtain a complete initial positive-Hamiltonian bound also retain:

- all finite-mode zero-point energies, whose combined sum is below 1e8;
- the clock zero-mode packet kinetic energy 1/(8a)=1/32;
- the actual initial interaction. Its cubic expectation is zero by SO(4) symmetry and integral Z=0, even though finite-g clock tails are present. Its quartic expectation is positive and below 6e-71, using (4) and the Gaussian fourth moment.

Thus the **complete finite-K positive Hamiltonian** initially has mean below 1.02e81. This useful bound includes unrenormalized oscillator constants; it is not a new covariant gravitational subtraction prescription. Its large classical clock term persists independently of those constants.

The exact Hamiltonian is even under simultaneous body parity. The actual initial body is even, so before encoding the linear momentum mean is zero. The two opposite momentum codes have identical complete energy laws and add exactly eta^2 ||f_K||^2/2 to the mean. They do not change the potential because that potential depends only on coordinate fields.

For the complete Gaussian reader, every potential term in (1) commutes with the receiver coordinate. Let v=25 eta^2 and c=||g_K||^2<=1. Gaussian momentum-kick averaging gives the exact identities
\[
 \Delta\langle H_{\rm total}\rangle=vc/2,\qquad
 \Delta{\rm Var}(H_{\rm total})=
 v\langle\Pi_\psi(g_K)^2\rangle+v^2c^2/2.
\]
The positive Hamiltonian controls the actual momentum moment by 2 E_pos. Retaining the 1.02e81 margin proves the latter increment is below 1e57. This is only a conservative increment bound; the actual total variance also includes the controller's initial variance and the code. It is not the ideal source-only variance bound 65 eta^2. Norm approximation has not been used to transfer an energy moment.

The clock's classical stress alone is
\(\rho_X=p_X=1/(2g^2)\).
It is not an eta^2 perturbation of the signed AP mean background, and a cosmological constant cannot cancel its enthalpy. A background which includes this source must be solved anew before the fixed-ESU pulse/record calculations can be used gravitationally.

## 7. Total Ward identity and what a spectral cutoff preserves

The untruncated classical action for X,Y and the conformal body is local and covariant. Its complete tensor includes every controller tensor and
\(-g_{\mu\nu}V_{\rm int}\). On its untruncated classical equations the total divergence vanishes; the matter/controller energy exchange has equal and opposite contributions. A continuum renormalized quantum tensor for this nonpolynomial model is not constructed here.

At finite spectral K, the local equations contain P_K of the nonlinear forces. If field A has interaction force F_A, then the divergence of the formally local complete tensor contains the projection residual
\[
 -\sum_A\operatorname{sym}((1-P_K)F_A,\partial_\nu\Phi_{A,K}).
\]
This residual must remain in local tests. Its full spatial energy integral is zero because each canonical velocity lies in Ran P_K. Likewise the SO(4) Killing charges are conserved, since their generators commute with the common cutoff and the interaction is invariant. Exact total Hamiltonian spectral conservation is therefore established without asserting a false finite-cutoff local Ward identity.

For a complete energy split H_m+H_c, including the interaction in one specified side, the transfer operators satisfy dot H_m=-dot H_c exactly. Every common time-smearing has covariance matrix
Var(W_f) times [[1,-1],[-1,1]]. The source and controller transfer noises cannot be made independent.

In the declared initial Gaussian domain the transfer variance is strictly
positive. Put Q_X=integral sym(sum F_j(gX)F_j'(gX),Pi_X). The quartic-clock
part of W has a four-body-quanta component in the plus-field k=1 mode
equal to
\[
 {g^3\sqrt{24}\over8\omega_1^2V_0^2}\,Q_X\chi_X .
\]
The other transfer terms contain only Phi_+^2 and cannot cancel it.
The clock packet has full support and uniform mean momentum 1/g;
the real part of Q_X chi_X contains (1/g) integral sum F_j F_j' times
chi_X. This functional is not identically zero since sum F_j^2 is a
nonzero compact function. Hence Var_initial(W)>0. This statement concerns
the common initial finite-K Schwartz domain, not all evolved sharp
products or a continuum noise kernel.

## 8. The program overlap is not the external-source CTP kernel

Changing the program means changes the controller's initial state. For two eight-vectors u_+,u_-, the modulus of their Y coherent overlap is
\[
 |\langle P(u_-),P(u_+)\rangle|
   =\exp[-V_0\|u_+-u_-\|^2/(8g^2)].
\]
A single autonomous unitary preserves the full joint overlap exactly. It therefore cannot be replaced by the generally different external-source AP kernel
\(\langle U[h_-]\Omega,U[h_+]\Omega\rangle\) of SOURCE_CTP. Even as g tends to zero, the former usually tends to zero while nearby external histories have a kernel near one.

The proof of (6) uses a fixed common program and two body codes. A two-branch metric/source calculation must keep the actual controller initial mixed block and its entire interaction history. The source-family CTP phase is not transferred by a single-program norm estimate.

## 9. Conditional clock resource bound and next gate

For the free homogeneous reference clock define
\(\tau(t)=gQ_0(t)/\sqrt{V_0}\). Then
\[
 [\tau(t_1),\tau(t_2)]=ig^2(t_2-t_1)/V_0.
\]
If both times separated by T are required to have RMS clock error at most delta_t, Robertson's inequality implies
\[
 g^2\le2V_0\delta_t^2/T,\qquad
 E_{\rm clock,cl}\ge T/(4\delta_t^2).
\]
This is conditional on this particular free-clock resolution contract. It is not a universal lower bound inferred from a binary record gap.

The next minimum gate is to control actual weighted stress moments and their program derivatives, obtain a legitimate continuum limit with the apparatus source, and solve the geometry with the controller included. The finite-K bounded-record construction is complete; the geometry--matter--apparatus closure is not.
