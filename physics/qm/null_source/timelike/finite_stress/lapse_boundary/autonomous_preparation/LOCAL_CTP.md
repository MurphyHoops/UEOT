# AM. A positive finite-cutoff joint CTP object and its preparation obstruction

## AM1. Concrete stable local member

Choose the AL potential on unit ESU with effective quadratic masses one,
\(g=1/10\), and all four quartic coefficients
\(\alpha=\beta=\kappa=\eta=\lambda=1/10\). The effective mass one can, for
example, come from zero bare masses and conformal curvature couplings.
Write \({\cal R}=\chi^2+\phi^2+\psi^2\). The raw potential is
\[
 V=\frac12{\cal R}+\frac1{10}\chi\phi\psi+\frac1{40}{\cal R}^2 .
\]
Since \(|\chi\phi\psi|\le{\cal R}^{3/2}/(3\sqrt3)\),
\[
 \boxed{V\ge\frac1{80}{\cal R}^2+\frac{133}{270}{\cal R}.}   \tag{AM.1}
\]
Indeed the minimum of \(r^2/80-r/(30\sqrt3)\) is \(-1/135\).

Expand all three real fields in all harmonics of frequency \(k\le K\).
There are \(d_K=3\sum_{k\le K}k^2=K(K+1)(2K+1)/2\) real coordinates.
This is a finite-mode cutoff, but \(L^2(\mathbb R^{d_K})\) remains infinite
dimensional. Let
\[
 H_K^{\rm raw}=\tfrac12\sum_jp_j^2+
       \tfrac12\int\sum_A|\nabla\varphi_{A,K}|^2dV+
       \int V(\varphi_K)dV .
\]
Orthonormality and Cauchy-Schwarz imply
\[
 \int V\ge |q|^4/(80V_0)+(133/270)|q|^2 .
\]
The kinetic-plus-potential quadratic form is densely defined and closed
on the intersection of \(H^1\) with the weighted \(L^2\) potential domain.
Its Friedrichs operator is self-adjoint and semibounded.
Local Rellich compactness and the \(R^{-4}\) tail bound give compact
embedding of its form domain, hence compact resolvent.
The form construction uses the standard Friedrichs theorem; see Teschl,
*Mathematical Methods in Quantum Mechanics*, §2.3,
[author's text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf).
The model-specific coercivity estimate is (AM.1).

The free conformal product vacuum \(\Omega_K\) is a normal Gaussian vector.
Polynomial multiplication and differentiation preserve the Schwartz
space. Such vectors are in the Friedrichs operator domain by form
integration by parts, so iteration puts \(\Omega_K\) in \(D(H_K^n)\)
for every finite \(n\) at fixed \(K\). No bound uniform in \(K\) is inferred.

## AM2. Same density operator, exact CTP positivity

Use this one common \(\rho_K=|\Omega_K\rangle\langle\Omega_K|\), and
\(O_{\chi,K}=\frac12\int\chi_K^2dV\).
The latter is a self-adjoint multiplication operator. Define the exact
two-parameter pulse family
\[
 U_K(\tau,s)=e^{-i\tau H_K}e^{-isO_{\chi,K}},
\qquad
 Z_K(a,b)=\operatorname{Tr}[U_K(a)\rho_KU_K(b)^\dagger].      \tag{AM.2}
\]
A homogeneous lapse history enters by its proper-time integral \(\tau\).
The \(s\) pulse is a diagnostic instantaneous mass-source insertion; it
is not asserted to be a smooth local apparatus or an autonomous preparation.

For arbitrary finite histories \(a_i\) and coefficients \(c_i\),
\[
 \sum_{ij}\bar c_i c_j Z_K(a_i,a_j)
 =\operatorname{Tr}[A\rho_KA^\dagger]\ge0,\qquad
 A=\sum_i\bar c_iU_K(a_i).
\]
Also \(Z_K(a,a)=1\) and \(Z_K(a,b)^*=Z_K(b,a)\).
These exact statements hold for any normal positive trace-one \(\rho_K\);
no moment or Gaussian assumption is needed for positivity itself.
The doubled-contour use of one initial density operator is standard;
see Berges, [hep-ph/0409233](https://arxiv.org/abs/hep-ph/0409233), §3.1.
The finite-cutoff Gram proof here supplies the precise positivity statement.

At the chosen Gaussian origin \((\tau,s)=(0,0)\), first, second and mixed
vector derivatives exist: every finite word in \(H_K,O_{\chi,K}\)
maps the Gaussian into Schwartz space. The symmetric second derivative
of attenuation is the covariance matrix of \(H_K,O_{\chi,K}\):
\[
 -\log|Z_K(\epsilon u,0)|
  =\tfrac12\epsilon^2u^\mathsf TN_Ku+o(\epsilon^2).
\]
This derivative statement is not extended to arbitrary normal states or
all histories without a domain proof. The same \(H_K\) gives exact total
energy conservation for homogeneous lapse evolution.
A spatial spectral cutoff does not preserve all local diffeomorphism Ward
identities. This construction does not assert the full local Einstein
constraints.

## AM3. Exact source-containing initial mixed block

Let \(C_K(x,y)=\langle\chi_K(x)\chi_K(y)\rangle\),
\(\sigma_K^2=C_K(x,x)=K(K+1)/(4V_0)\), and
\(J_m=\int dV_xdV_y\,C_K(x,y)^m\).
Then \(J_2=K/4\), and
\[
 \langle O_{\chi,K}\rangle=\frac{K(K+1)}8,\qquad
 \operatorname{Var}O_{\chi,K}=\frac K8.                     \tag{AM.3}
\]
The free Hamiltonian acts by an eigenvalue on \(\Omega_K\), and the
cubic term is odd. Gaussian contractions give
\[
 \operatorname{Cov}({\cal R}(x)^2,\chi(y)^2)
     =20\sigma_K^2 C_K(x,y)^2,
\]
\[
 \operatorname{Cov}({\cal R}(x)^2,{\cal R}(y)^2)
     =120C_K(x,y)^4+600\sigma_K^4C_K(x,y)^2 .
\]
It follows that
\[
 {\cal C}_K:=\operatorname{Cov}_{\rm sym}(H_K,O_{\chi,K})
       =\frac{5\lambda\sigma_K^2K}{8}
       =\frac{K^2(K+1)}{64V_0}\quad(\lambda=1/10),           \tag{AM.4}
\]
\[
 \operatorname{Var}H_K
   =g^2J_3+\frac{15\lambda^2}{2}J_4+
                        \frac{75\lambda^2}{8}\sigma_K^4K.
                                                               \tag{AM.5}
\]
Here \(J_3\ge0\) is the squared norm of the cubic free-vacuum vector;
\(J_4\ge0\) directly. The \(2\times2\) matrix \(N_K\) is strictly positive:
\[
 \operatorname{Var}H_K-\frac{{\cal C}_K^2}{K/8}
   =g^2J_3+\frac{15\lambda^2}{2}J_4+
                         \frac{25\lambda^2}{4}\sigma_K^4K>0.
\]
Thus a source-containing mixed lapse/mass block really occurs in one
positive normal finite-cutoff state. It was not independently assigned
as a cross-noise coefficient. It is not the geometric charge-matching
condition, and the mass derivative port is not a metric pressure column.

## AM4. Complete energy, Wick terms and the actual UV preparation gate

The raw free-vacuum energy contains both the full free zero-point sum
and the interaction expectation:
\[
 \langle H_K^{\rm raw}\rangle
 =\frac32\sum_{k\le K}k^3+
        \frac{3K^2(K+1)^2}{128V_0}
 =\frac{3K^2(K+1)^2}{8}
        +\frac{3K^2(K+1)^2}{128V_0}.                       \tag{AM.6}
\]
No scalar subtraction has been silently made. A chosen scalar subtraction
changes this mean and the CTP phase, but does not change the covariance
results. Its gravitational role must be fixed in a common renormalization
contract.

The variance of the raw model obeys
\[
 \operatorname{Var}H_K\ge
       \frac{3K^3(K+1)^2}{512V_0^2}.                       \tag{AM.7}
\]
This does not disappear just because every individual cutoff has a normal
density operator and positive CTP kernel.

Wick ordering is a different operator, not a scalar subtraction:
\[
 :{\cal R}^2:
 ={\cal R}^2-10\sigma_K^2{\cal R}+15\sigma_K^4 .
\]
Its cutoff-dependent quadratic counterterm exactly cancels (AM.4) on the
same Gaussian vacuum. Thus the initial mixed block is renormalization-
and preparation-dependent; the raw positive coefficient is not a
universal physical prediction.

Even after this Wick ordering, the fixed nonzero quartic four-particle
component remains. Its squared norm is \((15\lambda^2/2)J_4\). Scalar
and quadratic counterterms lie in orthogonal particle sectors and cannot
cancel it on this input. Cauchy-Schwarz on the product slice gives
\(J_4\ge J_2^2/V_0^2=K^2/(16V_0^2)\), hence
\[
 \boxed{\operatorname{Var}_{\Omega_K}(H_{K,\rm Wick})
    \ge\frac{15\lambda^2K^2}{32V_0^2}
     =\frac{3K^2}{640V_0^2}\quad(\lambda=1/10).}             \tag{AM.8}
\]

There is also a direct \(K^5\) lower bound. On a geodesic ball
\(\gamma\le1/K\), \(\sin(k\gamma)\ge k\gamma/2\) and
\(\sin\gamma\le\gamma\), so
\(C_K\ge K(K+1)/(8V_0)\).
The ball volume is at least \(\pi/(3K^3)\). Hence
\[
 J_4\ge\frac{\pi K(K+1)^4}{12288V_0^3},\qquad
 \operatorname{Var}_{\Omega_K}(H_{K,\rm Wick})
 \ge\frac{\pi K(K+1)^4}{163840V_0^3}\quad(\lambda=1/10).
\]
Both estimates refer to the same orthogonal four-particle component.

The same orthogonal-sector lower bound survives any additional scalar
or quadratic counterterm at fixed quartic coefficient. This rejects graph
recovery using precisely the fixed vacuum vectors \(\Omega_K\) for the stated sequence after
those adjustments. It does not reject other correlated preparations,
running quartics, other representations or all continuum theories. It also
does not exclude a different correlated recovery sequence converging to
the same Hilbert-space vector, if such a sequence can actually be proved.

## AM5. The sharp mass pulse itself fails the required normal cutoff limit

For this same free vacuum, the exact characteristic function is
\[
 \langle e^{-isO_{\chi,K}}\rangle
  =\prod_{k\le K}(1+is/(2k))^{-k^2/2}.
\]
For fixed \(s\ne0\),
\[
 \log|\langle e^{-isO_{\chi,K}}\rangle|
  =-\frac14\sum_{k\le K}k^2\log(1+s^2/(4k^2))
  =-\frac{s^2K}{16}+O_s(1).
\]
The last estimate follows from the summable \(k^{-2}\) error in
\(\log(1+u)=u+O(u^2)\).
For the nested cutoff difference \(2K\) versus \(K\), the tail overlap
therefore also tends to zero. Even allowing arbitrary scalar phases,
\[
 \|e^{i\alpha_{2K}}e^{-isO_{\chi,2K}}\Omega-
      e^{i\alpha_K}e^{-isO_{\chi,K}}\Omega\|^2\longrightarrow2.
                                                               \tag{AM.9}
\]

The actual nested tail has the explicit bound
\[
 |\langle\Omega,V_K(s)^\dagger V_{2K}(s)\Omega\rangle|
 \le\exp\!\left[-\frac{Ks^2}
 {16(1+s^2/[4(K+1)^2])}\right].
\]
It follows from \(\log(1+x)\ge x/(1+x)\), not from an assumed phase
renormalization. The distance squared after any scalar phases is at least
two minus twice the right-hand side.

The same interacting raw Hamiltonian also gives the exact pulse energy
cost. With \(D_\chi=\frac12\sum(p_\chi q_\chi+q_\chi p_\chi)\),
\[
 V_s^\dagger H_KV_s=H_K-sD_\chi+s^2O_{\chi,K},\qquad
 \Delta\langle H_K\rangle=\frac{s^2K(K+1)}8 .
\]
All coordinate potentials commute with the pulse, and the free Gaussian
has \(\langle D_\chi\rangle=0\). A scalar energy subtraction does not
change this increment.

For comparison, on the same free vacuum a centered time-smearing of this
mass port satisfies
\[
 \operatorname{Var}O_\chi(g)=\frac18\sum_{k\ge1}|\widehat g(2k)|^2<\infty
 \quad(g\in C_c^\infty).
\]
This free observable comparison does not construct the full interacting
smooth-source unitary. It prevents promoting the sharp-pulse failure to
a statement about every smooth local source.

This instantaneous pulse has no strong normal Fock unitary cutoff limit.
It is a concrete failure of the proposed sharp port, not of smooth
time-supported local mass interactions. A pointwise positive limiting
Gram function by itself would not restore the missing continuity and
normal implementation.

## Acceptance and next work

Accepted: a stable raw finite-mode local Hamiltonian, one common normal
preparation, exact CTP positivity, an actual initial mixed covariance and
its precise counterterm dependence. Rejected: the fixed free-vacuum graph
recovery and the sharp mass kick as routes to the required continuum.
Next: use smooth source histories and a correlated interacting preparation,
with the complete AL action and all finite renormalization data fixed.
Prove joint state/propagator and smeared stress limits before transferring
the Ward or Einstein constraints. Physical unification remains open.
