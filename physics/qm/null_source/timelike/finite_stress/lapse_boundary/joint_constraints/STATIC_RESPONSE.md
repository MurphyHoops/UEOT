# JC3 — Five missing directions of the actual static response

## 1. The operator being tested

Use exactly the stationary ground datum and mean solution of
[GROUND_DATUM.md](GROUND_DATUM.md). For a nearby spatial metric
\(\gamma'\), take its static positive-gap coupled ground state and the
same local renormalization prescription. Write
\[
 Qh=D_\gamma\langle T_{nn}\rangle[h],\quad
 Lh=\nabla^i\nabla^jh_{ij}-\Delta{\rm tr}\,h-2{\rm tr}\,h,\quad
 {\cal A}h=Lh-16\pi G_NQh .                                       \tag{1}
\]
This includes the actual change of the prepared ground mean. It is not
the frozen-source operator \(L\).

The static mean map is differentiable and spatial-Diff-natural on a
positive-gap neighborhood. One construction uses the parameter-dependent
elliptic heat kernel: subtract the finitely many local small-time terms
before differentiation and use the positive gap at large time.
Its local finite tensors obey the same covariance. This is a statement
about a covariant renormalized mean, not about differentiability of all
these vacua in one fixed bare Fock representation.

If a finite spectral construction is used away from the round metric,
its Riesz projector, eigenbasis and volume form must vary together.
A frozen projector is not automatically covariant. The special
first-order projected Ward identity in METRIC_RESPONSE.md is valid
because its round unperturbed generator commutes with that projector;
it is not an all-orders substitute.

## 2. The four first-harmonic range conditions persist

Let \(Z_A=x_A|_{S^3}\), \(A=1,\ldots,4\). Then
\[
 \nabla_i\nabla_jZ_A=-Z_A\gamma_{ij},\quad \Delta Z_A=-3Z_A,\quad
 L^*Z_A=0 .
\]
Since \(2Z_A\gamma={\cal L}_{-\nabla Z_A}\gamma\), spatial naturality and
constant background density give \(Q(2Z_A\gamma)=0\).

For completeness this also implies the needed adjoint statement, not
merely one zero column. \(SO(4)\)-equivariance says
\(Q^*:E_1\to\Gamma({\rm Sym}^2T^*S^3)\) intertwines representations.
At a point the \(SO(3)\) stabilizer restricts \(E_1\) as \(1\oplus3\),
whereas a symmetric tensor is \(1\oplus5\). Frobenius reciprocity leaves
only \(Q^*Z=cZ\gamma\). Pairing with \(2Z\gamma\) gives
\(6c\int Z^2=0\), hence
\[
 \boxed{Q^*Z_A=0,\qquad {\cal A}^*Z_A=0.}                         \tag{2}
\]
This conclusion applies to any differentiable, equivariant,
spatially natural metric-only prepared-mean family at the invariant
background. It does not cover independent preparation or apparatus
columns.

## 3. At the signed static ground background there is a fifth condition

The stationary Hellmann–Feynman identity in the same datum gives
\[
 \delta E=-\frac{p_0}{2}\int{\rm tr}\,h\,dV
 =\int Qh\,dV+\frac{\rho_0}{2}\int{\rm tr}\,h\,dV .
\]
Thus
\[
 \int Qh=-\frac{\rho_0+p_0}{2}\int{\rm tr}\,h,\qquad
 \int Lh=-2\int{\rm tr}\,h.
\]
The mean pressure equation is \(8\pi G_N(\rho_0+p_0)=2\), so
\[
 \boxed{{\cal A}^*1=0.}                                         \tag{3}
\]
The codomain therefore has at least the five missing directions
\(1,Z_1,\ldots,Z_4\). We have not proved this is its complete cokernel
or proved invertibility on the complement.

This fifth condition is specific to the static ground construction.
For a metric-dependent finite ramp output,
\(\delta E\) also contains the actual preparation-state variation;
the ground Hellmann–Feynman equation cannot be imported.

In a lapse variation \(\delta g_{00}=-2\nu\),
\(\delta\rho=\delta T_{00}-2\nu\rho_0\). Also
\(\delta(\sqrt\gamma\rho)=\sqrt\gamma(Qh+\rho_0{\rm tr}\,h/2)\).
The corresponding volume term on the geometric side cancels using the
signed background equation. Omitting only one side would create a false
extra range direction.

## 4. Independent state columns exist, at a positive cost

An exact global example makes the distinction concrete. In the plus
normal field put \(\mu=r\), \(Y_0=1/\sqrt{V_0}\),
\(Y_1=2Z/\sqrt{V_0}\),
\(\omega_0=\sqrt{1+\mu}\), \(\omega_1=\sqrt{4+\mu}\), and
\[
 U_\epsilon=\exp[\epsilon(a_0^\dagger a_1^\dagger-a_0a_1)] .
\]
This normal finite-mode squeeze changes the complete bare source state,
preserves Hadamard regularity and has all final coupled-energy moments.
It is a global reference gate, not a local autonomous actuator.

Writing \(n=\sinh^2\epsilon\), \(s=\sinh2\epsilon\), its exact field
differences are
\[
 F=\delta\langle\Phi^2\rangle
 =n(Y_0^2/\omega_0+Y_1^2/\omega_1)+sY_0Y_1/\sqrt{\omega_0\omega_1},
\]
\[
 P=\delta\langle\pi^2\rangle
 =n(\omega_0Y_0^2+\omega_1Y_1^2)-s\sqrt{\omega_0\omega_1}Y_0Y_1,\quad
 K_{ij}=n\,\partial_iY_1\partial_jY_1/\omega_1 .
\]
At this real squeeze slice the symmetrized \(q,p\) covariance vanishes,
so \(\delta T_{0i}=0\). The complete remaining tensor is
\[
 \delta\rho=\tfrac12[P+{\rm tr}K+(1+\mu)F]-\Delta F/6,
\quad
 \delta T_{ij}=K_{ij}-\nabla_i\nabla_jF/6+
 \gamma_{ij}[P-{\rm tr}K+(1-\mu)F]/6 .
\]
The odd density is \(CsY_0Y_1\), where
\[
 C=\frac{2+\mu-\omega_0\omega_1}{2\sqrt{\omega_0\omega_1}}
 =-\frac{\mu}{2\sqrt{\omega_0\omega_1}
                (2+\mu+\omega_0\omega_1)}<0 .                   \tag{4}
\]
For a smooth momentum code of strength \(\eta\), profile \(f\), let
\(J=\int Zf^2/2\). Its dipole is \(\eta^2J\), while this squeeze contributes
\(Cs/2\). Therefore
\[
 \epsilon=\tfrac12{\rm arsinh}(-2\eta^2J/C)                       \tag{5}
\]
cancels that dipole exactly. Rotate \(Y_1\) to treat any four-vector.
Its positive preparation energy and energy variance are
\[
 E_{\rm prep}=(\omega_0+\omega_1)n,\qquad
 {\rm Var}(H)_{\rm prep}=(\omega_0+\omega_1)^2s^2/4 .
\]
Since \(n=(\sqrt{1+s^2}-1)/2\leq s^2/4\), the energy is \(O(\eta^4)\),
while the energy standard deviation is \(O(\eta^2)\).
A later certificate constructs a genuine smooth local source pulse;
that pulse has a different, nonzero momentum column.

## 5. A common preparation cannot cancel both codes' homogeneous cost

Keep the same final Hamiltonian \(H_r\geq e(r)\), and a common normal
finite-energy input \(\varrho\). For
\(D_\pm=\exp[\pm i\eta\Phi_s(f)]\), exact conjugation gives
\[
 E_\pm-e=(E_\varrho-e)+\frac{\eta^2\|f\|^2}{2}
             \ \pm\eta\langle\Pi_s(f)\rangle_\varrho .
\]
Their average is at least \(\eta^2\|f\|^2/2>0\). For the centered
ground-based preparations each code separately has this positive cost.
A noncentered preparation can cancel one selected code; this is why the
**common preparation / both codes** qualification is necessary.

Consequently, a proposed expansion with metric and extrinsic-curvature
changes only of order \(\eta^2\), and with the above fixed-H common state
preparation, cannot cancel the homogeneous order-\(\eta^2\) source using
\({\cal A}\). A successful first-harmonic repair does not close this
additional range condition. This is not a no-go theorem for a changed
total Hamiltonian, binding energy, genuine mixed constraints or an
interacting apparatus.

## 6. The next geometric order must be retained

Allow \(\gamma_\eta=\gamma+\eta h_1+\eta^2h_2\) and
\(K_\eta=\eta K_1+\cdots\). After the first-order equations, the constant
projection at second order contains
\[
 \int\left[
 \tfrac12D^2R[h_1,h_1]+({\rm tr}K_1)^2-|K_1|^2
 -16\pi G_N(\rho_{\rm enc}+\rho_{2,\rm response})\right]dV=0.       \tag{6}
\]
Here \(\rho_{2,\rm response}\) includes **all** state, metric, normal,
counterterm and apparatus terms. The \(h_2\) part disappears by (3).
For instance a constant \(K_1=\kappa\gamma\) supplies \(6\kappa^2V_0\)
and makes the geometric linear momentum row vanish; the full row
additionally requires the corresponding matter momentum response to
vanish. That quantum-state response has not been computed. The positive second radius
derivative in GROUND_DATUM.md provides another exact diagnostic.

Equation (6) is a second-order range balance. It is not identified with
a full Einstein KID/Taub theorem, not a construction of a common
nonstatic history, and not a quantum constraint solution.

A static-ground Cauchy covariance for an ultrastatic spatial metric is
not automatically Hadamard for an arbitrary nonstatic spacetime with
the same spatial metric and extrinsic curvature on one slice. Its
ultraviolet Cauchy symbols also depend on the actual operator and
metric jets. The allowed second-order directions above still require
a legitimate history and state transport.
