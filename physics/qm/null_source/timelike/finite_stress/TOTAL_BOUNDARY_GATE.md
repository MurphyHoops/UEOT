# The total-source boundary gate: energy concentration and nonlinear compatibility

This entry tests the next proposed closure after BOUNDARY_STATE. It retains
the original two-field source and the static endpoint background A. It does
not introduce another clock, lattice, ordering or gravitational action.

The genuinely new quantitative application is an upper bound on the OLD
complete source plus an independent apparatus concentrating in the narrow
energy band of the new source-only candidate. The general spectral facts
used below are standard. The normal additive-constraint obstruction is
already present in the frozen QUANTUM_FLOOR/RELATIONAL entries; it is reused,
not counted as a new discovery. The nonlinear Ward identity and all-order
incoming obstruction are also frozen. Their explicit quadratic kernel is
a useful new corollary, not a new existence theorem.

## 1. Fix the complete endpoint observable

Let H_s be (65), including its one finite c-number E_c, and let H_a be a
self-adjoint apparatus Hamiltonian. Define
\[
 H_\Sigma=H_s\otimes I+I\otimes H_a
\tag{82}
\]
by the joint spectral calculus of the strongly commuting tensor factors.
Equivalently it generates the product unitary group. Its self-adjoint
spectral-sum domain need not equal D(H_s) intersect D(H_a), particularly
when opposite unbounded energies can cancel.

The same static full-space average is
\[
 \bar\rho_{\rm total}=H_\Sigma/V,\qquad V=V_0A^3 .
\]
Even a localized apparatus contributes H_a/V to this spatial monopole,
not H_a divided by its own small occupied volume. Local density observables
are different tests. Added mean apparatus stress must also satisfy the
mean equations; the original on-shell A is not automatically preserved.

Assume a complete preparation unitary U STRONGLY commutes with all spectral
projections of H_Sigma. This is a substantive closed-energy contract.
Merely having an autonomous H_full, or zero expectation of interaction
energy at two endpoints, does not prove it. A genuine endpoint scattering
intertwiner could provide the corresponding law, but is not built here.
A changed background, a persistent interaction, boundary flux or hidden
work source needs its own complete Hamiltonian and stress calculation.

## 2. The complete energy law is preserved, without moment assumptions

For every normal joint density R, correlated or otherwise, and every
bounded Borel function f,
\[
 {\rm Tr}(URU^\dagger)f(H_\Sigma)
       ={\rm Tr}R f(H_\Sigma).
\tag{83}
\]
This follows directly from strong commutation, cyclicity of the trace,
and boundedness of f(H_Sigma). Thus
\[
 \chi_{\Sigma,\rm out}(t)=\chi_{\Sigma,\rm in}(t),
 \quad \chi_\Sigma(t)={\rm Tr}R e^{itH_\Sigma}.
\]
All interval probabilities and bounded energy records are preserved;
finite mean, variance, compact support or a discrete apparatus spectrum
are unnecessary. In a fixed geometry, subtracting any fixed gravitational
target energy and dividing by V preserves the same conclusion for the
global density residual.

For an initial product R=rho_s tensor rho_a the probability law is
mu_Sigma=mu_s*mu_a and chi_Sigma=chi_s chi_a. Define
\[
 Q_\mu(\ell)=\sup_x\mu([x,x+\ell]),\qquad \ell>0 .
\]
Then
\[
 Q_{\Sigma,\rm out}(\ell)=Q_{\Sigma,\rm in}(\ell)
              \le Q_s(\ell).
\tag{84}
\]
Indeed mu_Sigma(I)=integral mu_s(I-e) dmu_a(e), and every shifted
interval has length ell. This is a complete-probability statement
stronger than the finite-variance ledger (81). Initial source-apparatus
correlations invalidate the convolution step, but not (83).

For reference, the inherited unfiltered two-ring law gives the exact
characteristic function
\[
 \Phi(q)=
 {e^{iq/(1-iq/\nu_0)}
  +e^{i(1+\sqrt3/2)q/(1-iq/\nu_0)}
  \over2(1-iq/\nu_0)} .
\]
For the frozen zero/high product source with its eight thermal shell
oscillators (and also the energy-degenerate NOON coherence change),
\[
 \chi_{\rm old}(t)=
 e^{itE_c}\Phi(\kappa_E t)
 [1+n(1-e^{it\varepsilon_2})]^{-8},
 \qquad \kappa_E={K_2\over2A^3}.
\tag{85}
\]
This is the frozen Gaussian moment-generating law evaluated on the
imaginary axis, with the full thermal energy distribution; it is not a
finite cumulant truncation. For an independent apparatus multiply by
its actual chi_a. An arbitrary correlated input cannot be assigned that
product merely because its marginal characteristic functions are known.

## 3. A rigorous small-band rejection for the actual old preparation

Under the current unfiltered input, R=P^2/K2 is the equal mixture of two
two-dimensional Gaussian radial laws. The squared center radii are
R_j=1 and 1+sqrt(3)/2, and the normalized covariance is I/(2 nu0).
The complete R law has not been cut off. Each radial density is
\[
 f_j(r)=\nu_0 e^{-\nu_0(r+R_j)}
          I_0(2\nu_0\sqrt{rR_j}),\qquad r\ge0.
\]
Here I0(z)=pi^{-1} integral_0^pi exp(z cos theta)dtheta.
The elementary inequality 1-cos(theta)>=2 theta^2/pi^2 gives, for z>0,
\[
 I_0(z)\le{e^z\sqrt\pi\over2\sqrt{2z}} .
\]
When r>=R_j/4 this implies
\[
 f_j(r)\le
 {\sqrt{\pi\nu_0}\over4(rR_j)^{1/4}}
 e^{-\nu_0(\sqrt r-\sqrt{R_j})^2}
 \le{\sqrt{\pi\nu_0}\over2\sqrt{2R_j}}
 \le M,\quad M={\sqrt{\pi\nu_0}\over2\sqrt2}.
\]
When r<R_j/4, the simpler I0(z)<=exp(z) gives
f_j(r)<=nu0 exp(-nu0/4). The frozen nu0>=16 and
exp(nu0/4)>nu0^2/32 imply this is <32/nu0<=2<M.
This also handles r=0. The convex mixture therefore has density bounded
by M everywhere.

Changing variables H_z=kappaE R gives a global energy density bound
M/kappaE. The frozen independent high-mode energy and any independent
apparatus energy are convolutions; neither can increase that bound.
Under (82)-(83), for every interval I of length ell,
\[
 \Pr_{\rm out}\{H_\Sigma\in I\}
 \le \min(1,\ell M/\kappa_E).
\tag{86}
\]
This does not assume an apparatus energy sign or finite energy moments.
It does assume the displayed frozen zero/high product input and an
initially independent apparatus. For other correlations use their
actual full spectral law.

The BOUNDARY_STATE example has sigma=epsilon2/100 and its SOURCE energy
is entirely in an interval of width 2 sigma. Substituting ell=2 sigma
in (86) gives an outward-certified bound of approximately 2.0e-7 for
the CLOSED TOTAL energy to lie in ANY interval of that width. The exact
interval is in total_boundary_gate.json.

Consequently a source-only support probability of one cannot be
transferred to the complete device/source. If a target joint normal state
tau has total-energy support inside such an interval, measuring that
energy event gives
\[
 D_{\rm tr}(\rho_{\rm total,out},\tau)
 \ge1-\min(1,2\sigma M/\kappa_E).
\tag{87}
\]
This is a distance for the SAME total-energy observable on the SAME
endpoint representation. It is not a lower bound on the distance to the
new source marginal alone. A successful selected output supported in
that total interval can have probability at most the same bound when
all failed outcomes are retained in the complete conserving process.
With leakage at most epsilon in the successful conditional output the
bound is divided by 1-epsilon.

For a global density tolerance +/-epsilon_rho use ell=2 V epsilon_rho.
The supremum over centers prevents a mere constant recentering from
evading the bound. A record-dependent geometry or target energy is new
joint boundary data and is not covered by this fixed-target conclusion.

## 4. Correlations do not manufacture a normal exact energy surface

The frozen QUANTUM_FLOOR already excludes a normal exact additive
constraint in this source representation and RELATIONAL distinguishes
its physical-Hilbert-space alternative. Here is a short endpoint proof
that makes the apparatus scope transparent.

The H_s point spectral projection at every E vanishes: on each countable
Fock occupation sector it is multiplication by P^2/(2A^3)+a constant,
and its level set has two-dimensional Lebesgue measure zero. For a simple
tensor psi tensor phi, the spectral measure of H_Sigma is the convolution
mu_psi^s * mu_phi^a. Thus
\[
 \langle\psi\otimes\phi,\Pi_\Sigma(\{E\})
                 \psi\otimes\phi\rangle
 =\int\mu_\psi^s(\{E-e\})\,d\mu_\phi^a(e)=0 .
\]
The projection is positive and simple tensors have dense linear span,
so Pi_Sigma({E})=0 as an operator. Every normal joint state, including
entangled states, therefore has a non-atomic total-energy law.
No energy moments or sign assumption on H_a were used.

This excludes a normal exact delta energy law in this FIXED-BACKGROUND,
DECOUPLED-ENDPOINT tensor representation. It gives no uniform positive
variance floor across arbitrary changing marginals. If the complete old
source marginal and its finite dilation moment are held fixed, the
stronger frozen uncertainty floor still applies and cannot be evaded by
claiming arbitrary initial anticorrelation. Distributional constraint
solutions with a new physical inner product, sustained interactions
with bound states, and a full coupled gravitational Hamiltonian are
not excluded by this endpoint argument.

A further simple resource distinction is useful. If H_a is bounded below
and the old source marginal has its full unbounded upper energy tail,
then H_Sigma also has unbounded upper support, even for a correlated
initial state. By (83) the final total support remains unbounded. If
the outgoing source has the compact band of (68), the outgoing apparatus
must consequently have unbounded upper energy support. This is not a
claim of infinite mean or variance: a distribution can have unbounded
support and finite moments of every order. A bounded-band apparatus
cannot make this exact transformation under the displayed contract;
finite-error versions must retain the corresponding total-energy tail.

## 5. The nonlinear incoming escape must also satisfy pressure

Read the frozen exact mean functional and its Ward identity, not a
new adiabatic guess rho(a). In conformal time, a=A exp(u), h=u',
\[
 E=h^2+1-\tfrac23 a^2\rho,\qquad
 S=h'+\tfrac12(h^2+1)+a^2p,\qquad
 E'+hE=2hS .
\tag{88}
\]
The actual same-state covariant conservation rho'+3h(rho+p)=0 proves
this identity. The old incoming domain fixes E0=S0=0 and E1=0;
S1[u]=P(partial_eta)u is the frozen complete response, including its
declared state transport and local terms.

Define E(epsilon v)=epsilon^2 E2[v]+O(epsilon^3), with no hidden
factorial. Expansion of (88) gives
\[
 E_2'[v]=2v'Pv .
\]
On the old positive-frequency, no-constant incoming space,
\[
 E_2[v]=2\partial_\eta^{-1}(v'Pv).
\tag{89}
\]
For modes with positive rates r,s the associated symmetric bilinear
kernel is
\[
 K_E(r,s)={rP(s)+sP(r)\over r+s}.
\tag{90}
\]
It is P(r) on the diagonal. For the classical comparison P(r)=r^2-4,
it reduces to rs-4. No old mode or geometry ODE is rerun.

The frozen complete factorization
P(r)=-Q(r^2)(r^2-s_*^2)(r^2-sigma_F^2), Q>0,
and sigma_F/s_*>468087 show that the quadratic form is indefinite OFF
shell: r=2s_* gives positive E2 and r=2sigma_F gives negative E2.
But any combination of the actual incoming linear root directions has
Pv=0 and therefore E2[v]=0. Off-shell sign flexibility is not a
constraint solution.

In particular, suppose a separately specified small-source extension
has nonzero density forcing epsilon b+o(epsilon), pressure forcing
O(epsilon), the same leading mean functional and old incoming domain,
and a regular expansion u_epsilon=sqrt(epsilon)v+O(epsilon).
The leading pressure equation requires Pv=0. Equations (89)-(90) then
give E(u_epsilon)=o(epsilon), unable to match epsilon b.
Merely announcing a sqrt(source width) scale does not close this
candidate. This is a necessary compatibility result for that explicit
expansion, not an all-model prohibition of nonanalytic or nonlinear
quantum backreaction.

At a finite initial slice, integrating E2' permits a genuine constant
charge C2. Its value is NOT provided by the old inverse derivative.
Decaying modes, initial state-memory data or nonzero constant geometry
data require the actual new finite-slice RSET and Ward calculation.
The kernel (90) is not extended through r+s=0 by fiat. The annulus
zero/shell energy correlation also has different metric dependence in
its components; its total static energy width cannot be substituted
time by time for a single fluctuating zero-mode mean parameter.

The frozen all-order E=e^{-u}C result and the earlier exclusion of merely
randomizing incoming growth amplitudes remain inherited results. We do
not count them again as new solutions or exclusions.

## 6. The next constructive contract is now narrower

A usable finite-slice proposal must supply one actual total boundary
object, its common metric/state transport, and the nonzero singlet
constraint data from its declared action. It must state which original
condition is changed: the complete matter marginal, the static incoming
past, the tensor representation, the interaction/energy-exchange
contract, or the physical gravitational law. Changing one does not
silently waive the others.

The concrete next calculation is the finite-slice homogeneous
constraint map and the initial CTP boundary blocks for that object,
including C_boundary and its cross correlations. A classical choice
C_boundary=-xi is not an actual quantum density. A thin matter energy
band does not quiet the full closed apparatus. The old incoming modes
do not supply the missing quadratic charge. The new candidate must
pass these gates before the already nonzero NOON pressure difference
can be propagated into an absolute gravitational baseline and then
into a calibrated local instrument.

These conclusions do not remove the valid deterministic mean-SCE
history or the source-only family. They also do not prohibit local
pressure contrasts within energy-degenerate sectors. Complete
geometry-matter-device dynamics and physical unification remain OPEN.

## Sources and exact inheritance

- BOUNDARY_STATE.md and its new source-bound JSON: actual annulus state,
  homogeneous influence and finite source-only budgets.
- ../joint_history/HISTORY.md and history.json: the unfiltered two-ring
  law, covariance convention, source product and common normalization.
- ../constraint_states/POSITIVE_CLOCK.md: inherited radial moment-generating law.
- ../constraint_states/QUANTUM_FLOOR.md and RELATIONAL.md: inherited normal
  additive-constraint obstruction and the distinct physical inner product.
- ../nonlinear_history/EXISTENCE.md, SELECTION.md, history.json,
  selection.json: exact same-state Ward identity, root separation and
  previously established all-order incoming obstruction.

The analytic measure and domain proofs are not machine-formal proofs.
The new script checks their algebraic normalization, new intervals,
source identities and scope; three native read-only agents check the
actual committed text separately.
