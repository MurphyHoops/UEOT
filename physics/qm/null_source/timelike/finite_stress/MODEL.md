# Declared discrete-volume model and its continuum limit

## 1. Physical inputs and sign

This is a new homogeneous two-massless-zero-mode model. It retains the frozen
U0 and the original complete momentum law, but introduces a specified
K-quantization-inspired volume representation, a positive dust clock, a
spectral inverse volume and a factor ordering. It does not restore the
nonzero modes, the AE terms or a local preparation controller.

In the project's G_ab = 2 T_ab convention the Einstein-Hilbert coefficient
is 1/4. With unit S3 volume V0 = 2 pi^2, set v=a^3 and p_a=3a^2 p_v.
The proper-lapse classical gravitational Hamiltonian is
\[
 H_g=-{3v\over2V_0}p_v^2-{3V_0\over2}v^{1/3}+V_0U_0v.
\]
The two zero modes have K0=|P|^2/(2v). The declared dust constraint is
C=P_T+H=0 with P_T positive. Thus the physical Hamiltonian H is restricted
to its nonpositive spectral sector and the dust energy is -H. This sign is
derived from this constraint; it is not copied from a paper's differently
oriented Hamiltonian.

For fixed ell>0 choose delta=2ell and the positive orientation sector
v_n=delta n, n=1,2,... . On ell2(N), (S u)_n=u_(n-1), u_0=0, and
L=2-S-S*. Then 0<=L<=4 and
\[
 H_P=-\gamma\sqrt v L\sqrt v+qv-c_0v^{1/3}+{|P|^2\over2v},\quad
 \gamma={3\over8V_0\ell^2},\quad q=V_0U_0,\quad c_0={3V_0\over2}.
\tag{1}
\]
Zero volume decouples through the square-root factors; a boundary at a
strictly positive macroscopic volume has not been inserted. The positive
semilattice and the spectral inverse at nonzero volume are nevertheless
additional quantum representation inputs.

## 2. Self-adjoint family

On finite sequences, (1) is a real Jacobi operator with
\[
 a_n=\alpha\sqrt{n(n+1)},\quad
 b_n=bn-dn^{1/3}+\epsilon/n,
\]
\[
 \alpha=\gamma\delta,\quad b=(q-2\gamma)\delta,\quad
 d=c_0\delta^{1/3},\quad \epsilon=|P|^2/(2\delta).
\]
Since 1/sqrt(n(n+1)) >= 1/(n+1), the Carleman series diverges.
The minimal Jacobi operator is essentially self-adjoint. For each fixed
s=|P|^2, H_s=H_0+sD where D=diag(1/(2delta n)) is bounded. Hence the
self-adjoint domain is common to all s, and the resolvent identity gives
norm-resolvent continuity with bound
\[
 \|(H_s-z)^{-1}-(H_{s'}-z)^{-1}\|
 \le {|s-s'|\over2\delta|\operatorname{Im}z|^2}.
\]
The direct integral H over Lebesgue d2P is therefore well defined.
All subsequent states use this single measurable family, not independently
chosen boundary roots at different times.

## 3. Provenance and limits

Husain and Pawlowski, arXiv:1108.1147, section 3.2 equation (11), use
square-root-volume factors around a difference operator in dust time and
describe decoupled orientation/zero sectors. Their sign and normalization
are not asserted to be identical to (1).

Singh and Wilson-Ewing, arXiv:1310.6728v2, section II.C equation (2.44),
describe K quantization of closed FLRW, polymerizing extrinsic curvature
and retaining the classical curvature term. Section IV.A equation (4.9)
gives a spectral inverse that vanishes at zero volume and equals the
ordinary inverse otherwise. This supplies structural precedent, not a
derivation of all our choices. The closed FLRW F quantization of
Ashtekar, Pawlowski, Singh and Vandersloot (gr-qc/0612104) is inequivalent;
its extra spin-connection corrections cannot silently be omitted and
then attributed to that model.

If kappa=8piG and hbar=1 are restored, p_v=-2V0 Hubble/kappa.
For b_LQC=gamma_BI Hubble and holonomy lambda b_LQC, the canonical
parameter is ell=kappa gamma_BI lambda/(2V0). It is not directly the
area-gap length lambda, and gamma in (1) is not the Immirzi parameter.
The density scale is
\[
 \rho_c={4\gamma\over V_0}={3\over2V_0^2\ell^2}.
\]

## 4. Continuum ordering is not the old flat/LB operator

For fixed smooth test functions away from v=0, central differences yield
\[
 H_{\rm kin}\longrightarrow {3\over2V_0}\sqrt v\,\partial_v^2\sqrt v
\]
on L2(dv). This is consistency on these test functions, not a uniform
state/domain or finite-stress convergence theorem.

Set x=sqrt(v)=a^(3/2) and U psi(x)=sqrt(2x) psi(x^2). The transformed
kinetic operator is
\[
 {3\over8V_0}\partial_x^2-{9\over32V_0x^2}
 =c\partial_x^2-{3c\over4x^2},\quad c={3\over8V_0}.
\]
Thus its inverse-square coefficient is g_eff=P^2/(2c)-3/4, the previous
constant-weight family with beta=3 or -1, rather than beta=0 or 2.
The earlier finite-stress bad threshold becomes P^2>=2c=3/(4V0).
The full Gaussian has nonzero mass there. Also K0<=P^2/(2delta) is not
uniform as delta goes to zero. No full GR, AE or original-state continuum
limit is concluded.

## 5. Verification scope

model.py checks the canonical algebra, the actual unitary ordering
transformation and outward intervals for the critical scales. Carleman,
direct-integral and representation statements are analytic proofs supported
by standard Jacobi theory, not machine-formalized in this certificate.

## 6. Why a small expansion does not identify the classical branch

For the principal classical symbol,
Hkin=-3v sin2(ell p_v)/(2V0 ell2) and
Hubble=-sin(2ell p_v)/(2V0 ell).
Put y=-2V0 ell Hubble. On the branch cos(2ell p_v)>0, the kinetic
Legendre function is
\[
 L_{\rm low}={3v\over4V_0\ell^2}
       [1-\sqrt{1-y^2}-y\arcsin y]
 =-\tfrac32V_0v\,{\rm Hubble}^2+O({\rm Hubble}^4).
\]
Near the opposite band edge, after subtracting the total derivative
pi dot(v)/(2ell), it is
\[
 L_{\rm edge}={3v\over4V_0\ell^2}
       [1+\sqrt{1-y^2}+y\arcsin y]
 =4\gamma v+\tfrac32V_0v\,{\rm Hubble}^2+O({\rm Hubble}^4).
\]
At criticality the constant 4gamma v cancels the vacuum contribution
in the reduced Lagrangian, while the quadratic sign differs from the
low branch. This explains the parity construction's positive gradient
term; it is not a claim about a covariant ghost or about every critical
state. The arbitrary-state comparison is DISPERSION_GAP.md.

The negative energy needed for positive dust in the critical construction
is supplied by the closed-S3 curvature term. Removing that term leaves
a nonnegative critical operator, with no normal negative-sector state.
A flat critical LQC example cannot silently replace this mechanism.
