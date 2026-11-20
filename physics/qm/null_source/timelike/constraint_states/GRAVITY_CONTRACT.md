# From a clock code to a declared homogeneous quantum-gravity model

This is a separate leading-GR dust model with two truly homogeneous free
zero modes. It is not the original all-mode AE/QFT model or its NOON
preparation. The construction closes the operator/physical-inner-product
definition of a reduced candidate, while retaining its new ordering and
boundary assumptions. None is claimed to follow from Core.

## 1. Action and positive clock source

For G_mu_nu=2T_mu_nu, the Einstein-Hilbert coefficient is 1/4.
With V0=2*pi^2 and ds2=-N2dt2+a2dOmega3^2, integration by parts gives
\[
 L_g=-{3V_0a\dot a^2\over2N}+{3V_0Na\over2}-V_0NU_0a^3,
 \qquad p_a=-3V_0a\dot a/N ,
\]
\[
 H_g=-{p_a^2\over6V_0a}-{3V_0a\over2}+V_0U_0a^3.
\]
Here U0 remains an explicit physical input. For harmonics normalized to
unit spatial L2 norm, the projected finite-mode matter expression is
\[
 H_m=\sum_j[P_j^2/(2a^3)+\lambda_j a Q_j^2/2],
 \qquad\lambda_j=k_j^2-1 .
\]
Inhomogeneous modes generally source omitted inhomogeneous geometry.
This projected expression is not a proof of a consistent full local
Einstein truncation. The zero-mode-only submodel below is a genuinely
homogeneous classical truncation.

The covariant irrotational dust action is
\[
 S_d=-\tfrac12\int\sqrt{-g}\,\rho_d[(\nabla T)^2+1],
 \qquad\rho_d\ge0.
\]
On the future branch dot(T)=N,
\[
 P_T=V_0a^3\rho_d\ge0,\qquad
                 C_{\rm GR}=P_T+H_g+H_m=0 .
\]
Thus the dust density is P_T/(V0 a^3); it is never removed from the
constraint. Quantization must select the nonpositive spectral sector of
H_g+H_m to maintain positive dust. The action and deparametrization
framework are standard (Brown–Kuchar, gr-qc/9409001; Husain–Pawlowski,
arXiv:1108.1147). The closed-curvature and G=2T coefficients above are
derived directly here.

## 2. An explicit two-zero-mode self-adjoint completion

Set x=a^(3/2), p_a=(3/2)a^(1/2)p_x and choose the NEW ordering/measure
\[
 {\cal H}_{\rm red}=L^2(\mathbb R_+,dx)\otimes L^2(\mathbb R^2,d^2P).
\]
This is not an inherited Laplace-Beltrami prescription. With no nonzero
field modes, the fiber differential expression is
\[
 H_P=c\,d^2/dx^2+V_0U_0x^2-\tfrac32V_0x^{2/3}
                      +|P|^2/(2x^2),\qquad c=3/(8V_0).
\]
Start on compactly supported smooth functions. This Hamiltonian is not
semibounded; a Friedrichs extension does not select its domain.

For U0>0, at infinity the zero-spectral-parameter equation is
psi''+q_P(x)psi=0, with q_P(x)~Kx^2>0. Its Liouville correction obeys
\[
 \int^\infty {|5q_P'^2-4q_Pq_P''|\over q_P^{5/2}}dx<\infty
\]
(the integrand is O(x^-3)). The Volterra construction after the Liouville
transform gives a solution q_P^-1/4 exp(i integral sqrt(q_P))[1+o(1)].
Its squared modulus behaves as const/x and is not integrable. Weyl's
alternative therefore makes infinity limit-point.

At zero let g_P=4V0|P|^2/3, d_P=1/4-g_P and fix a new scale ell>0.
For z=log(x/ell) define C_d(z)=cosh(sqrt(d)z) for d>=0 and
cos(sqrt(-d)z) for d<0. Define S_d(z)=sinh(sqrt(d)z)/sqrt(d) for d>0,
z for d=0, and sin(sqrt(-d)z)/sqrt(-d) for d<0. Put
\[
       u_P=\sqrt{x}C_{d_P}(z),\qquad
       v_P=\sqrt{x}S_{d_P}(z),\qquad W_x(u_P,v_P)=1 .
\]
These leading inverse-square solutions depend continuously on the
parameter at d=0. Since g_P>=0, both are square integrable near zero.
The remaining potential is O(x^(2/3)), so zero is limit-circle.

For the maximal domain, use the boundary coordinates
\[
 \alpha_P(\psi)=\lim_{x\downarrow0}W(\psi,v_P),\qquad
 \beta_P(\psi)=\lim_{x\downarrow0}W(u_P,\psi).
\]
One can multiply u,v by a near-zero cutoff. Their operator images are
locally square integrable, so Green's identity establishes these limits.
Choose ONE fixed theta in [0,pi) for all P:
\[
       \cos\theta\,\alpha_P+\sin\theta\,\beta_P=0 .
\]
The boundary form is proportional to
conj(alpha_psi) beta_phi-conj(beta_psi) alpha_phi; this one-dimensional
real condition is maximal isotropic. Together with the limit-point
infinite endpoint it defines a self-adjoint H_{P,theta}.

The family is measurable: regular-interval resolvents with the displayed
left Robin data and right Dirichlet data are measurable in P. Sending the
left endpoint to zero and right endpoint to infinity gives the specified
boundary-condition resolvent, whose strong limit remains measurable.
Therefore
\[
                 H_\theta=\int^\oplus H_{P,\theta}\,d^2P
\]
is self-adjoint. This uses standard Sturm–Liouville and measurable
self-adjoint-extension results; references include Teschl, Chapter 9,
Gitman–Tyutin–Voronov arXiv:0903.5277, and Gitman et al. arXiv:1012.2588.
The inverse-square boundary mechanism is also described by
Derezinski–Richard arXiv:1604.03340. These references do not choose a
unique physical theta or ell for this model.

## 3. Nonempty positive-dust histories and bounded readout effects

High-frequency test functions supported away from zero have expectation
-cn^2+O(1). Thus H_theta is unbounded below and
\[
 {\cal H}_{\rm phys}^{d}=1_{(-\infty,0]}(H_\theta){\cal H}_{\rm red}
\]
is nonempty. Its restricted H_phys is self-adjoint, and the physical dust
energy is P_T=-H_phys>=0. The physical-inner-product histories are
Psi(T)=exp(-iH_phys T)psi. This is a well-defined constrained unitary history in the stated reduced
model. It does not yet certify finite positive matter stress.

Scale-factor interval readouts are safely represented by the effects
\[
 E_a(B)=\Pi_-1_B(x^{2/3})\Pi_- .
\]
They need not be projections after compression. No unproved self-adjoint
compressed radius is assumed.

For any chosen R>0 there is some nonzero finite negative spectral band
[-E2,-E1], with E2>E1>2R, because the spectrum is unbounded below. A normal
state supported there has finite energy moments. With an even normalized smooth
packet h supported in [-2R,2R], the map
\[
 (V_d\psi)(p)=h(p+H_\theta)\psi,\quad p>0
\]
is an isometry on that band. Its clock support is [E1-2R,E2+2R],
\[
       \langle P_T+H_\theta\rangle=0,\qquad
       \langle(P_T+H_\theta)^2\rangle=\sigma_k^2 ,
\]
and its conditional dust-time evolution is exactly exp(-iH_theta T).
This is a finite normal approximation to the exact physical history,
not an exact normal kinematic constraint state.

## 4. What has and has not been closed

The action, canonical normalization, endpoint domain, measurable direct
integral, positive-dust physical sector and unitary conditional evolution
are specified. The symbolic checker certifies the Legendre transform,
Friedmann normalization, x transformation, indicial roots, Wronskians
and the finite clock support identities. The analytical endpoint and
direct-integral arguments above are reviewed mathematics, not a computer
formalization or a numerical ODE test.

New inputs remain: the dust field, canonical quantization, the flat x
measure/order, theta, ell, and a physical initial state in the selected
spectral sector. The original k=2 NOON shell is absent. Nonzero modes,
inhomogeneous constraints and the full AE limit have not been recovered.

The subsequent [finite-stress check](DUST_REGULARITY.md) rejects this
candidate as a carrier of the original momentum law. In the positive-dust
sector, a normal state with finite total H second moment and finite
positive K0=|P|^2/(2x^2) throughout an open time interval must be supported
in |P|^2<3/(16V0). The original source has less than 2.85e-12 probability
there. This also excludes its momentum-preserving stress-equivalent
family in this model. The signed total operator can be finite despite a
divergent positive matter form; self-adjointness does not close that gate.

The operator construction above remains valid. It is not an accepted
finite-stress physical carrier for the actual source. The original
A/P/K0 and the positive-clock conditional error bound cannot be transferred
to it. A physically justified new domain/constraint must pass the positive
matter-form time-window test before it can be extended to the full source.
