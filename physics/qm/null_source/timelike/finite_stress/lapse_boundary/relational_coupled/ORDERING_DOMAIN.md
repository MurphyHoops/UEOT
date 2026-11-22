# Ordering family: endpoint domain, uncertainty and complete evolution

## O1. A declared family, not a unique quantization

On the same flat slice measure and positive branch, replace the principal reference by
\[
 A_\eta=\kappa^{-1/2}P_\kappa^2\kappa^{-1/2}+\eta\kappa^{-3},
 \qquad \eta\ge-1/4.
\]
The added term is an ordering choice of order \(\hbar^2\). The classical action does
not select its value. The original congruence is \(\eta=0\); the flat Weyl
principal choice is \(\eta=1/4\). Each value below has its own specified
Friedrichs domain; different values are not asserted to share an operator domain.

With \(x=2\kappa^{3/2}/3\) and the same unitary Liouville transform,
\[
 A_\eta=-\partial_x^2+\frac{-5+16\eta}{36x^2}
       =-\partial_x^2+\frac{\nu^2-1/4}{x^2},\quad
 \nu=\frac{\sqrt{1+4\eta}}3.
\]
The two powers at zero are \(\kappa^{1\pm\sqrt{1+4\eta}/2}\).
For \(-1/4<\eta<2\) the endpoint is limit circle and the plus power specifies
Friedrichs. At \(\eta=-1/4\), the alternatives are \(\kappa\) and
\(\kappa\log\kappa\); the closed ground-state form selects the no-log branch.
For \(\eta\ge2\), the endpoint is limit point. These standard inverse-square
facts are applied with the explicitly computed coefficient; see REFERENCES.

Put \(\alpha=1+\sqrt{1+4\eta}/2\ge1\). On the compact core write
\(\psi(\kappa)=\kappa^\alpha f(\kappa)\), with values in the source Hilbert
space (and an arbitrary purification space when needed). Integration by parts gives
\[
 q_\eta[\psi]=\int_0^\infty \kappa^{2\alpha-1}\|f'(\kappa)\|^2d\kappa.       \tag{O1}
\]
Its closure defines the positive principal form. At the critical value one
must use this closed expression; the two separated inverse-square terms
can diverge and its domain is not simply \(H_0^1(dx)\).

## O2. Source-independent geometric resource bound

For a normalized vector, let \(m=\langle\kappa\rangle<\infty\) and
\(I=\langle\kappa^{-1}\rangle\). A second integration by parts gives
\[
 \alpha I=-\Re\int\kappa^{2\alpha}\langle f,f'\rangle\,d\kappa,
 \qquad
 \boxed{q_\eta\ \ge\ \frac{\alpha^2 I^2}{m}
                      \ \ge\ \frac{\alpha^2}{m^3}}.                    \tag{O2}
\]
The first step is weighted Cauchy--Schwarz, the second is Jensen.
No factorization of source and geometry is used. Connection transport by
\(W_K\) commutes with \(\kappa\), so the same bound holds for its covariant
principal form and for normal mixed states through purification.

The extension from the core does not assume \(I\) finite in advance.
First impose an upper \(\kappa\) cutoff: its derivative error in O1 is
\(O(R^{-3})\|\psi\|^2\), and it converges in form norm. For fixed upper
cutoff, approximate in the Friedrichs core and use lower semicontinuity.
Fatou and then \(R\to\infty\) prove O2 and finiteness of I whenever q and m
are finite. This argument includes the critical closed form.
Cauchy--Schwarz in the first bound is sharp for \(f=e^{-\lambda\kappa^2/2}\);
the final bound expressed only in m is not claimed optimal.

For \(\eta<-1/4\), the principal core form is unbounded below.
Indeed \(\phi=x^{1/2}F(\log x)\) gives
\[
 q_\eta=\int (|F'|^2+(1+4\eta)|F|^2/9)\,dy.
\]
A sufficiently wide F gives a negative value. Normalized dilations towards
zero scale this value as \(-L^2\), whereas a fixed finite-energy source and
the scalar \(x^{-2/3}\) terms grow only as \(L^{2/3}\). Thus this semibounded
Friedrichs route fails. This is not exclusion of every self-adjoint extension.

## O3. Full dynamics for every member of this family

In the positive confining coefficient window of COEFFICIENT_WINDOW, replace
q_F in COUPLED_FORMS by the closed q_eta and take
\[
 {\cal Q}_\eta=D(q_\eta)\cap D(\kappa^{3/2})
                 \cap D(\kappa^{-1/2}H_0^{1/2}).
\]
The scalar inverse-power term is infinitesimally bounded relative to
\(q_\eta+\langle\kappa^3\rangle\). To see this without a noncritical Hardy
assumption, O2 gives \(I\le\sqrt{mq_\eta}/\alpha\le
\epsilon q_\eta+m/(4\epsilon)\); then absorb m using
\(\kappa\le\delta\kappa^3+C_\delta\).
The squeezed source energy has uniformly equivalent forms on each compact
clock interval. Coefficients and their first two derivatives are bounded.
Thus the common-form C2 construction and the auxiliary frozen-time Stone
construction apply for each fixed eta, including its critical value.
The actual original-frame strong operator-domain transport remains unproved.
LENS_EVOLUTION extends this result to every compact window with g_K>0.

O2 is the useful resource statement for mean recovery. It does not claim an
experimental energy bound, a choice of nature's ordering, or a full-field limit.
Restoring units places \(\hbar^2\) in front of the geometric kinetic resource.
