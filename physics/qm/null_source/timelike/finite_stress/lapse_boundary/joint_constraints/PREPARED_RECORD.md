# JC11 — The same prepared state through coding, causal transfer and reading

## 1. One preparation and an unambiguous time coordinate

Use the actual eight-control state in the certified ball of
QUANTIFIED_PREPARATION.md. The pulse is supported in \([-1/5,1/5]\).
At the absolute slice \(t_{\rm enc}=\pi\), apply either source momentum
code
\[
 D_\pm=\exp[\pm i\eta\phi_s(f)],\qquad 0<\eta\leq10^{-11},
\]
using the unique common control for the target
\((-\eta^2\mathbf d,\mathbf0)\).
The eight projected **mean** conditions hold on this encoding slice.

For all later statements define elapsed time
\(\tau=t-t_{\rm enc}\). Use exactly the inherited disjoint caps:
radius \(1/2\), center separation \(3/2\), and nonnegative smooth
bump profiles \(f,g=b_{1/2}/\sqrt{V_{1/2}}\) with norms at most one.
After preparation the Hamiltonian is the same fixed \(H_r\), \(r=1/5\).

The causal Cauchy propagator depends on this final operator, not on
which Gaussian input was prepared. Therefore the inherited exact kernel
and cap estimates apply with the code amplitude multiplied by \(\eta\):
there is no receiver-cap signal for \(0<\tau<1/2\), and a positive
record mean on \(5/2<\tau<\pi\).
Choose \(\tau_{\rm read}=3\), hence **absolute read time \(t=\pi+3\)**.
It would be incorrect to compare this absolute time with the
first-wrap bound on the elapsed variable.

The exact state-independent receiver mean bound is
\[
 |\langle Q_p(g)\rangle_\pm|=\eta\mu,\qquad
 \mu\geq\mu_{\rm lo}
 =\frac{r e^{-2/3}V_{1/4}^2}{8\pi V_{1/2}}>0,\quad
 V_\epsilon=2\pi(\epsilon-\tfrac12\sin2\epsilon).
\]
The frozen local_record.json supplies the independently checked
interval \(\mu_{\rm lo}\simeq3.42735067487022\times10^{-5}\).
This entry recomputes the closed formula, but does not execute that
predecessor module or borrow the AQ state covariance.

## 2. A fresh covariance and energy budget for this actual state

In the coupled \(D_\pm\)-scaled canonical coordinates the initial
ground covariance is \(I/2\). During the pulse
\[
 x_0=\int\|V_u(t)\|dt
 \leq\nu\sqrt{B_0^2+B_1^2}|u|<30\times10^{-16}.
\]
The symplectic norm is at most \(e^{x_0}\). Subsequent free evolution
is orthogonal in these scaled coordinates. Hence at every final
waiting time
\[
 \nu_Q=\operatorname{Var}Q_p(g)
 \leq\frac{e^{2x_0}}4
 \langle g,(D_+^{-1}+D_-^{-1})g\rangle
 \leq\frac{e^{2x_0}}4(1/\sqrt{1.2}+1/\sqrt{0.8})<9/16 .            \tag{1}
\]
Similarly \(D_++D_-\leq2D_0\), \(D_0=\sqrt{-\Delta+1}\), gives
\[
 \operatorname{Var}\Pi_{s,p}(h)
 \leq\tfrac12e^{2x_0}\langle h,D_0h\rangle
 <\tfrac{11}{20}\langle h,D_0h\rangle<P_*,
\quad
 P_*=\tfrac{11}{20}\sqrt{1+(22/5)^2}.
\]
This uses the same smooth cap gradient bound but the new preparation.

There is an explicit uniform preparation budget. Put
\(x=1.6\times10^{-10}\), \(Q_*=2e^x(x+3x^2+x^3)\).
The actual endpoint bound is \(\|D_+\beta\|_{\rm HS}\leq Q_*\).
For the pure Gaussian state let
\(\gamma=\beta\beta^\dagger,\ \kappa=\alpha\beta^T\).
At each finite cutoff Wick's identity and
\(\kappa\kappa^\dagger=\gamma(1+\gamma)\) imply
\[
 \operatorname{Var}H_r=
 {\rm Tr}D^2\gamma+{\rm Tr}(D\gamma D\gamma)
                         +{\rm Tr}(D\kappa D\kappa^\dagger)
 \leq2(1+\|\gamma\|){\rm Tr}D^2\gamma .
\]
The elementwise inequality \(2d_id_j\leq d_i^2+d_j^2\), and
\(\kappa^T=\kappa\), justify the two trace bounds.
Taking the actual weighted-HS limit, with \(D_+>1\), gives
\[
 0\leq E_{\rm p}\leq Q_*^2,\qquad
 0\leq V_{\rm p}\leq2(1+Q_*^2)Q_*^2.                              \tag{2}
\]
They are approximately bounded by \(1.025\times10^{-19}\) and
\(2.05\times10^{-19}\), respectively. These coarse bounds cover
the whole declared control ball.

## 3. Complete instrument and a certified positive sign record

At elapsed time three use the complete Gaussian instrument
\[
 M_z(Q)=(2\pi\sigma^2)^{-1/4}
        e^{-(z-Q)^2/(4\sigma^2)},\quad \sigma=1/10,\quad
 \int_{\mathbb R}M_z^\dagger M_z\,dz=I .
\]
Retain all outcomes and coarse grain to \(z\geq0\) or \(z<0\).
The raw distribution is exactly Gaussian, with means \(\pm\eta\mu\)
and the same variance \(\nu_Q+\sigma^2\).
Consequently its complete binary contrast is
\[
 d_\eta=\operatorname{erf}\!
 \left(\frac{\eta\mu}{\sqrt{2(\nu_Q+\sigma^2)}}\right)
 \geq \eta\,c_{\rm rec},\qquad
 c_{\rm rec}=\frac{2x_{\rm lo}}{\sqrt\pi}e^{-x_{\rm lo}^2},
 \quad x_{\rm lo}=\mu_{\rm lo}\sqrt{200/229}.                       \tag{3}
\]
The last inequality uses \(0<\eta\leq1\).
At the certified endpoint strength \(\eta=10^{-11}\),
\[
 \boxed{d_\eta>3.61418\times10^{-16}.}                             \tag{4}
\]
This is a strictly positive mathematical lower bound, not a practical
experimental signal-to-noise certification.

The actual all-outcome cutoff instrument converges on this state.
Indeed for \(Q_K=Q(P_Kg)\), the commuting Gaussian identity
\[
 \int M_z(Q_K)M_z(Q)\,dz=e^{-(Q_K-Q)^2/(8\sigma^2)}
\]
proves strong convergence of the Stinespring isometries.
Combine it with the actual prepared density, smooth Weyl code and
free propagator limits. Conditional, nonselective and binary outputs
remain normal and Hadamard: their two-point changes are finite-rank
smooth solutions or Gaussian mixtures thereof. Smooth Weyl vectors
and Gaussian outcome moments preserve all final coupled-energy
moments in the established common-diagonal/varying-\(H_K\) sense.

The field's bounded spectral functions belong to the receiver
time-slice local algebra, so the nonselective dual instrument acts as
identity on its spacelike commutant. This abstract local operation
does not construct an autonomous distributed pointer or finish
collection of a cap-wide result into one classical device.

## 4. Reading changes the complete retained source

Let \(c_f=\|f\|^2,\ c_g=\|g\|^2\). Parity of the common preparation gives
\[
 \Delta E_{\rm code}=\eta^2c_f/2,\quad
 \Delta{\rm Var}H_{\rm code}
       =\eta^2\operatorname{Var}_{\rm p}\Pi_s(f).
\]
The subsequent coherent solution has positive conserved energy at
most \(\eta^2/2\), so
\(|\langle\Pi_p(g)\rangle|^2\leq\eta^2\).

The nonselective reader is a random probe momentum kick of variance
\(v=1/(4\sigma^2)=25\). Its exact full retained-Hamiltonian increments
are
\[
 \Delta E_{\rm read}=25c_g/2,\qquad
 \Delta{\rm Var}H_{\rm read}
 =25\langle\Pi_p(g)^2\rangle+625c_g^2/2 .
\]
Thus
\[
 E_{\rm out}\leq e+E_{\rm p}+\eta^2/2+12.5,
\quad
 {\rm Var}H_{\rm out}
 \leq V_{\rm p}+(25+\eta^2)P_*+25\eta^2+625/2 .                   \tag{5}
\]
Moreover, using the half cap,
\[
 \Delta E_{\rm read}\geq
 \frac{25}2 e^{-2/3}V_{1/4}/V_{1/2}>0 .                          \tag{6}
\]
This lower bound is about \(0.83\) in model units and does not
decrease with \(\eta\) at the fixed reader resolution.

At the reading slice the nonselective retained stress jump is
\[
 \delta\rho_{\rm read}=25g^2/2,\quad
 \delta T_{ij,\rm read}=25g^2\gamma_{ij}/6,\quad
 \delta T_{0i,\rm read}=0 .
\]
The source-species marginal is unchanged instantaneously by this
probe-only instrument; the complete source-plus-probe gravitational
source is changed. Both facts must be kept.

For real smooth post-read spacetime tensor tests, write the exact
quadratic kick identity
\(T_F\mapsto T_F+\xi B_F+\xi^2C_F\).
Its complete noise increment is
\[
 \Delta N(F,G)=25\,\operatorname{Re}\langle B_FB_G\rangle
                       +2(25)^2C_FC_G ,
\]
a positive semidefinite bilinear form on the declared domain.
No divergent sharp composite variances are subtracted.

## 5. What this closes

One and the same new normal preparation supports the eight initial
projected means, both sign codes, causal transfer, a complete
mathematical instrument, and explicit retained energy/noise accounting.
The sign record is not a measurement of a geometry constraint charge.
The eight mean conditions were imposed only at \(t=\pi\); their
preservation during later evolution has not been proved, and the
readout adds a new inhomogeneous stress. The full geometric constraints
must therefore be solved again throughout the history.
The actuator, encoder, pointer, causal classical collection and
their total gravitational source remain open.
