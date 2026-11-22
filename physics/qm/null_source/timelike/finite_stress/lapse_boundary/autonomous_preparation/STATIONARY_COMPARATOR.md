# AP — One stationary local action, correlated state, readout and stress

## AP.1 Exact scope and why this comparison is needed

This is a new **constant-coupling local two-field comparison** on unit
Einstein static spacetime (ESU), not the nonlinear AL candidate, the
global Z controller, or the earlier minimally coupled common geometry.
Frozen W/X already construct smooth local free-field probes, Hadamard
transport and normal instruments. We do not claim those general results
as new. The increment here is one explicit stationary correlated initial
kernel, full energy law, source-only sign encoding, same-H readout cost,
complete tensor noise and a direct static-Einstein rejection on that state.

Put \(V_0=2\pi^2\), \(r=1/5\), and retain the local action
\[
 S=-\frac12\int\sqrt{-g}\{(\nabla\phi)^2+(\nabla\psi)^2+
 R(\phi^2+\psi^2)/6+2r\phi\psi\}.
\]
The normal fields \(\Phi_\pm=(\phi\pm\psi)/\sqrt2\) have positive spatial
operators \(A_\pm=-\Delta_{S^3}+1\pm r\), frequencies
\(\omega_{k\pm}=\sqrt{k^2\pm r}\), degeneracy \(k^2\). The minus mass
parameter is negative, but \(A_-\ge4/5\) on this fixed background. No
variable background stability or gravitational completion follows.

The inherited Z fiber diagonalization, read as proof/data only, gives
\[
 H_r=W_r\,d\Gamma(\omega)\,W_r^\dagger+e(r),\quad
 \theta_{k\pm}=\tfrac14\log(1\pm r/k^2),
\]
\[
 e(r)=\sum_{k\ge1}k^3b(r/k^2),\quad
 b(z)=\tfrac12(\sqrt{1+z}+\sqrt{1-z}-2)+z^2/8.
\]
This uses the inherited ESU scalar energy convention \(c_r=0\).
It does **not** fix every finite locally covariant curvature counterterm,
absolute pressure, or arbitrary-metric lapse response.

## AP.2 Actual normal state and the correct energy domain

With \(a=1-r\),
\[
 \sum_{k,\pm}k^2\sinh^2\theta_{k\pm}
 \le {r^2\cosh^2(r/4a)\over8a^2}\zeta(2)<0.013.
\]
Thus \(W_r\) exists in the bare Fock representation and
\(\Omega_r=W_r\Omega_0\) is normal. Nevertheless its bare \(H_0\) mean
diverges logarithmically: the summand is asymptotic to \(r^2/(8k)\).
It belongs to every domain of the **actual** coupled \(H_r\), since it is
its ground vector. These two Hamiltonians have different form domains.

The positive ultrastatic ground covariances are Hadamard for the actual
coupled equation \(P_r\). This follows either by rotating to its two
positive spatial operators or the stationary vector-field microlocal
spectrum theorem. Polynomial Bogoliubov decay between \(P_0\) and \(P_r\)
is not a test of two Hadamard states of one fixed equation.

For actual constituent cutoffs, choose positive vacuum overlap phases:
\(W_{r,K}\to W_r\) strongly and \(e_K\to e\).
Consequently
\(H_{r,K}^j\Omega_{r,K}=e_K^j\Omega_{r,K}\to e^j\Omega_r\).
A displacement of the \(k=1\) source mode has a finite coherent
Poisson law independent of higher cutoffs, so the same convergence holds
as varying-operator graph recovery
\(H_{r,K}^j\Psi_K\to H_r^j\Psi\) for every fixed integer power and
the displaced vectors below. This is not fixed physical \(H_r\)-graph
convergence: finite-cutoff vectors retain a bare high-mode vacuum tail
and need not even belong to the full \(H_r\) form domain.
No preparation from a decoupled finite past is asserted here.

At each \(k\) the nonzero symmetric covariances are
\[
 Q_{ss}=Q_{pp}={\omega_+^{-1}+\omega_-^{-1}\over4},\
 Q_{sp}={\omega_+^{-1}-\omega_-^{-1}\over4},
\quad
 P_{ss}=P_{pp}={\omega_++\omega_-\over4},\
 P_{sp}={\omega_+-\omega_-\over4}.
\]
All symmetric \(QP\) entries vanish. The finite-mode wavefunction is
proportional to
\[
 \exp[-(\omega_++\omega_-)(q_s^2+q_p^2)/4
       -(\omega_+-\omega_-)q_sq_p/2].
\]
The initial mixed block comes from the same action and normal state;
it is not an independently assigned classical cross-noise.

## AP.3 One common history kernel and exact total energy law

Encode \(q_0=\pm1\) by \(D_s(q_0)=e^{-iq_0p_{s,1}}\) on \(\Omega_r\).
The probe marginal is initially identical for the two codes.
The initial joint state is correlated: this construction is **not**
an assignment channel for arbitrary bare source states tensored with
one fixed probe. It defines a valid instrument on the joint state and
a calibrated two-code classical input (or a retained encoding register).

Write \(a_+=\sqrt{1+r},a_-=\sqrt{1-r}\). The exact means are
\[
 q_s(t)={q_0\over2}(\cos a_+t+\cos a_-t),\quad
 q_p(t)={q_0\over2}(\cos a_+t-\cos a_-t),
\]
\[
 \langle p_p(t)\rangle=-q_0m(t),\quad
 m(t)=\tfrac12(a_+\sin a_+t-a_-\sin a_-t).
\]
The entire coupled energy has law
\[
 E=e+a_+N_++a_-N_-,\qquad
 N_\pm\ \hbox{independent Poisson}(q_0^2a_\pm/4).
\]
Hence \(\langle H_r\rangle=e+q_0^2/2\) and
\(\operatorname{Var}H_r=q_0^2(a_+^3+a_-^3)/4\). Both sign codes have
the **same full energy law**, not merely equal means.

For \(U(\tau,q)=e^{-i\tau H_r}D_s(q)\) and common \(\rho_r\),
the exact history overlap, with \(\Delta\tau=\tau-\tau'\), is
\[
 Z[(\tau,q),(\tau',q')]=e^{-ie\Delta\tau}
 \exp\!\sum_{\nu=\pm}{a_\nu\over4}
 [-\tfrac12(q^2+q'^2)+qq'e^{-ia_\nu\Delta\tau}].
\]
It is a normal-state Gram kernel; all its finite history matrices are
positive. The actual cutoff changes only \(e\) to \(e_K\), for \(K\ge1\).
This is same-H proper-time evolution and source encoding, not the CTP
functional for arbitrary spatial lapse histories.

## AP.4 Complete Gaussian record, same-H energy cost and domains

At \(T=1/2\), measure the physical probe \(P=p_{p,1}\) with Gaussian
Kraus density
\[
 M_z=(2\pi\sigma^2)^{-1/4}\exp[-(z-P)^2/(4\sigma^2)],
 \quad \sigma=1/10,\qquad \int M_z^\dagger M_z\,dz=I.
\]
Then retain every outcome, optionally scoring the binary record with
\(w(z)=(1+\sin z)/2\).
The Gaussian probability variance is \(v_P+\sigma^2\), where
\(v_P=(a_++a_-)/4\). The absolute two-code probability gap is
\[
 d=e^{-(v_P+\sigma^2)/2}\sin m(T)>0.071.
\]
This is a dimensionless model calibration, not an SI detector response.
The physical \(P\) mode and homogeneous encoding are spatially global;
locality of the field action does not make these operations local.

The nonselective instrument is a Gaussian random \(q_p\) translation
of variance \(v=1/(4\sigma^2)=25\).
Set
\[
 w_E=(a_+^3+a_-^3)/4,\quad
 z_T=\tfrac12(a_+^2\cos a_+T-a_-^2\cos a_-T).
\]
Using this same \(H_r\),
\[
 \Delta\langle H_r\rangle=v/2=12.5,\quad
 \langle H_r\rangle_{\rm out}=e+13,
\]
\[
 \operatorname{Var}_{\rm out}H_r
 =w_E+v(w_E+z_T^2)+v^2/2 .
\]
Here \(q_0^2=1\) and
\(\langle(q_p+rq_s)^2\rangle=w_E+z_T^2\).
The formula includes the coupling term. It is not the energy accounting
of the AD finite-LO reader and omits no success/failure outcome.

Only the two \(k=1\) oscillators are changed. Each conditional Gaussian
state, its nonselective mixture and binary coarse grain retain all
coupled energy moments and a smooth finite-mode two-point difference
from \(\Omega_r\); hence they remain Hadamard for \(P_r\).
This assertion is for these specified states, not all normal inputs.
A physical reader's own stress, an autonomous implementation and a
permanent record are still absent.

## AP.5 Complete tensor stress and a static-Einstein rejection

Use the complete improved classical tensor (plus one consistent quantum
local-covariant prescription)
\[
 T_{\mu\nu}=\sum_{A=s,p}\nabla_\mu\Phi_A\nabla_\nu\Phi_A
 -\tfrac12g_{\mu\nu}\{\sum_A(\nabla\Phi_A)^2+2r\phi\psi\}
 +\tfrac16[G_{\mu\nu}+(g_{\mu\nu}\Box-\nabla_\mu\nabla_\nu)]
                 (\phi^2+\psi^2).
\]
In ESU,
\(T_{00}=\tfrac12\sum_A(\pi_A^2+|\nabla\Phi_A|^2+\Phi_A^2)
-\Delta(\phi^2+\psi^2)/6+r\phi\psi\).
Its spatial integral is the coupled Hamiltonian, with the same scalar
energy prescription. Conformal curvature coupling does not remove the
dimension-two mixing potential. On shell its trace is
\(-2r\phi\psi\), plus quantum c-number anomaly/finite terms.
Centered trace noise is generally nonzero.

Code-minus-ground mean stress is unambiguous, because all state-independent
renormalization terms cancel. For the homogeneous means above,
\[
 \delta\rho={q_0^2\over2V_0},\quad
 \delta p={\dot q_s^2+\dot q_p^2+q_s^2+q_p^2\over6V_0}
                 -{rq_sq_p\over3V_0}
 ={ \delta\rho\over3}-{2rq_sq_p\over3V_0},\quad
 \delta T_{0i}=0.
\]
The trace difference is \(-2rq_sq_p/V_0\). In particular
\[
 \delta p(t)={q_0^2\over6V_0}
 -{rq_0^2\over12V_0}(\cos2a_+t-\cos2a_-t),\quad
 \delta p''(0)={2r^2q_0^2\over3V_0}>0.
\]
The vacuum stress, fixed curvature counterterms and static Einstein
left side are stationary. They cannot cancel this pressure history.
Thus these codes on the fixed ESU **fail the static full Einstein
equations**, although the matter Ward identity holds. This does not
exclude a different state, extra physical source or nonstatic geometry;
it cannot replace the previously accepted nonstatic minimal-coupling
average history.

Joint sign parity leaves the complete quadratic stress algebra invariant.
The two codes have identical stress statistics, while the odd probe
record distinguishes their signs. This is not a calibration of energy
or a geometric constraint charge.

## AP.6 Full tensor noise on its actual spacetime test domain

Let \(W_{AB}(x,y)=\langle\Omega_r,\Phi_A(x)\Phi_B(y)\Omega_r\rangle\)
be the positive-frequency covariance and \(h_A\) the coherent mean.
For the symmetric point-split polarization \(D_{\mu\nu}^{AB}\) of the
complete tensor above, the connected two-point function is
\[
 C_{\mu\nu\rho\sigma}
 =D_x^{AB}D_y^{CD}\{
 W_{AC}W_{BD}+W_{AD}W_{BC}
 +h_A(x)h_C(y)W_{BD}+h_A(x)h_D(y)W_{BC}
 +h_B(x)h_C(y)W_{AD}+h_B(x)h_D(y)W_{AC}\}.
\]
Coincidence at each tensor insertion is taken in the Wick-distribution
sense. Symmetric noise is \(N=\operatorname{Re}C\).
The cross terms use the same matrix \(W\). One must not square the
symmetrized Hadamard function, replace contractions by \(W\) minus a
parametrix, or inherit the old uncoupled trace-zero noise.

For real \(f^{\mu\nu}\in C_c^\infty(\mathbb R\times S^3)\), Weyl pullback
gives \(\delta T(f)\Psi=D_s(q_0)(Q_f\Omega_r+L_f\Omega_r)\).
The quadratic and linear terms create two and one particles, respectively,
so
\[
 N(f,f)=\|Q_f\Omega_r\|^2+\|L_f\Omega_r\|^2\ge0 .
\]
This is finite and is an actual constituent-cutoff limit. Indeed
\(|\nabla^jY_{ka}|\le C_jk^{j+1}\), \(j\le2\), and
\(\omega_{k\pm}\asymp k\). Repeated time integration by parts in a pair
coefficient gives
\[
 |c_{ka,lb}(f)|\le C_{f,N}\sqrt{kl}(k+l)^{2-N}.
\]
Including degeneracies, the squared sum is bounded by
\(C\sum_{n\ge2}n^{11-2N}\); choose \(N>6\), or \(N>p+6\) after a
\(H_r^p\) weight. The smooth coherent linear part is even simpler.
In diagonal Fock space the cutoff vectors are projections onto
constituents \(k,l\le K\), and \(W_K\to W\) transports them back.
Thus the centered tensor vectors converge in each fixed power of the
common diagonal energy graph before transport. After \(W_K\) transport
they converge strongly with varying-operator graph recovery
\(H_{r,K}^j v_K\to H_r^jv\), not in a fixed physical \(H_r\) graph.
For noninteger weights use the positive operator \(1+H_r-e\). This is a fixed-background centered-noise construction; subtracting
each cutoff ground expectation is not a full absolute-gravity
renormalization prescription.

Sharp time is different even in the coupled Hadamard ground.
Let \(P_{\rm int}=\int_{S^3}p\) and \(B=\int_{S^3}\phi\psi\).
The trace identity and ground energy give
\(\delta P_{\rm int}\Omega_r=-(2r/3)\delta B\Omega_r\), hence
\[
 \operatorname{Var}_{\Omega_r}P_{{\rm int},K}
 ={r^2\over18}\sum_{k\le K}k^2
 [1/(k^2+r)+1/(k^2-r)]
 ={r^2\over9}\sum_{k\le K}{k^4\over k^4-r^2}
 \ge {K\over225}.
\]
For time test \(g\), the first sum instead contains factors
\(|\widehat g(2\omega_{k\pm})|^2\) and converges.
Finite total energy moments and Hadamard regularity therefore do not
supply a sharp spatial-pressure second moment.

## AP.7 Acceptance and references

Accepted: one specified normal coupled-Hadamard state, actual all-mode
evolution and finite-time record, full energy law/cost, derived initial
mixed block, complete spacetime-smoothed tensor noise, and the precise
static-Einstein rejection. Open: finite-past correlated preparation in
this proof, arbitrary lapse CTP and its contacts, local autonomous reader,
total apparatus gravity and physical unification.

Primary background:
- Sahlmann–Verch, math-ph/0002021, Theorem 5.1 (stationary ground
  microlocal spectrum), https://arxiv.org/abs/math-ph/0002021 .
- Sahlmann–Verch, math-ph/0008029, Theorem 5.8 (vector Hadamard criterion),
  https://arxiv.org/abs/math-ph/0008029 .
- Hollands–Wald, gr-qc/0103074, Section 2 (Wick algebra and test domains),
  https://arxiv.org/abs/gr-qc/0103074 .
- Moretti, gr-qc/0109048, Section 2.1 and Theorem 2.1 (complete stress
  with smooth potential and Ward identity),
  https://arxiv.org/abs/gr-qc/0109048 .

The certificate verifies the displayed algebra and outward numerical
bounds. It is not a formal proof of these cited theorems or an experiment.
