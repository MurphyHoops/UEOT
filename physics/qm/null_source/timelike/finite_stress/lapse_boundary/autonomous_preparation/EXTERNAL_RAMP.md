# AQ — Actual finite-past local preparation with an explicit external work source

## AQ.1 Scope: a completed preparation in the AP linear model

AP's correlated coupled ground was specified at a finite slice. Here a
real finite-past evolution produces a normal state close to it, with an
explicit all-mode error and work budget. The linear two-field action is
retained but \(r\) is now a prescribed external smooth scalar source.
No old mode ODE or scientific module is executed. This is not an
autonomous quantum controller, the AL nonlinear action, or a common
Einstein geometry. General free-field Hadamard propagation and smooth
probe existence were already used in frozen W/X; the new deliverable is
this particular monotone preparation, quantitative error, retained
renormalized work and actual same-state sign record.

Define the flat compact bump and monotone ramp
\[
 b(s)=\begin{cases}e^{4-1/[s(1-s)]}&0<s<1\\0&\text{otherwise},\end{cases}
 \quad I=\int_0^1b(s)\,ds,\quad
 F(s)=I^{-1}\int_{-\infty}^s b(u)\,du,\quad
 r_\tau(t)=\tfrac15F(t/\tau).
\]
Use \(\tau=100\) as one concrete instance, in model units.
On \([7/20,13/20]\), \(b\ge e^{-36/91}\), whence
\(I\ge(3/10)e^{-36/91}>1/5\). Consequently
\[
 \|F'\|_\infty<5,\quad \|F''\|_1<10,\quad
 \|F'\|_2^2<5.
\]
The second identity uses the single maximum of \(b\); the third uses
\(\int F'=1\). Thus
\[
 \|\dot r\|_\infty<1/\tau,\quad
 \|\ddot r\|_1<2/\tau,\quad
 \|\dot r\|_2^2<1/(5\tau),\quad\int|\dot r|=1/5.
\]
The source is zero in the whole past \(t\le0\), and exactly \(1/5\)
after \(t=\tau\). Start with the same normal decoupled vacuum \(\Omega_0\).

## AQ.2 Exact Bogoliubov bounds, not a first-Dyson truncation

The \(\sigma=\pm\) real normal modes obey
\[
 \ddot q_{k\sigma}+(k^2+\sigma r_\tau(t))q_{k\sigma}=0,\quad
 \omega_{k\sigma}\ge\sqrt{\kappa}\,k,\quad\kappa=4/5 .
\]
Their exact instantaneous coefficients have
\[
 \dot\alpha=g e^{2i\varphi}\beta,\quad
 \dot\beta=g e^{-2i\varphi}\alpha,\quad
 g={\sigma\dot r\over4\omega^2},\quad
 \dot\varphi=\omega,\quad(\alpha,\beta)(0)=(1,0).
\]
Set \(L_k=\int|g|\le1/(16k^2)\). The exact inequalities
\(|\alpha|\le\cosh L_k,\ |\beta|\le\sinh L_k\) follow by integration,
not by dropping feedback in the two equations.

One integration by parts in \(\int g\alpha e^{-2i\varphi}\) gives
\[
 |\beta(t)|\le {|\dot r(t)|\cosh L_k\over8\kappa^{3/2}k^3}
 +{\cosh L_k\|\ddot r\|_{1,[0,t]}\over8\kappa^{3/2}k^3}
 +\left({3\cosh L_k\over16}+{\sinh L_k\over32}\right)
 {\|\dot r\|_{2,[0,t]}^2\over\kappa^{5/2}k^5}.
\]
The initial boundary term vanishes. At the completed flat endpoint the
current boundary term also vanishes. Put
\(C=\cosh(1/16)\), \(S=\sinh(1/16)\). Then
\[
 |\beta_{k\sigma}(\tau)|
 \le {c_f\over\tau k^3}<{0.43\over\tau k^3},\quad
 c_f={C\over4\kappa^{3/2}}+{3C\over80\kappa^{5/2}}
                         +{S\over160\kappa^{5/2}},
\]
\[
 \sup_{0\le t\le\tau}|\beta_{k\sigma}(t)|
 \le {c_m\over\tau k^3}<{0.60\over\tau k^3},\quad
 c_m={3C\over8\kappa^{3/2}}+{3C\over80\kappa^{5/2}}
                           +{S\over160\kappa^{5/2}}.
\]
For example, the rational bounds
\(C<501/500,S<63/1000,\kappa^{3/2}>71/100,
\kappa^{5/2}>57/100\) give
\(c_m<1286055/2158400<3/5\).
The certificate checks both complete constants outwardly.

## AQ.3 Actual cutoff unitaries, including their phase

At finite constituent cutoff retain the AP scalar convention:
\[
 H_K(t)=H_{0,K}+r(t)B_K+C_K(r(t)),\quad
 B_K=\int\phi_K\psi_K,\quad
 C_K(r)={r^2\over8}\sum_{k\le K}{1\over k}.
\]
These are finite-mode self-adjoint quadratic Hamiltonians, extended by
free evolution on the omitted modes. Their exact time-dependent
propagators are not replaced by instantaneous ground states.

Transform with the actual squeeze \(W_K(r(t))\). The adapted generator
is diagonal \(d\Gamma(\omega_K)+e_K(r)\) plus its quadratic connection
\(-iW_K^\dagger\dot W_K\). Up to the immaterial sign convention the
connection in each normal oscillator is
\(i\dot\theta(a^{\dagger2}-a^2)/2\).
For a tail vacuum,
\[
 \|A_{>K}(t)\Omega\|^2
 ={1\over2}\sum_{\sigma,k>K}k^2\dot\theta_{k\sigma}^2
 \le {|\dot r(t)|^2\over16\kappa^2K},\quad
 \int\|A_{>K}\Omega\|dt\le {1\over16\sqrt K}.
\]
Independent modes factorize exactly. Duhamel on a finite-low-mode vector
tensored with a vacuum tail bounds the adapted cutoff difference by
this quantity plus the scalar phase tail; the omitted diagonal energy
annihilates the vacuum. Such vectors are dense. The reverse evolution
has the same tail estimate, so both propagators and their adjoints
converge strongly to an actual unitary \(U_\tau\).

The phase is retained: \(e_K(r)\to e(r)\) uniformly on \(0\le r\le1/5\),
with AP's \(O(K^{-4})\) tail. Hence
\(\exp[-i\int e_K(r(t))dt]\to\exp[-i\int e(r(t))dt]\).
The actual endpoint squeezes \(W_K\to W\) also converge strongly.
This proves a normal same-state full-field preparation with its cutoff
phase, not merely an implementable symplectic map up to an arbitrary phase.

Every admissible finite collection of such smooth source histories,
with common initial \(\Omega_0\), consequently has a positive limiting
Gram kernel \(\langle U_{r'}\Omega_0,U_r\Omega_0\rangle\).
This fixed-metric history statement does not supply arbitrary-lapse
functional derivatives or an Einstein-CTP solution.

## AQ.4 Hadamard and energy domains: three distinctions

The actual two-point function is a bisolution of the smooth matrix
wave operator with potential \(r_\tau(t)\sigma_x\). It is the ordinary
Hadamard vacuum in the whole past. The vector-wave propagation theorem
(Sahlmann–Verch, math-ph/0008029, Theorem 5.5) makes it Hadamard for
this **time-dependent** equation everywhere.

At \(t\ge\tau\) the equation is exactly \(P_r\). Its two-point difference
from the AP ground is smooth. On compact \(S^3\), the corresponding
Cauchy spectral coefficients are rapidly decreasing; using both field
and momentum Cauchy covariances isolates the occupations
\(n_{k\sigma}=|\beta_{k\sigma}|^2\) and anomalous covariances.
The combination \(\omega\,\delta Q+\omega^{-1}\delta P=2n\)
cancels the anomalous covariance. For an independent squeezed oscillator,
its energy cumulants are bounded by a constant times \(\omega^j n\)
when \(n\) is bounded. The rapidly decreasing final occupations therefore
give all final coupled-energy moments. The final state also lies in the
spacetime-smoothed Wick-stress domain.

At intermediate times, the explicit \(k^{-3}\) bound by itself supplies
finite first and second moments of the instantaneous coupled energy.
It is not a proof of every higher instantaneous-energy graph domain.
Hadamard for the true varying equation is not comparison with a
different equation obtained by freezing \(r\) at that time.

In fact, at any fixed active time \(0<t<\tau\), a second integration by
parts with bounded smooth ramp derivatives gives
\[
 |\beta_{k\sigma}(t)|={\dot r(t)\over8k^3}
                       +O_{\tau,t}(k^{-4}),\qquad
 n_{k\sigma}\sim{\dot r(t)^2\over64k^6}>0.
\]
The leading term is the current endpoint of AQ.2; the initial endpoint
is flat, and \(\alpha=1+O(k^{-4})\).
The third instantaneous excitation-energy moment diverges logarithmically.
A direct positivity proof uses the squeezed product's nonzero vacuum
probability \(F_{\rm vac}=\prod_j(1+n_j)^{-1/2}>0\). The probability of
one pair in mode \(j\), all others empty, is
\(F_{\rm vac}n_j/[2(1+n_j)]\). Hence the third moment is at least
\(4F_{\rm vac}\sum_j\omega_j^3 n_j/(1+n_j)=\infty\).
Thus the state is in \(D(H_t)\), but not in
\(D((1+H_t-e_t)^{3/2})\), at an active time. This sharp threshold concerns
the frozen instantaneous energy; it does not contradict Hadamard
regularity for the true time-dependent equation.


Finally these are coupled-energy domains. When \(r(t)>0\), the bare
\(H_0\) form generally diverges because the static squeeze has a
\(k^{-2}\) leading coefficient. Moreover finite-cutoff physical vectors
have a bare vacuum tail and need not belong to the fixed full \(H_r\)
form domain. The precise actual convergence assertion is
\[
 \Psi_K\to\Psi,\qquad H_{r(t),K}\Psi_K\to H_{r(t)}\Psi,
\]
and, at completed endpoints, the analogous recovery for each fixed
integer power. It is **varying-operator graph recovery**. Fixed graph
convergence holds after putting the cutoff vectors in the common
diagonal representation; it is not asserted for the physical
bare-tail cutoff vectors under one fixed \(H_r\).

## AQ.5 Quantitative final state and energy errors

Let \(c=43/100,\ d=c^2/\tau^2\). In the final ground frame,
independent real squeezed oscillators give the exact formulas
\[
 N_{\rm exc}=\sum_{k,\sigma}k^2 n_{k\sigma},\quad
 E_{\rm exc}=\sum_{k,\sigma}k^2\omega_{k\sigma}n_{k\sigma},\quad
 V_E=2\sum_{k,\sigma}k^2\omega_{k\sigma}^2n_{k\sigma}(1+n_{k\sigma}).
\]
The coefficient bounds imply
\[
 N_{\rm exc}<2d\zeta(4),\quad
 E_{\rm exc}<2\sqrt{6/5}\,d\zeta(3)<{0.51\over\tau^2},
\]
\[
 V_E<4(6/5)d[\zeta(2)+d\zeta(8)].
\]
The pure-state half trace distance from the coupled ground satisfies
\[
 D_{\rm tr}^2=1-\prod_{k,\sigma}(1+n_{k\sigma})^{-k^2/2}
 \le \tfrac12N_{\rm exc},\quad
 D_{\rm tr}<{0.448\over\tau}.
\]
This is a density-operator distance; no unadjusted vector-phase distance
is substituted. Energy errors are proved from the explicit occupation
law, not inferred from trace distance. At \(\tau=100\), in particular
\(D_{\rm tr}<0.00448\) and \(E_{\rm exc}<0.000051\).
These bounds do not say the state is exactly the ground at finite time.

## AQ.6 Full renormalized mean work and the sharp-insertion boundary

At every finite \(K\), the exact balance is
\[
 {d\over dt}\langle H_K(t)\rangle
 =\dot r(t)\langle B_K+C_K'(r)\rangle .
\]
The instantaneous ground has
\[
 \langle B_K\rangle_{\Omega_{r,K}}
 ={1\over4}\sum_{k\le K}k^2(\omega_{k+}^{-1}-\omega_{k-}^{-1}).
\]
Its \(-r/(4k)\) tail cancels \(C_K'=r\sum1/k/4\),
leaving \(e_K'(r)\). In the actual prepared state write its instantaneous
occupation and anomalous covariance as \(n_{k\sigma}\) and \(m_{k\sigma}\),
with \(|m|=\sqrt{n(n+1)}\). Then the exact remaining term is
\[
 \langle B_K+C_K'\rangle-e_K'(r)
 =\sum_{\sigma,k\le K}{\sigma k^2\over2\omega_{k\sigma}}
          (n_{k\sigma}+\operatorname{Re}m_{k\sigma}).
\]
The uniform \(0.60/(\tau k^3)\) bound makes this tail \(O(k^{-2})\),
uniform in the preparation interval. Thus summation and time integration
commute, and the actual nonselective mean work is
\[
 W_{\rm ext}=\int_0^\tau\dot r\,
       \lim_K\langle B_K+C_K'\rangle dt
       =e(1/5)-e(0)+E_{\rm exc}.
\]
It includes the interaction and the same counterterm datum.
Allowed finite scalar changes \(c(r)\) change this work by
\(c(r_f)-c(r_i)\); we keep the inherited \(c_r=0\) energy datum fixed.

The limit above is a **mean insertion**, not a sharp-time Hilbert
operator with finite variance. Already in the AP ground
\(\operatorname{Var}B_K\ge K/4\). The work balance is obtained from
finite-cutoff expectations and a dominated integral. It does not
require or prove \(B_{\rm ren}\Psi\in\mathcal H\).

With the external source held fixed in metric variation, the local Ward
identity has the source term
\(\nabla^\mu\langle T_{\mu\nu}\rangle
=-\langle B_{\rm density}+C'_{\rm density}\rangle\partial_\nu r\).
A complete autonomous controller would have to supply the opposite
stress transfer. External work cannot be erased by calling the ramp
adiabatic.

The chosen vacuum energy difference can make this external work negative.
A return to r=0 from the same initial vacuum instead has net work equal
to the final nonnegative free energy; finite scalar endpoint terms cancel
on the cycle. This is external-source accounting, not free apparatus energy.

## AQ.7 Same-state smooth source noise and cutoff lapse contacts

Let incoming-normalized modes \(u_{k\sigma}\) solve the exact oscillator
equation, \(u=e^{-ikt}/\sqrt{2k}\) in the past.
For \(B(t)=\frac12\sum(q_+^2-q_-^2)\), its connected Wightman kernel is
\[
 C_{BB}(t,s)={1\over2}\sum_{k,\sigma}k^2
                   [u_{k\sigma}(t)u_{k\sigma}^*(s)]^2 .
\]
For real smooth compact time test \(g\),
\[
 N_B(g,g)={1\over2}\sum_{k,\sigma}k^2
               \left|\int g(t)u_{k\sigma}(t)^2dt\right|^2\ge0.
\]
The true-equation Hadamard/Wick domain makes this spacetime smearing
finite. Equivalently the exact positive pair-vector series converges;
its finite constituent projections give the actual cutoff limit.
At a constant coupled ground it reduces to
\(\frac18\sum k^2|\widehat g(2\omega_{k\sigma})|^2/\omega_{k\sigma}^2\).
The scalar \(C_K'\) drops out of centered noise; \(C_K''\) does not drop
out of response.

In the finite-cutoff homogeneous canonical chart with externally fixed
\(r(t)\),
\[
 H_K(N,r)=N[H_{0,K}+rB_K+C_K(r)],\quad
 C_{Nr}=B_K+C_K',\quad C_{rr}=NC_K''I,\quad C_{NN}=0,
 \quad C_K''=\tfrac14\sum_{k\le K}1/k.
\]
Same-branch log-CTP contacts carry the Hamiltonian signs
\(-i\langle C\rangle\) on ++ and \(+i\langle C\rangle\) on --.
There is no corresponding bulk contact between opposite branches.
One cannot discard the divergent contact before matching the common
renormalized response. A profile programmed as a function of
\(\int Ndt\), instead of held fixed, has extra chain-rule lapse terms.
Full spatial lapse variation, finite boundary terms, metric response and
a common normal gravitational state remain open.


A useful **static ground-family** response check, distinct from the
fixed-initial-state finite-time CTP Hessian, is
\[
 e_K''(r)=C_K''+
 2\sum_{n\ne0}{|\langle n|B_K|\Omega_{r,K}\rangle|^2\over e_K-E_n}
 =\sum_{k\le K}\left\{{1\over4k}
 -{k^2\over8}[(k^2+r)^{-3/2}+(k^2-r)^{-3/2}]\right\}.
\]
Each real oscillator pair has squared matrix element \(1/(8\omega^2)\)
and gap \(2\omega\). The spectral response cancels the logarithmic
\(C_K''\) contact exactly, leaving an \(O(r^2k^{-5})\) summand.
For \(r\le1/5\), the discarded absolute tail at \(K\) is bounded by
\(15r^2/(128\kappa^{7/2}K^4)\).
In this datum \(e''(0)=0\). This finite response does not subtract the
positive symmetric noise or the sharp variance divergence.

## AQ.8 Connect this actual prepared state to the AP sign record

The prepared state is zero-mean Gaussian and invariant under joint sign
parity. Apply the same source-only \(q_0=\pm1\) displacement after
\(t=\tau\), evolve for \(T=1/2\) with the final constant Hamiltonian,
and use AP's full Gaussian \(p_{p,1}\) instrument, \(\sigma=1/10\).
No arrival condition or outcome is postselected.

For monotone \(r\), the exact squeezing integrals at \(k=1\) are
\(L_+=\frac14\log(1+r)\) and
\(L_-=-\frac14\log(1-r)\).
At any final constant-coupling waiting time,
\[
 \operatorname{Var}p_{p,1}
 \le{a_+e^{2L_+}+a_-e^{2L_-}\over4}
 ={2+r\over4}={11\over20}.
\]
The mean response remains precisely \(m(T)\) from AP, since only the
encoding changes the mean. Hence the same actual-preparation record has
\[
 d_{\rm prep}\ge e^{-7/25}\sin m(1/2)>0.069 .
\]
This direct covariance bound does not infer unbounded observables from
trace distance.

The source encoding adds \(1/2\) to the mean energy; the complete
Gaussian reader adds \(25/2\). Thus
\(\langle H_r\rangle_{\rm out}=e+E_{\rm exc}+13\).
One also has
\(\operatorname{Var}(q_s+rq_p)\le14/25\) in the zero-mean prepared state,
and the same bound for the centered \(q_p+rq_s\) at readout.
Parity removes the energy/linear-encoding covariance. Therefore
\[
 \operatorname{Var}_{\rm out}H_r
 \le V_E+{14\over25}
       +25\left({14\over25}+z_T^2\right)+{625\over2},
\]
where \(z_T\) is the AP coherent mean force.
Each conditional readout state and the nonselective output retain the
true final \(P_r\)-Hadamard property and all coupled-energy moments:
only a finite pair of modes is changed, and the high-mode final
Hadamard factor is common.

The two sign codes still have identical complete energy and quadratic
stress laws. This is a source-sign calibration, not a geometric-charge
calibration. Encoding and readout are global operations, their physical
hardware stress is not constructed, and the external ramp is not
autonomous. AP's ground-code static-pressure rejection must not be
silently relabeled as the exact mean equation for this different squeezed
prepared state.

## AQ.9 What is closed and what follows

Closed in this specified local linear model: actual finite-past correlated
preparation, a fixed counterterm/phase convention, positive normal
same-state history, completed-endpoint Hadamard and energy domains,
uniform intermediate energy/work control, smooth source noise and a
complete calibrated finite-time sign record. Its limits are explicit.

The next gravitational task is to promote the external source and reader
to a local dynamical apparatus, choose all finite covariant stress data,
and solve the same-state lapse/pressure/constraint response with that
apparatus included. None of the bounds here substitutes for that task,
nor resolves AL's nonlinear continuum preparation.

Primary references: Sahlmann–Verch,
https://arxiv.org/abs/math-ph/0008029 , Theorems 5.5/5.8;
Hollands–Wald, https://arxiv.org/abs/gr-qc/0103074 , Section 2;
Moretti, https://arxiv.org/abs/gr-qc/0109048 , Theorem 2.1.
The new constants and model-specific work/record calculation are derived
above; these references do not prove an autonomous gravitational device.
