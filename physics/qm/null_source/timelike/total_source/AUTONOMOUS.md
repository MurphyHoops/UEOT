# A finite-energy autonomous pulse on one constrained leading-GR history

This is a separate classical homogeneous benchmark. It does not replace the original actual CQ source, the small-cap field probe, or the complete AE/QFT theory. The positive U0 is taken from the frozen input, but the initial momenta below are newly specified benchmark data.

## Full action, Hamiltonian and one time evolution

Use the dynamical three-field action in FIELDSPACE.md with F=1 and kappa a smooth compact bump of chi. On closed FLRW set V0=2pi^2 and use homogeneous field values X=(chi,phi,psi). Their canonical momenta are pi=V0 a^3 G Xdot/N; these differ by sqrt(V0) from the previous Y0-normalized field coordinates. The homogeneous Hamiltonian is
\[
 H[g]=\frac{N}{V_0a^3}{\cal K},\quad
 {\cal K}=\frac{\pi_\chi^2}{2F^2}
 +\frac{\pi_\phi^2+\pi_\psi^2-2\kappa\pi_\phi\pi_\psi}{2(1-\kappa^2)}.
\]
With zeta=integral N/(V0 a^3)dt, this is a time-independent Hamiltonian. Both shift momenta pi_phi, pi_psi and K are conserved. Write its second term as W(chi). Then
\[
 \frac{F^2}{2}(d\chi/d\zeta)^2+W(\chi)={\cal K}.
\]
If K>sup W and the incoming clock momentum is positive, chi crosses a compact coupling region monotonically. W<=W0/(1-kappa_*) supplies an explicit sufficient finite-energy condition.

The probe displacement relative to free evolution across the same zeta interval is
\[
 \Delta\psi=\int\frac{\kappa^2\pi_\psi-\kappa\pi_\phi}{1-\kappa^2}d\zeta.
\]
For pi_psi=0, pi_phi>0 and a nonzero nonnegative bump, it is strictly negative. At fixed incoming clock momentum Pi_chi its magnitude equals
\[
 F\pi_\phi\int
 \frac{\kappa\,d\chi}
 {(1-\kappa^2)\sqrt{\Pi_\chi^2-\pi_\phi^2\kappa^2/(1-\kappa^2)}}.
\]
Its derivative with respect to pi_phi is positive wherever the gap is positive. This is a real source-sensitive classical QND shear, not a field relabelling.

## Complete matter source and the same geometry

The complete matter density and pressure are
\[
 \rho_m=p_m={\cal K}/(V_0^2a^6).
\]
Together with U0 and G=2T,
\[
 H^2=2U_0/3+2{\cal K}/(3V_0^2a^6)-a^{-2}.
\]
The spatial equation follows by differentiating this constraint with K fixed. No controller energy is omitted, and no root is reselected along the history.

Choose
\[
 a_0=\sqrt{3/(2U_0)},\quad \Pi=V_0a_0^2,\quad
 L=1/20,\quad \kappa(\chi)=b(\chi/L)/4,
\]
where b(x)=exp[-x^2/(1-x^2)] for |x|<1 and zero otherwise. Set chi0=-L, pi_chi=pi_phi=Pi, pi_psi=0. Then K=Pi^2 and H0=sqrt(2/3)/a0 satisfy both homogeneous initial constraints.

For a>=a0, H stays positive and H<=Hbar=sqrt(5/3)/a0. Also W<=8Pi^2/15, so dchi/dzeta>=Pi sqrt(14/15) and
\[
 \zeta_{cross}\le2L/[\Pi\sqrt{14/15}].
\]
Cosmological expansion leaves only a finite future zeta length; this must be checked. Since a(t)<=a0 exp(Hbar t),
\[
 \zeta(t)\ge\frac{1-e^{-3\bar Ht}}{3V_0a_0^3\bar H}.
\]
Our data obey 3V0 a0^3 Hbar zeta_cross<=3/(2sqrt(14))<1. Thus the pulse actually completes on this same expanding solution, with
\[
 t_{cross}\le-\frac{a_0}{3\sqrt{5/3}}
 \log(1-3/(2\sqrt{14})).
\]
On |chi|<=L/2, b>=e^{-1/3}>2/3; with dchi/dzeta<=Pi this gives
\[
 1/120<|\Delta\psi|<(2/75)\sqrt{15/14}.
\]
The free-out clock momentum equals its incoming value, as do both shift momenta. The full stiff source is K/a^6 throughout: internal readout dynamics does not create a change in the complete conserved source.

## Explicit quantum reduction, without a quantum pulse shortcut

For the reduced mechanics choose L2(R^3,dmu_G), dmu_G=F sqrt(1-kappa^2)dchi dphi dpsi, and the nonnegative Friedrichs realization Khat=-Delta_G/2. Its positive quadratic form and the uniformly positive smooth field-space metric specify a self-adjoint Hamiltonian. This Laplace–Beltrami ordering is an additional explicit quantum input.

All prescribed-history Hamiltonians are N Khat/(V0 a^3), so one fixed normal state has
\[
 {\cal F}_{hom}[g_+,g_-]
 =Tr\rho\,e^{-i\widehat{\cal K}(\zeta_+-\zeta_-)}.
\]
All clock reflection, transmission and entanglement remain in the same unitary evolution. The classical crossing/gain bounds are not a no-reflection theorem for arbitrary normal wavepackets. Classical homogeneous consistency is not a quantum truncation theorem for the full interacting QFT. An averaged Einstein model using E Khat, a random-source model and quantized geometry are distinct additional contracts.

No old or new mode/geometry ODE is integrated for these results.
