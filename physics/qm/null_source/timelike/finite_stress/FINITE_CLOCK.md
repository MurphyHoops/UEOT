# A normal positive-clock lift with the full source retained

This is a normal approximation to the same positive-dust constraint,
not an additional second dust field. In the physical description dust
energy is E=-H; after the kinematic lift it is the positive momentum p.
Only one of these is included in the corresponding energy ledger.

## 1. Exact isometry and conditional history

The critical state has H<=-h_min with
h_min=(r/2)B_*^(1/3)>0. Take 0<sigma<h_min and a fixed real even
normalized h0 in C_c^infinity(R), with support contained in [-1,1].
Let h_sigma(u)=sigma^-1/2 h0(u/sigma), and define
\[
 (W_\sigma\psi)(p)=h_\sigma(p+H)\psi,\qquad p>0.
\tag{39}
\]
All spectral support lies at p>0, so integration in p gives
W_sigma* W_sigma=I on this gapped subspace. Thus
R_sigma=W_sigma Omega W_sigma* is a normal positive trace-one density
on L2(R_+,dp) tensor the geometry-source Hilbert space.

The positive-energy clock has the covariant time POVM obtained by
compressing the full Fourier PVM. With <t|p>=exp(ipt)/sqrt(2pi),
\[
 \langle t|W_\sigma\psi\rangle
 =g_\sigma(t)e^{-itH}\psi,\quad
 g_\sigma(t)=(2\pi)^{-1/2}\int h_\sigma(u)e^{iut}\,du .
\tag{40}
\]
Where g_sigma is nonzero the conditional state is exactly the fixed
unitary history. For a finite interval I of nonzero probability the
conditional state is its normalized |g_sigma|2-weighted average.
A point time is a density, not a nonzero-probability postselection.

Such half-line time POVMs are standard; see Fewster et al.,
Communications in Mathematical Physics 406, 19 (2025),
DOI 10.1007/s00220-024-05180-7, section 3.1, Example 3.
No self-adjoint time operator canonically conjugate to a semibounded
clock Hamiltonian is assumed.

## 2. Constraint residual and energy

For C=p+H, the residual variable has distribution |h_sigma|2, independent
of the input energy. If mu2=integral u2 |h0(u)|2 du, then
\[
 \langle C\rangle=0,\quad\operatorname{Var}C=\sigma^2\mu_2,\quad
 \langle p\rangle=-\langle H\rangle,\quad
 \langle p^2\rangle=\langle H^2\rangle+\sigma^2\mu_2.
\tag{41}
\]
The full normal kinematic state is not an exact strong zero-constraint
state. Conditional accuracy does not erase the residual (41).

The unconditioned geometry-source marginal is exactly
\[
 \bar\Omega_\sigma=\int |g_\sigma(t)|^2
                       e^{-itH}\Omega e^{itH}\,dt .
\tag{42}
\]
It generally changes the bare source and geometry; it is not Omega.
Because g_sigma is Schwartz and the volume propagation is polynomial,
(42) has every finite polynomial volume moment. In particular the actual
kinematic positive energy
\[
 J_{\rm kin}=p+qv+K_0
\]
has
\[
 \langle J_{\rm kin}^2\rangle
 \le3[\langle H^2\rangle+\sigma^2\mu_2+
                     q^2\langle v^2\rangle_{\bar\Omega_\sigma}
                     +\langle P^4\rangle/(4\delta^2)]<\infty .
\tag{43}
\]
Here p,v,P mutually commute, and the positive multiplication sum has
its natural self-adjoint domain. No extra -H is counted in (43).

## 3. A completely explicit finite-window lower bound

Choose h0 proportional to exp(-1/(1-u2)) on |u|<1 and zero elsewhere.
It is positive, even, smooth and normalized. Its decreasing radial
square density gives 0<mu2<1/3 by the integral rearrangement inequality
against the increasing function u2.

For |t|<=T and sigma T<pi/2,
\[
 |g_\sigma(t)|^2\ge
 {\sigma\over2\pi}\cos^2(\sigma T)
       \left(\int h_0\right)^2 .
\]
The unnormalized bump is at least exp(-4/3) on [-1/2,1/2], and its
squared integral is at most 2exp(-2). Thus
\[
 \Pr\{|t|\le T\}\ge
 {\sigma T\,e^{-2/3}\over2\pi}\cos^2(\sigma T)>0.
\tag{44}
\]
finite_clock.py evaluates the declared example sigma=1/2, T=1/24 and
verifies sigma<h_min. These are model time/energy units.

## 4. Resolution has a geometry cost

g_sigma(t)=sqrt(sigma)g0(sigma t). Combining (22) with (42) bounds
<v^q> by a constant times 1+sigma^(-3q) as sigma goes to zero.
The state is finite for every fixed positive sigma, but this control is
not uniform at zero residual. It is an upper-bound deterioration, not
a proved matching divergence or an optimal resource law.

This lift establishes a finite-source normal clock/history construction
in the reduced model. It is not a local clock apparatus, a covariant
dust RSET, or recovery of the original AE/instrument history.

## 5. Higher positive energy moments in this representation

In the kinematic representation the positive multiplication operators
commute, so for each integer k>=1,
\[
 J_{\rm kin}^k\le3^{k-1}[(qv)^k+p^k+(P^2/(2\delta))^k],
\]
and the positive homogeneous density
rho_+=U0+p/(V0v)+P2/(2V0v2) satisfies the analogous bound using
v>=delta. All these moments are finite after the normal clock lift.
This stronger statement applies to this commuting kinematic sum.
It does not assert every high moment of the noncommuting compressed
physical J in POSITIVE_SOURCE.md, or a unique covariant RSET.
