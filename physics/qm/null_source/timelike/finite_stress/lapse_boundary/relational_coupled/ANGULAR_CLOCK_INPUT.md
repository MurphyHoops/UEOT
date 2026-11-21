# A directed scalar-clock source and its actual preparation/readout costs

This source-level construction changes the current thin bare state. It
uses the same original two massless fields and the same fixed incoming
radial profile. It does not itself embed that full bare state into a
chosen quantum-geometric constraint domain. The separately constructed
Dirac angular bridge in SYMMETRIC_CLOCK has its own stated scope.

## A1. A normal energy-preserving angular change

In the two zero-mode momentum plane write P=(r cos theta,r sin theta).
The frozen thin states of BOUNDARY_STATE factor, under the polar unitary
identification, as
rho_old=tau_(radial,shell,rest) tensor |u0><u0|,
where u0(theta)=(2pi)^-1/2. The radial/shell correlations in tau are retained.

Choose a real nonnegative normalized smooth g(theta), compactly
supported in (-pi/4,pi/4), and replace u0 by g in both N2 branches:
rho_g=tau tensor |g><g|. The momentum wavefunctions remain smooth on
compact annuli away from r=0. They are normal Schwartz states; the
fixed-background Hadamard singularity is unchanged by this finite-mode
modification. For the same once-selected A,e_N,sigma,
\[
 P_1>\sqrt{A^3(e_2-\sigma)}>0.                              \tag{A1}
\]
The radius and its correlations with the unchanged shell number are
preserved. Thus the complete incoming total-energy law, including its
width Var H_in=sigma² mu2, is exactly unchanged.

There is an explicit source Hilbert-space unitary. Set
c=<u0,g> real, v=(u0-g)/sqrt(2(1-c)) and
H_theta=I-2|v><v|. Then H_theta u0=g. It acts only on angle, so it
strongly commutes with P1²+P2² and with the incoming full energy.
It is a mathematical energy-conserving source unitary, not a local
autonomous apparatus or an implementation with a complete controller
stress tensor.

The original action has pi_j=a² D phi_j=P_j under the common transport
q=a(Q+I P), p-kappa q=P/a. Thus A1 concerns the same original Noether
momentum, rather than a newly invented clock charge.

## A2. Exactly what the change preserves and costs

The total derivative two-point function governing the summed minimal
massless stress depends on sum_j <P_j²>, the unchanged high-mode
quadratic moments and the zero/high cross moments, which remain zero.
Constant Q solutions are removed by stress derivatives. Hence on the
same canonical field transport the total mean-RSET functional is
preserved. This is not equality of individual-species W2, the complete
bare state, or all higher records. In particular angular gradients
alter Q moments.

Because the old angular factor is pure,
\[
 D_{\rm tr}(\rho_g,\rho_{\rm old})
 =\sqrt{1-|\langle u_0,g\rangle|^2}.
\]
Cauchy--Schwarz on a sector of angular measure pi/2 gives
|<u0,g>|²<=1/4, hence
\[
 D_{\rm tr}(\rho_g,\rho_{\rm old})\ge\sqrt3/2.                \tag{A2}
\]
The inequality is strict for the stated compact interior support.
This is stronger than the sector-projection measurement bound 3/4.
The unitary has changed the complete source substantially despite
preserving its complete incoming energy law.

A positive P1 spectral sector does not provide a self-adjoint canonical
field-coordinate clock within that restricted sector. The physical
clock observables and inner product need the separate constraint
construction; positivity of this momentum alone is not that construction.

## A3. A quantitative single-reading calibration gate on the actual quiet history

At the current finite slice a_i=A and I=I_i, define the original
zero-mode field-value reading
T_i=Q1+I_i P1. The actual proper-time mean drift on the prescribed
common history is <P1>/A³>0. The frozen incoming proper-energy operator
H_in of BOUNDARY_STATE has
\[
 [H_{\rm in},T_i]=-iP_1/A^3,\qquad
 \Delta H_{\rm in}=\sigma\sqrt{\mu_2}.
\]
H_in here is the once-defined incoming charge operator. It is not being
identified with every instantaneous full Hamiltonian on the evolving
geometry. The commutator and the actual zero-mode drift suffice.

All these moments exist in the stated source state, so Robertson gives
the RMS width of a field-value reading calibrated by that initial mean
drift:
\[
 \delta\tau_{\rm rms}:={\Delta T_i\over|\langle P_1\rangle|/A^3}
 \ge {1\over2\sigma\sqrt{\mu_2}}.                            \tag{A3}
\]
No zero/shell independence is assumed. The preserved complete energy
law, including its correlations, is used.

For the frozen decreasing bump mu2<1/3 and sigma=sqrt3/(100A), so
delta tau_rms>50A. The independent interval certificate compares this
with the actual c=exp(-20000) quiet-window proper duration
[1634.4938051130607,1634.4945784116621] in model units and obtains a
ratio greater than 2499. This is not seconds or experimental precision.

A3 concerns this source, one field-value reading and this mean-drift
calibration. It is not a bound for every POVM, repeated estimation,
arbitrary multi-clock protocols or every scalar-clock physical state.
It does show that the directed momentum and preserved thin energy law
by themselves do not supply a precise reading of the current window.
A full instrument, apparatus energy and backreaction remain to be
derived from their action.

## A4. Homogeneous influence, a Gaussian restriction and local preparation

There is more preservation than just the mean in one precise class.
For admissible **homogeneous prescribed histories**, identified on the
same original-phi Cauchy data and with the same AE prescription, the
zero-mode propagators depend only on P1²+P2². They and the independent
nonzero-mode propagators commute with H_theta. Cyclicity therefore gives
F_g[+,-]=Tr(U_+ rho_g U_-^\dagger)=Tr(U_+ rho_old U_-^\dagger).
This is also immediate from BOUNDARY_STATE (77b), whose conditional
zero-mode factors depend only on radius. It includes the retained
zero/shell correlations. It is not equality for arbitrary inhomogeneous
mode mixing or a quantum-geometric/device CTP history. In q coordinates
the endpoints and initial density must be transported together.

An exact source-only Gaussian gate on the two zero modes cannot realize
this angular change while preserving P1²+P2². Its affine canonical map
has P'=C Q+D P+d. Equality of the full quadratic operator forces C=0
from C^T C=0, d=0 from the constant term, and D^T D=I. It only rotates
the old radial momentum law, leaving the uniform angular distribution
unchanged. The stated Householder is non-Gaussian. This restriction does
not cover a larger interacting apparatus, energy exchange or conditioning.

A second necessary condition comes from locality in the **complete
local free QFT on the prescribed geometry**, not from a sharp finite-K
truncation (which has no exact microcausality).
The species-1 derivative field, intended as a clock readout, has
\[
 n\cdot\nabla\langle\Phi_1\rangle
   ={\langle P_1\rangle\over\sqrt{V_0}\,a^3}.
\]
It vanishes in the old uniform angular state and is strictly positive
in the directed state at every spatial point. If a proposed nonselective
probe coupling is supported in a compact region K with a nonempty open
causal complement O in the compared free-out spacetime, take a compact
nonnegative derivative test there. Its mean changes. Finite moments
imply that some bounded local Weyl observable exp(is derivative(Phi1)[j])
also has a changed expectation.

Fewster--Verch Proposition 3.1(b) and Eq.(3.23) show that the nonselective
local channel is the identity on that causal-complement algebra.
It therefore cannot output the entire rho_g in this situation.
This concerns the full output including all records; selective branch
conditioning is a different statement.

In closed FLRW, causality is conformal to the Einstein cylinder.
If K lies before the output slice, its spatial support stays in a
unit-S3 cap of radius r, and its earliest conformal time is eta_pre,
a strict inequality eta_out-eta_pre+r<pi leaves an open neighborhood
of the antipode outside J(K). Hence a necessary condition for this
globally changed field-mean output is
\[
                    \eta_{\rm out}-\eta_{\rm pre}+r\ge\pi.
\]
A preparation wholly within the current 1/50 conformal window cannot
remain confined to any fixed cap of radius r<pi-1/50. Any cap known
to contain the full coupling support must meet that radius bound.
This does not require the coupling to fill every point of a large cap. A longer real preparation past,
distributed apparatus, or a local clock goal is not excluded.
No apparatus stress or experiment time in seconds is inferred.

Finally, the new two radial/NOON support branches still have the same
complete total-energy law. The earlier rank-two spectral-compression
argument for an unchanged complete bare marginal therefore still applies
to rho_g. Directed clock momentum does not by itself make an independent
carrier cancel the source constraint charge.
