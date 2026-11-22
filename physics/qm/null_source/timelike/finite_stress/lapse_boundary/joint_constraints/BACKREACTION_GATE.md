# JC20 — The clock's gravitational cost and the failure of the old background

## 1. An exact kinetic difference, independent of subtraction constants

On the same initial slice take two clock states with identical coordinate Gaussian, identical covariances and identical Y/body factors. Change only the homogeneous mean unit-normal X momentum from zero to 1/g. All coordinate-dependent interactions in CLOCK_ACTUATOR and all state-independent counterterms are unchanged. The minimal massless clock gives exactly
\[
 \Delta\rho_X=\Delta p_X={1\over2g^2},\qquad
 \Delta j_i=0,\qquad \Delta E_X={V_0\over2g^2}.                  \tag{1}
\]
This is a difference of actual initial states with the same subtraction prescription. It is not eliminated by changing a vacuum constant. The finite-K statement is exact, and the free-clock difference also concerns only a smooth zero-mode displacement.

At g=10^-40 the added energy exceeds 9.5e80 in model units. The complete apparatus reference stress has not been covariantly renormalized in this entry; (1) does not silently set that additional reference stress to zero.

### A complete energy-variance lower bound

This apparatus also has an exact fluctuation cost. At its initial time
write the full normal finite-mode wave function as
psi(q)=exp(i pbar dot q) varphi(q), where varphi is a real positive
product Gaussian. The complete positive Hamiltonian is
H=-Delta/2+V(q) with real V. After removing the plane-wave factor,
the imaginary part of (H-<H>)psi is exactly -i pbar dot grad varphi.
The real potential, including the full interaction, cannot cancel it.
Independence of the Gaussian coordinate factors gives
\[
 \operatorname{Var}H_{\rm total}
 \ge\sum_j\bar p_j^2\operatorname{Var}P_j
 \ge {V_0\over4a g^2}={V_0\over16g^2}\quad(a=4).
\]
At g=10^-40 this exceeds 1.18e80 in squared model energy units.
A real scalar subtraction does not change the variance. The complete
autonomous unitary preserves its energy spectral law. Body parity
makes the symmetrized covariance of H with the code's linear momentum
zero, so the two encoders add the nonnegative variance
eta^2 <Pi_f^2>. The complete nonselective Gaussian reader also adds
the nonnegative increment in CLOCK_ACTUATOR. The lower bound therefore
persists through the full-outcome readout. It is not a lower bound for
every conditionally selected outcome and is not a calibrated metric
fluctuation.

## 2. A necessary small-background constraint with the unproved part exposed

The old AP datum has fixed G and Lambda and satisfies the unit-ESU constraint
\(6=2\Lambda+16\pi G\rho_0\).
For a proposed new initial slice assume the following explicit bounds:

- the averaged scalar curvature is at most 6+delta_R;
- the extrinsic-curvature norm is at most kappa;
- the actual clock normal mean is at least (1-delta_v)/g in magnitude;
- all remaining density changes, including the new-field reference subtraction and any moved higher-curvature terms, are bounded below by -B.

No bound on those remaining terms is inferred from the finite-K record norm. The Hamiltonian constraint and
\(({\rm tr}K)^2-|K|^2\le2|K|^2\)
then require
\[
 \boxed{\delta_R+2\kappa^2\ge
 {8\pi G(1-\delta_v)^2\over g^2}-16\pi GB.}                     \tag{2}
\]
A declared small-backreaction contract with B, delta_R and kappa of order one cannot meet (2) at the explicit g. For illustration, even allowing B=10^8 and delta_v=0 leaves the right side above 2.1e84. This is a conditional rejection with B stated, not an unqualified theorem about all semiclassical matter states. A finite R^2 term needs its relevant higher metric derivatives controlled; C^2-small geometry alone is insufficient to bound that contribution by B.

There is an independent static check. On unit ESU the two Einstein mean equations imply
\(\rho+p=1/(4\pi G)\). The added clock enthalpy is \(1/g^2\).
Changing only Lambda cannot absorb it. Keeping the old static geometry would need a real compensating enthalpy response of the same size or a changed G/datum. None has been supplied.

If only the initial scalar constraint is balanced with h=gamma and
K=H gamma, and all other mean densities retain the old value, then necessarily
\[
 6H^2={8\pi G\over g^2},\qquad
 |H|={\sqrt{4\pi G/3}\over|g|}.
\]
At the chosen g this is about 6.12e41, with inverse about 1.64e-42 model time units. This is an initial constraint scale, not a solved full apparatus evolution.

The old AP Cauchy state also cannot be silently kept when K changes.
Already for a massless conformal scalar on a FRW slice a=1,a'=H,
the canonical variable chi=a phi gives p_phi=pi_chi-H chi. The
conformal-vacuum covariances in the old physical chart are
\[
 QQ={1\over2k},\quad \operatorname{sym}QP=-{H\over2k},\quad
 PP={k\over2}+{H^2\over2k}.
\]
Relative to the old static chart the pair coefficient is
beta_k=-iH/(2k). With degeneracy k^2 its squared norm diverges linearly
for H nonzero. These are legitimate Hadamard data on the new geometry,
but not a normal state obtained by a unitary in the old AP bare chart.
The constant paired masses affect subleading ultraviolet terms and
require the actual source/metric jets as well. Thus the conditional
large-H scale above is not an Einstein initial-data solution with the
old density rho_0 already supplied.

## 3. A solved clock-only comparison shows why the program must be recomputed

To make the dynamical issue concrete, consider a **separate classical** closed FRW model containing only a homogeneous minimal massless scalar and the same positive Lambda and G. It is not the five-field quantum apparatus. Set a(0)=1, dot X(0)=1/g and choose the expanding branch. The exact first integrals are
\[
 \dot X={1\over g a^3},\qquad
 H^2={C\over a^6}+{\Lambda\over3}-{1\over a^2},\qquad
 C={4\pi G\over3g^2}.
\]
If C>=2(1+epsilon)^6, the time spent with
\(1\le a\le1+\epsilon\) obeys the conservative bound
\[
 \Delta t\le {\sqrt2\,\epsilon(1+\epsilon)^3\over\sqrt C}.
\]
Thus the unit-radius time program has no order-one stationary window in this comparison as g tends to zero.

There is also a future bound for the clock coordinate itself. Put
\[
 A=(3C/\Lambda)^{1/6}.
\]
If A^4<=C/2 and A^2>=6/Lambda, then H^2>=C/(2a^6) for 1<=a<=A and H^2>=Lambda/6 for a>=A. Both bounds are positive, so this expanding solution continues to arbitrarily large a. Integrating
\(d(gX)/da=a^{-4}/H\) yields
\[
 \Delta(gX)_{\rm whole\ future}
 \le{\sqrt2\over\sqrt C}\left(\log A+{1\over3}\right).             \tag{3}
\]
The certificate checks these hypotheses with the current G,Lambda and g=10^-40. The bound is below 10^-39. Starting at gX=-1, this clock-only expanding comparison cannot even reach the gate support gX>-.2. This conclusion is not transferred to the unsolved five-field or quantum system; it demonstrates exactly why replacing the geometry invalidates the old free program X=t/g and Y=cos(2t)u/g.

## Decision

The finite-K normal actuator and its eight matter-plus-interaction means can be constructed. Its clock source is not a perturbation of the old signed ESU background. The next common-history construction must solve the geometry with the full source, use the resulting physical clock trajectory, and recompute both source preparation and readout. The present results do not establish that any such full construction exists, and they do not rule out all alternative apparatus designs.
