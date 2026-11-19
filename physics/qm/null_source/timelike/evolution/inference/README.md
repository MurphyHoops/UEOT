# Finite-window identification with an uncalibrated curvature coupling

**Result:** a nine-mode source coefficient can be identified without fixing
the finite curvature counterterm, with two different information contracts.

- **Keep the original total stiff second moment and zero-mode covariance
  calibrated:** two new density readings in the two original nominal time
  supports suffice to fit the nine-mode coefficient and the curvature
  coefficient. Their certified worst-case epsilon error gain is below
  **9.352409**, with a directed interval rank certificate.
- **Treat the combined stiff calibration as an additional unknown:** the
  two density averages alone fail. Three independent geometry contractions
  can fit all three coefficients; `[E_1, rho_2, E_2]` has a certified error
  gain below **15.748363**. A fourth reading, `rho_1`, supplies a held-out
  relation with certified residual error gain below **1.999941**.

The first contract is the least additional geometry information when the
original source calibration is retained. The second is an explicit upgrade
for fitting uncertain source energy, not a prerequisite for eliminating the
curvature coefficient. A bounded calibration uncertainty can instead be
propagated through the two-reading design.

This is a conditional relation between physical observables. No new geometry
apparatus has been implemented or measured, no old Ramsey result is relabelled
as a geometry datum, and no experimental records are generated here. A
certified dynamic reference at four points is not a certified reference
integral across the windows. The latter, the added apparatus calibration, and
a finite-coupling remainder bound remain required before this inference can
be applied to data.

## 1. Which physical freedom remains?

Use the same source and reference contract as
[`../../continuation/SOURCE.md`](../../continuation/SOURCE.md):
the original massless minimally coupled real scalar, the closed-S3 auxiliary
reference selected by `instrument.state_scale`, its regular Gaussian zero
mode, and the original finite-rank nine-mode state change. In the physical
homogeneous region,

\[
 a(\eta)^2=3c,\qquad c=\cos(2\eta),\qquad d\tau=a\,d\eta,
 \qquad 4\pi G=1.
\]

We assume that the finite Newton and cosmological couplings have already been
independently calibrated. In the standard local covariant, dimension-four
renormalization ambiguity, the remaining tensors are the variations of
\(R^2\), \(R_{ab}R^{ab}\), and \(R_{abcd}R^{abcd}\).
Let their normalization be the one in Decanini--Folacci, equations
(136)--(142). Here H3 denotes the variation of Riemann-squared; it is not
Anderson--Eaker's differently defined (3)H anomaly tensor. The latter must
not be mistaken for an independently adjustable counterterm. Their Euler and Weyl-squared identities in four dimensions give

\[
 H_1-4H_2+H_3=0,\qquad
 H_3-2H_2+\tfrac13H_1=0 \quad\text{on conformally flat metrics}.
\]

The second equation holds because the first variation of the integral of
Weyl-squared vanishes at Weyl tensor zero. Consequently

\[
 H_2=H_3=\tfrac13H_1,
 \qquad \alpha_{\mathrm{eff}}=C_1+(C_2+C_3)/3.
\]

There is one effective curvature coefficient **within this declared
four-dimensional bulk ambiguity class and conformally flat family**. This
does not discard boundary effects, anisotropic perturbations, independent
higher-dimensional effective-action operators, or uncalibrated \(G,\Lambda\).
Those would change the inference model.

Here \(\alpha\) is defined by adding \(\alpha H_1\) to the **right-hand,
stress-energy side** of the field equation. A coefficient originally placed
on the gravity side has the opposite sign after it is moved to this side.
Choosing a numerical subtraction scale or setting \(\alpha=0\) does not
select a physical theory, and the deterministic Core supplies no such choice.

Primary sources:

- Decanini and Folacci, *Hadamard renormalization of the stress-energy tensor*,
  equations (136)--(142): https://arxiv.org/pdf/gr-qc/0512118
- Anderson and Eaker, *Analytic approximation and an improved method for
  computing the stress-energy...*, equations (10)--(14):
  https://arxiv.org/pdf/gr-qc/9906055

### Independent sign and contraction check

With the conventional \((-+++)\) metric, the Decanini--Folacci expression is

\[
 (H_1)_{ab}
 =2\nabla_a\nabla_bR-2RR_{ab}
 +g_{ab}(-2\Box R+R^2/2).
\]

On the same background,

\[
 R=-2c^{-3},\quad R_{nn}=2c^{-3},\quad
 (H_1)_{nn}=-2RR_{nn}-6H\dot R-R^2/2
 =\frac{6(4c^2-3)}{c^6}.
\]

This agrees with direct substitution in Anderson--Eaker equation (10b),
including their \((+---)\) signature and curvature convention. Their trace
\(\rho-3p\) is \(-48(2c^2-3)c^{-6}\), so

\[
 (H_1)_E\equiv\frac{(H_1)_\rho+3(H_1)_p}{2}
 =\frac{18(4c^2-5)}{c^6}.
\]

The script checks both computations symbolically. Its conservation check
also verifies \(E=-\rho-c\,\partial_c\rho\) for each of the three basis
sources, because \(a^2=3c\). No energy condition is assumed; \(E\) names
the combination \((\rho+3p)/2\), which may have either sign.

## 2. Fixed physical radius, not a change of time slicing

Let the homogeneous coherent-source momentum have mean \(\bar P\),
classical displacement variance \(\sigma_P^2\), and full second moment
\(M_2=\mathbb E[P^2]=\bar P^2+\sigma_P^2\). A deterministic classical
source is the special case \(\sigma_P^2=0\). Let \(\zeta\) multiply
the independent regular quantum zero-mode momentum covariance,
\(\operatorname{Var}p_0=3\zeta/2\). Only admissible regular Gaussian
covariances are allowed; for example, \(\zeta>0\) with
\(\operatorname{Var}q_0=1/(6\zeta)\) and zero cross covariance saturates
the uncertainty bound and recovers the original covariance at \(\zeta=1\).
The q covariance has no homogeneous zero-mode stress contribution.

The original mixed-displacement family has \(P=3\sqrt3\,Y\),
\(Y=s/2+X\), \(\mathbb EX=0\), \(\mathbb EX^2=3/4\).
Thus \(M_{2,0}=27\), even though
\(\bar P=s\,3\sqrt3/2\) and \(\sigma_P^2=81/4\).
Using the squared mean alone would give the wrong mean stress. The reference
has \(\zeta_0=1\). We consider regular first-order changes with
\(M_2-27=O(\hbar)\), finite \(\epsilon,\alpha,\zeta\), and fixed
physical scale factor \(a\) when comparing geometries. The mixture's
higher moments play no role in this mean-stress relation.

If \(\rho_{\mathrm{ref}}(a)\) and \(E_{\mathrm{ref}}(a)\) are the
same dynamic reference, including its original zero mode, define

\[
 D_\rho(a)=
 \frac{\tfrac32(H_{\mathrm{obs}}(a)^2+a^{-2})-27/(2a^6)}{\hbar}
 -\rho_{\mathrm{ref}}(a),
\]
\[
 D_E(a)=
 \frac{R_{nn,\mathrm{obs}}(a)/2-27/a^6}{\hbar}
 -E_{\mathrm{ref}}(a).
\]

The geometric factors use \(G_{nn}=2\rho\) and
\(R_{nn}=\rho+3p=2E\) in the declared units, after the calibrated
cosmological term is accounted for. The density formula additionally uses
the calibrated homogeneous spatial curvature \(+1/a^2\).

For

\[
 A=\frac{M_2-27}{2\hbar}+\frac{3(\zeta-1)}{8\pi^2},
 \qquad u=A/27,\qquad v=6\alpha,
\]

the first-order relations are

\[
 \begin{pmatrix}D_\rho\\D_E\end{pmatrix}
 =
 \begin{pmatrix}
 c^{-1}-c/2 & c^{-3} & (4c^2-3)c^{-6}\\
 c & 2c^{-3} & 3(4c^2-5)c^{-6}
 \end{pmatrix}
 \begin{pmatrix}\epsilon\\u\\v\end{pmatrix}
 +\begin{pmatrix}r_\rho\\r_E\end{pmatrix}.
\]

The nine-mode density is equivalently \(3/a^2-a^2/6\). The remainders
include finite-order feedback and any discrepancy from the declared family.
They are not bounded by the symbolic first-order calculation alone. An
\(O(\hbar^2)\) unscaled field-equation remainder becomes an
\(O(\hbar)\) remainder in these residuals; setting \(\hbar=1\) in
units is not evidence that it is small.

For contracting points away from the turning point, the equivalent
same-radius linearized Hubble response is

\[
 H_{\mathrm{cl}}=-\sqrt{9/a^6-a^{-2}},\qquad
 \delta H(a)=\frac{\hbar}{3H_{\mathrm{cl}}(a)}
 \left[\rho_{\mathrm{ref}}(a)
       +\epsilon(3/a^2-a^2/6)+A/a^6+\alpha(H_1)_\rho(a)\right]
 +O(\hbar^2).
\]

It is singular as a linearized \(H\) formula at the turning point;
the density constraint above remains the appropriate expression there.
Our windows are strictly on the contracting side.

A change of subtraction scale adds a multiple of \(H_1\) to the reference
and shifts the fitted \(\alpha\) oppositely. The projected \(\epsilon\)
and the held-out relation are unchanged. This is cancellation of a stated
nuisance parameter, not a derivation of the coupling.

### What remains indistinguishable, and what is already calibrated

Geometry sees the deterministic mean, the classical random displacement
variance, and the independent quantum zero-mode covariance only through
\(A\). Their separate contributions cannot be recovered by adding more
geometry radii. This is an exact functional degeneracy. The nine-mode
direction is a different function of radius.

If the original preparation contract \(M_2=27,\zeta=1\) is retained
exactly, then \(u=0\) is already known. It must not be turned into a free
nuisance merely to justify adding more apparatus. The two-density design
below applies. If the calibration gives an interval for u, its uncertainty
can be propagated explicitly.

A homogeneous field-mean readout obeys

\[
 \Delta\langle\phi\rangle=\bar P\,K[a],
\]

where \(K[a]\) is the difference between the two normalized window averages
of \(\int d\tau/a(\tau)^3\), evaluated on the actual calibrated geometry.
It determines only the mean \(\bar P\). The constant field offset cancels,
and the nine-mode mixture has zero first moment. Such a readout determines
\(M_2\) only if the displacement variance is independently known, including
the restricted deterministic case \(\sigma_P^2=0\). Only with that extra
information can a measured u determine the regular zero-mode coefficient
\(\zeta\). This claim is not extended to mixtures with an unknown
displacement variance.

The existing two characteristic-function probabilities do not by themselves
provide that mean and variance calibration. Replacing \(K[a]\) by its
classical value also drops an \(O(\hbar)\) correction at the order being
studied. No finite field sample is claimed here to certify an otherwise
unrestricted source distribution.

## 3. Actual complete-window coefficients

The nominal supports are the original ones,

\[
 I_1=[1/32,1/16],\qquad I_2=[5/32,3/16].
\]

Their centers are \(3/64\) and \(11/64\). For \(z=(\eta-\ell)/(h-\ell)\),
the actual smooth instrument weight is proportional to

\[
 q(z)=\exp[-1/(4z(1-z))],\quad 0<z<1,
 \qquad \langle f\rangle_j=
 \frac{\int_0^1q(z)f(\ell+(h-\ell)z)\,dz}{\int_0^1q(z)\,dz}.
\]

This is exactly `bump(2*z-1)` from `instrument.py`. The archived
\(30z^2(1-z)^2\) weight and center-point approximation are diagnostics only.

For fixed-radius comparison, \(\eta\) in this definition labels the
reference radius \(a_0(\eta)\). The new apparatus must match the measured
radius to this label and calibrate its Jacobian, rather than assuming that
the perturbed proper-time clock reaches that radius at the old time.
Timing, spatial-curvature, radius, and weight errors belong in the error
budget. The two supports are retained as a design choice; this is an added
radius-trigger/calibration contract.

With row order \([\rho_1,E_1,\rho_2,E_2]\), the complete smooth matrix is

\[
 M\simeq
 \begin{pmatrix}
 .5067236971&1.0135335606& .9905635685\\
 .9955318237&2.0270671213&-3.1918871424\\
 .5915284002&1.1986564499& .7822491962\\
 .9414247778&2.3973128999&-6.2754535643
 \end{pmatrix}.
\]

These rows operate on \((\epsilon,u,v)\) with the same normalization.
The receipt records the full precision and rigorous enclosing intervals.

### Retaining the original calibration: two density windows suffice

For calibrated u, subtract \(u\langle c^{-3}\rangle_j\) from the two
density residuals. The remaining matrix on \((\epsilon,v)\) is

\[
 A_2=
 \begin{pmatrix}
 .5067236971&.9905635685\\
 .5915284002&.7822491962
 \end{pmatrix}.
\]

Its determinant lies in
\([-0.189567268524,-0.189557287905]\), strictly excluding zero.
The epsilon weights are approximately \((-4.1266079071,5.2255310382)\).
Their numerical L1 gain is 9.35213895; the certified upper gain is
**9.352408899**, and the column-normalized condition number is 10.27513.
The receipt supplies outward intervals for the determinant and both weights. The same two nominal
supports therefore suffice to eliminate the curvature nuisance when the
source's total stiff energy is known.

If the u calibration has error at most \(\Delta u\), write
\(w_2=e_1^T A_2^{-1}\) and
\(r=(\langle c^{-3}\rangle_1,\langle c^{-3}\rangle_2)\). Then

\[
 |\widehat\epsilon-\epsilon|
 \le\|w_2\|_1\delta+|w_2r|\Delta u.
\]

The fully certified bound is
\(9.352408899\,\delta+2.081488946\,\Delta u\).
With exact u calibration, a unit-gap fixed midpoint decision requires total
row error below 0.0534621620. These are required error budgets, not achieved
apparatus accuracies. A bounded calibration error does not automatically
require additional contractions;
the desired discrimination precision determines whether the two-reading
bound is sufficient.

### When the stiff calibration is free, two density windows fail

For \(R=M_{[\rho_1,\rho_2]}\), the two nuisance columns are invertible.
Its null direction, normalized to unit nine-mode change, is

\[
 (\delta\epsilon,\delta u,\delta v)
 \simeq (1,-.4805010562,-.0199076074).
\]

Thus two different nearby source/coupling triples give exactly the same two
density averages. The direction can be scaled arbitrarily small to remain
in a regular perturbative family and inside \(\epsilon\ge0\) away from
its boundary. Positivity of the added-state covariance does not remove this
local ambiguity.

As a falsification control, if the true curvature coefficient is changed by
\(v=1\), but the fitting model incorrectly fixes \(v=0\), the two-density
fit creates a false \(\epsilon\) shift of about **50.2321**. This is an
algebraic counterexample, not generated data.

The poor density-only conditioning near the turning point has an analytic
cause:

\[
 \frac{f_\rho}{c^{-3}}=c^2-c^4/2,\qquad
 \left.\frac{d}{dc}(c^2-c^4/2)\right|_{c=1}=0.
\]

The nine-mode and stiff sources have tangent normalized density profiles
there. Their focusing profiles do not have this same tangency.

### A minimal useful relation and a held-out check

Take \(d=(\langle D_E\rangle_1,\langle D_\rho\rangle_2,
\langle D_E\rangle_2)\), and let \(A_M=M_{[1,2,3]}\).
Then the exact projected coefficient is

\[
 \epsilon=w\cdot d,\quad
 w=e_1^T A_M^{-1}
 \simeq(7.4440030655,-4.0151771987,-4.2867478077).
\]

It annihilates both nuisance columns and returns one on the nine-mode
column. The fourth row predicts

\[
 \langle D_\rho\rangle_1=p\cdot d,\qquad
 p\simeq(-.0267370351,.9439408965,-.0265837299).
\]

Thus \(T=\langle D_\rho\rangle_1-p\cdot d\) is a held-out,
coupling-independent residual. A nonzero residual beyond its error interval
rejects this three-parameter source family; it does not identify which
omitted physical effect caused the failure.

When u is genuinely free, within the menu of unprocessed \(\rho_j,E_j\)
averages, three independent scalar functionals are the minimum for fitting
the three free coefficients;
the two declared density averages provably fail. A purposely constructed
single projected readout could encode the same combination, but its
implementation still contains the three calibrated couplings above.

| Geometry design | Column-normalized 2-condition number | Worst-case epsilon error gain |
|---|---:|---:|
| \(E_1,\rho_2,E_2\) | 36.1842 | 15.74593 |
| \(\rho_1,E_1,E_2\) | 35.9533 | 15.98373 |
| \(\rho_1,E_1,\rho_2\) | 621.0620 | 329.23999 |
| \(\rho_1,\rho_2,E_2\) | 1118.0250 | 548.89603 |
| Three density windows, adding \([7/32,1/4]\) | 859.8696 | 576.37618 |

These condition numbers are numerical diagnostics with columns normalized
to unit Euclidean norm. The gains use the declared physical residual units,
so they have a direct worst-case error interpretation. The interval
certificate proves the selected design has rank three and gives rigorous
gain bounds; the displayed extra-density-window comparison is numerical.

The retained-calibration, two-density design is the first option above.
Knowing only the mean \(\bar P\) does not calibrate u when displacement
variance or the regular zero-mode covariance is still unknown.

The density-only rank obstruction is not permanent at all radii. Divide the
density columns by \(c^{-3}\), write
\(z=4/c-3/c^3\), \(y=c^2-c^4/2\), and compute

\[
 z'>0,\qquad z'y''-z''y'
 =40(c^2-3)(c^2-3/4)c^{-4}.
\]

On \(\sqrt3/2<c\le1\), equivalently \(0\le\eta<\pi/12\), the
parametric curve \((z,y)\) has strictly signed curvature. Hence three
distinct radius points are not collinear. The same signed determinant
persists when each row is averaged with a positive weight over three ordered,
disjoint supports in that domain: expand the determinant as a triple
integral. Our comparison third window satisfies that support condition.
The script also checks the corresponding focusing identity
\(z'y''-z''y'=20(21-4c^2)c^{-2}>0\) after using
\(z=4/c-5/c^3,y=c^4\).

## 4. Error statement, including what is not yet known

For exact coefficient integrals, the retained-calibration design has the
two-reading bound stated above, including a separate term for a bounded
u calibration error. For the upgraded three-reading design with errors
\(|e_i|\le\delta_i\), with no independence or probability assumption,

\[
 |\widehat\epsilon-\epsilon|
 \le\sum_i|w_i|\delta_i.
\]

Each \(\delta_i\) must include instrument error, the dynamic-reference
window integral error, matching and weight error, and the finite-coupling
remainder. Repetition alone does not reduce unknown systematic components.
The certified equal-error bound is

\[
 |\widehat\epsilon-\epsilon|<15.748363\,\delta.
\]

Similarly the held-out residual obeys
\(|T|<1.999941\,\delta\) if all four residuals have equal absolute error
bounds. For distinguishing two *predeclared* epsilon values separated by one
with a fixed midpoint threshold, it suffices that the entire error budget
per row is below **0.0317493**. This is a derived requirement, not an achieved
apparatus accuracy, and not a claim that two separately constructed
confidence intervals must be disjoint.

The interval weights in `receipt.json` enclose the exact mathematical
weights. Applying only the rounded displayed weights to measured data
requires an additional coefficient-rounding term. One may instead multiply
the interval weights by the measured intervals directly.

If the actually realized matrix is \(\widehat A+\Delta A\), with
\(\|\Delta A\|_\infty\le\eta\), set
\(K=\|\widehat A^{-1}\|_\infty\) and
\(\widehat\theta=\widehat A^{-1}d\). Provided \(K\eta<1\),

\[
 \|\theta-\widehat\theta\|_\infty
 \le\frac{K}{1-K\eta}
       \left(\delta+\eta\|\widehat\theta\|_\infty\right).
\]

This bounds coefficient perturbations from realized weight/radius errors
without pretending an unknown finite curvature coefficient is zero.
For the chosen nominal matrix, \(K\simeq15.74593\). The bound still needs
an actual calibration of \(\eta\); no such calibration is claimed here.

### Why the geometry contract is additional work

The existing Ramsey/pointer couplings sample local field characteristic
functions. They do not measure \(G_{nn}\), \(R_{nn}\), \(H\), or
spatial curvature. A possible finite geometry measurement route uses a
calibrated geodesic, irrotational congruence. If \(y=\log(V/V_0)\),
\(\theta=\dot y\), and a proper-time weight \(W\) and its first
derivative vanish at the window boundary, Raychaudhuri gives

\[
 \int W R_{nn}\,d\tau
 =-\int \ddot W y\,d\tau
  -\int W(\theta^2/3+\sigma_{ab}\sigma^{ab})\,d\tau.
\]

This is a finite-window expression, not an instantaneous acceleration
oracle. It requires volume, expansion and shear calibration, the
radius-to-proper-time Jacobian for the chosen weight, and accounting for
the measurement apparatus stress. Density requires the corresponding
expansion and spatial-curvature information. The same-radius matching and
subtraction must be performed before forming the residuals.

Focusing and density are related by stress conservation as functions of
radius. Two scalar density averages do not contain the weighted derivative
information supplied by the focusing averages. No statistical independence
of the two measured contractions is assumed in the interval bounds.

No mass, work, backreaction, bandwidth or causal implementation certificate
for this geometry apparatus is supplied here. Consequently this result
advances the observable relation and tells the next apparatus calculation
what accuracy it must attain; it does not yet claim physically realized
discrimination or a unique fundamental theory.

## 5. Reproduction and proof boundary

Run from any working directory:

```sh
/Users/murphyhoops/Documents/ueot-physics-closure-20261111/.physics-venv/bin/python \
  /Users/murphyhoops/Documents/ueot-physics-continuation-20261119/physics/qm/null_source/timelike/evolution/inference/check.py --write --check
```

For read-only validation, omit `--write`. Dependencies are numpy, sympy,
and mpmath. The program performs symbolic conservation and curvature checks,
high-precision coefficient integration, and an independent interval
integration. The latter uses 1024 midpoint cells with an interval bound on
each second derivative and a monotonic bound on the two flat endpoint cells.
The smooth normalization is enclosed independently. Interval cofactor
inversion then gives

\[
 \det A_M\in[-1.262597140,-1.262229596],
\]

strictly excluding zero. Thus the rank result is not an inference from an
SVD tolerance. Binary64 outward rounding is used only to serialize interval
endpoints. Source hashes bind the original reference contract and instrument
definition. Platform-dependent diagnostic floats have a small comparison
tolerance; contracts, hashes, structures, integers and booleans are exact.

The script's negative controls establish that two density windows retain
a nuisance direction, that an artificial alpha-zero fit creates a false
signal, that center values differ from full-window coefficients, and that
geometry alone cannot distinguish the two stiff components. The checks do
not substitute synthetic samples for missing observations.

### Remaining requirements for a finite physical conclusion

1. A certified, same-reference integral of both dynamic \(\rho\) and
   \(E\) over each actual window, including propagated low-mode and
   infinite-tail errors. Point-value certificates are insufficient.
2. A realizable geometry measurement and source preparation contract,
   including finite apparatus stress and the complete error budget above.
3. A finite-order remainder bound or validated nonlinear evolution on the
   specified branch; a large dynamic reference is not automatically a
   small metric perturbation.
4. If separating coherent mean, random displacement variance, and regular
   zero-mode covariance is desired, enough independent source calibrations
   to determine both the mean and the full second moment are required.
   A mean-field measurement alone does not supply them.

These are explicit inputs to the relation, not hidden choices of
renormalization constants or consequences of the set-level Core theorem.
