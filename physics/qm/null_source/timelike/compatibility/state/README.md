# Legal quantum states, changed geometry, and semiclassical initial data

This directory closes a specific interface left by the large dynamic density
result. A quantum state on a chosen background, a solution of the initial
Hamiltonian constraint, and a solution of the coupled semiclassical evolution
are different mathematical objects. The distinctions below are constructive,
not just a list of missing assumptions.

**Completed results**

1. Constant scaling of the entire smooth spacetime and its quantum reference
   gives an exact positive, CCR-preserving Hadamard state, including the full
   propagated zero-mode covariance.
2. The same induced metric and extrinsic curvature do not suffice to move the
   old complete Cauchy kernel to a different future. A counterexample using
   the actual old reference has an exact positive logarithmic divergence in
   the new renormalized energy.
3. A legal repair preserves any finite set of old canonical mode blocks and
   uses the new geometry's own Hadamard reference in the remaining modes.
   Two explicit repairs on the new static background are certified without
   integrating any new mode ODE. They have finite stress for all time.
4. The repaired static states have a certified nonconstant pressure component,
   so they are not exact static semiclassical solutions. This separates
   successful state repair from successful geometry repair.
5. The team's separate scaled, retuned-source construction is a valid
   positive-state construction with an exact initial density constraint and
   a certified small equation defect over a whole interval. That result
   does not require transplanting a kernel to an unknown metric, and does
   not claim an error bound on a nearby exact metric.

Frozen inputs come from commit
`1a90c68b6178968e6b8239fc97a8b26200f8d59d`. No frozen evolution calculation,
Core, or manuscript file is changed.

## 1. Scope and source contracts

The field is the same four-dimensional, real, massless, minimally coupled
scalar. The smooth auxiliary closed-S3 preparation geometry is the archived
`instrument.state_scale`; its physical homogeneous part has

\[
 a(\eta)^2=3\cos(2\eta),\quad
 p_k=a^2u'_k,\quad \omega_k=\sqrt{k^2-1},\quad k\ge2.
\]

The k=1 mode is a regular Gaussian, not an oscillator ground state.
The spectrum has degeneracy k-squared. The numeric static repair example
uses the same Anderson--Eaker prescription, physical mu=1, and no extra
finite curvature terms.

The global Hadamard statements here apply to the **smooth auxiliary
spacetimes**. For the physical finite ball they apply only after restriction
to its smooth, isometric homogeneous causal region. The original exterior
quintic taper is only C2. It does not by itself supply a global smooth
background or a global Hadamard coherent displacement. A smooth exterior,
its quantum state, and its renormalized stress need a separate completion;
changing the taper to a C-infinity one also requires rechecking the old
exact ADM and matching numbers.

## 2. Exact homothetic transport theorem

Let (M,g) be a smooth globally hyperbolic four-dimensional spacetime, and
let W be the two-point function of a positive Hadamard state of the massless
minimal field. For a positive constant lambda, define

\[
 g_\lambda=\lambda^2g,\qquad
 W_\lambda=\lambda^{-2}W.
\]

**Then W_lambda is a positive Hadamard two-point function for g_lambda.**

For a constant metric scaling, the wave operator scales as
\(P_\lambda=\lambda^{-2}P\). The invariant delta kernel scales as
\(\delta_\lambda=\lambda^{-4}\delta\), so the causal propagator is
\(E_\lambda=\lambda^{-2}E\). Hence W_lambda is a bisolution and has
antisymmetric part i E_lambda. Positivity is unchanged by a positive
multiplicative factor and the positive volume rescaling. Constant scaling
does not change the null cones, null geodesics as unparametrized curves, or
the positive-frequency wavefront relation. The Hadamard condition is
therefore preserved.

In the canonical closed-FLRW coordinates this theorem gives

\[
 u_{k,\lambda}=u_k/\lambda,\qquad
 p_{k,\lambda}=\lambda p_k,\qquad
 S_\lambda=\operatorname{diag}(\lambda^{-1},\lambda).
\]

The matrix S_lambda is symplectic. Every canonical covariance transforms as
\(V_\lambda=S_\lambda V S_\lambda^T\); its determinant and uncertainty
inequality are preserved. This is an exact statement about the whole
geometry and state, not an approximation using a finite list of jets.

### The zero mode at the physical initial surface

The diagonal covariance (1/6,3/2) belongs to the preparation seed. At the
physical surface eta=0, let

\[
 J_0=\int_{-1/8}^{0}\frac{d\eta}{a_s(\eta)^2}.
\]

The full original Gaussian covariance there is

\[
 V_{\Sigma_0}=
 \begin{pmatrix}
 1/6+(3/2)J_0^2&(3/2)J_0\\
 (3/2)J_0&3/2
 \end{pmatrix},\qquad \det V_{\Sigma_0}=1/4.
\]

Its off-diagonal entry must be retained. Scaling multiplies Vqq by
lambda^-2, Vpp by lambda^2, and leaves Vqp unchanged. The stress depends
only on the conserved Vpp for this homogeneous minimal zero mode, so the
previous stress certificates did not need a numerical value of J0.
The new repair keeps the exact old zero-mode Cauchy block, including J0;
it does not reset the covariance to a diagonal matrix.

### Scaling the quantum reference does not fix the coherent source contract

For a homogeneous coherent displacement with momentum P and full second
moment M2=E[P^2], the mean stiff stress is M2/(2a^6). The old mixed family
has M2=27; its squared mean alone is 27/4. On g_lambda, distinct choices are:

| Contract | Classical displacement | New M2 |
|---|---|---:|
| Fixed source momentum distribution | phi_lambda=phi/lambda^2 | 27 |
| Transport the entire field state naturally | phi_lambda=phi/lambda | 27 lambda^2 |
| Classical Einstein homothety | phi_lambda=phi | 27 lambda^4 |
| Retune a positive total source moment | explicitly rescale the displacement distribution | separately specified |

The second row agrees with the canonical field transport; the third agrees
with the scaling of the classical Einstein tensor for fixed Newton
coupling. They are different contracts. The reference W_lambda can be
combined with any explicitly specified positive coherent-displacement
mixture whose second moment is finite. The added two-point term is smooth
on the smooth homogeneous region.

## 3. An exact obstruction to a same-h,K kernel transplant

Compare two independent smooth spacetimes:

- The original prepared background, which near eta=0 has
  a_old^2=3 cos(2 eta).
- The static background a_static^2=3.

Their induced spatial metric and extrinsic curvature at eta=0 agree.
In conformal notation,

\[
 a_{\rm old}(0)=a_{\rm static}(0)=\sqrt3,\qquad
 a'_{\rm old}(0)=a'_{\rm static}(0)=0.
\]

Their second normal metric derivatives do not agree:
\(a''_{\rm old}/a=-2\), while \(a''_{\rm static}/a=0\).
There is no nonsmooth spacetime join in this example.

Transport the **entire old canonical Cauchy kernel** to the static
spacetime and propagate it by the new Klein--Gordon equation. Positivity
and CCR are preserved by this Cauchy evolution. Hadamard regularity is not.

To see the failure directly in the renormalized stress, use the same
locally covariant prescription on both spacetimes. Write

\[
 h=a'/a,\quad q=-1-a''/a,\qquad
 d_k=k+\frac{E_1}{k}+\frac{E_3}{k^3},
\]
\[
 E_1=(h^2-1)/2,\qquad
 E_3=\frac{q^2-2(h^2-1)q+2h q'}8.
\]

At eta=0, h=0 in both metrics; q_old=1 and q_static=-1. Thus

\[
 E_{1,\rm old}=E_{1,\rm static}=-1/2,\qquad
 E_{3,\rm old}=3/8,\quad E_{3,\rm static}=-1/8.
\]

The bare energy of every mode at that surface is identical because the
canonical kernel, a, and a' are identical. With complete k-squared
degeneracy, the subtraction difference is exactly

\[
 k^2(d_{k,\rm old}-d_{k,\rm static})=\frac1{2k}.
\]

Consequently the two truncated renormalized densities satisfy

\[
 \rho_{\rm static,N}
 =\rho_{\rm old,N}
  +\frac{H_N}{72\pi^2}
  +\rho_{\rm an,static}-\rho_{\rm an,old},
 \qquad H_N=\sum_{k=1}^N\frac1k.
\]

The old renormalized sum converges. Both local analytic additions are finite.
Since \(H_N\ge\log(N+1)\), the transplanted state's new renormalized
density diverges to positive infinity. Any fixed finite curvature
counterterm changes only the finite offset and cannot remove this
cutoff-dependent logarithm.

This is a statement about the renormalized density itself; it does not
infer stress divergence just from a particle-number estimate. It applies
to the actual archived reference. The regular zero mode or any other
finite-rank change cannot cancel the divergent harmonic tail.

**Therefore an induced metric and extrinsic curvature alone do not
guarantee that a complete old Hadamard kernel is admissible for a new smooth
future.** This counterexample does not contradict constant homothety:
there the whole operator, metric jets, and Cauchy covariance are transported
together.

## 4. A constructive repair preserving finite quantum information

Here is a useful exact replacement theorem for the homogeneous closed-FLRW
case.

Choose a new smooth, globally hyperbolic FLRW background and a homogeneous
Hadamard reference state on it. Choose a finite K. For every complete
degeneracy shell k<=K, use specified positive canonical Cauchy blocks from
the old state; for k>K use the new reference blocks. Include a legitimate
regular zero-mode block. Evolve every block with the **new** field equation.

The resulting block sum is positive and has the correct CCR because every
canonical block does. It differs from the new Hadamard reference by a
finite sum of smooth mode bisolutions, so it is Hadamard. The difference
need not itself be positive; the complete replacement state is positive.
Finite low-mode canonical data are preserved exactly. The old entire kernel
is deliberately not preserved.

This theorem supplies a legal state for every specified new background in
this class for which the reference has been supplied. It does not choose a
self-consistent metric. A simpler sufficient condition for preserving a
whole old kernel is that both smooth metrics agree on a spacetime
neighborhood of the Cauchy surface; Hadamard propagation then applies after
the metric departs from that neighborhood.

### Explicit repair on the new static background

Use the exact old modes through K=64 or 256, with the old zero-mode block.
For every larger mode use the new static vacuum of frequency
\(\omega_k=\sqrt{k^2-1}\). The exact old modes are specified by the frozen
preparation ODE. Their certified intervals are used for arithmetic;
rounded numerical centers are not substituted as exact CCR data.

Let rho_s,p_s be the certified new static reference stress, including its
regular zero mode. The repaired initial stress is

\[
 \rho_K=\rho_s+
 \frac1{36\pi^2}\sum_{k=2}^{K}k^2(e_k-\omega_k),
\]
\[
 p_K(0)=p_s+
 \frac1{36\pi^2}\sum_{k=2}^{K}k^2(s_k-\omega_k/3).
\]

The infinite static vacuum tail is included by the positive binomial
remainder bound. No new ODE or unbounded unknown tail is introduced.

| Preserved shells | Constant density rho_K | Pressure at eta=0 |
|---|---:|---:|
| 2..64 | [0.669108086608, 0.669108086610] | [6.83193963691868, 6.83193963691876] |
| 2..256 | [1.52094899135739, 1.52104740496880] | [66.4344600304011, 66.4345584440126] |

The table uses conservative rounded endpoints. Exact rational endpoints
and global-in-time pressure enclosures are in `receipt.json`.

For each pure nonzero mode on a static background, its energy is constant.
Writing X=sqrt(omega)*a*u and Y=p/(sqrt(omega)*a), its pressure has mean e/3
and oscillation amplitude

\[
 \frac23\sqrt{e^2-\omega^2}.
\]

The receipt bounds the sum of all finitely many amplitudes and adds the
static reference pressure. This proves finite stress for the entire static
field evolution, not only at the initial instant.

### Legal state repair still does not solve static semiclassical evolution

For both repairs the k=2 pressure term has conformal-time frequency
2 sqrt(3) (proper-time frequency 2 at static a=sqrt(3)) and a strict amplitude lower bound

\[
 A_2>2.56378\times10^{-5}.
\]

All other k have different frequencies. Thus this finite pressure sum is
not constant on any open time interval. A static Einstein tensor, static
local curvature counterterms, and a homogeneous classical source with
constant momentum have constant pressure contributions. They cannot cancel
this unique frequency identically. These repaired states therefore do not
solve the exact static semiclassical equation with those ingredients,
even if a single initial density constraint were separately tuned.

This is a concrete boundary on the repair: it completes positive Hadamard
state construction and finite stress, while explicitly falsifying an
unjustified inference to a self-consistent static future.

## 5. What the scaled, retuned-source construction does complete

The team's primary positive continuation retains the entire known
homothetic metric g_lambda and its exact transported Hadamard reference.
Let Q_rho(eta),Q_p(eta) include the fixed-mu scaling anomaly and any fixed
declared finite curvature contribution. Define Q0=Q_rho(0) and

\[
 M_{2,\lambda}=27\lambda^4-54\lambda^2Q_0.
\]

If this moment is positive, a positive rescaling of the original coherent
displacement distribution realizes it. Its field amplitude squared relative
to the classical homothety is \(1-2Q_0/\lambda^2\). With the same exact
Q0 used in both places, the initial density constraint vanishes exactly,
and homogeneity makes the momentum constraint zero.

For c=cos(2 eta), both stress component defects are exactly

\[
 D_\rho=\lambda^{-4}(Q_\rho(\eta)-Q_0c^{-3}),\qquad
 D_p=\lambda^{-4}(Q_p(\eta)-Q_0c^{-3}).
\]

The quantum effective tensor is conserved, and the subtracted c^-3 term is
a conserved stiff source. Hence the defect is conserved on the specified
metric. The geometric required components are
\(\rho_{\rm geom}=p_{\rm geom}=1/(2\lambda^2c^3)\), so their relative
defects are

\[
 \frac{|D_{\rho,p}|}{1/(2\lambda^2c^3)}
 =\frac{2c^3}{\lambda^2}|Q_{\rho,p}(\eta)-Q_0c^{-3}|.
\]

A independently inspected and replayed
`../scaling/check.py --check`. Its directed bounds certify, for lambda=8192
and eta in [0,3/16],

\[
 \frac{|D_\rho|}{\rho_{\rm geom}}<0.000286660,\qquad
 \frac{|D_p|}{p_{\rm geom}}<0.008066751.
\]

This is a legal quantum state on a fully specified smooth background, a
positive adjusted source, exact correlated initial density/momentum
constraints, and a uniformly controlled field-equation defect. It is not
the fixed-M2 contract and not automatic transport of the entire old field
state. Using an independently chosen midpoint M2 gives a finite initial
residual instead; the constraints certificate records that separate
implementable rational instance.

Neither a small equation defect nor an initial constraint root proves a
nearby exact metric. Such a conclusion requires a coupled existence and
stability estimate controlling geometry and state on the declared interval,
including higher-derivative branches. No such estimate is asserted here.

### A small mean equation defect does not suppress the original source noise

The principal source can retain the original bounded A distribution, not
merely its second moment: take \(Y=s/2+X\), \(s=\pm1\), with independent
equiprobable \(X=\pm\sqrt3/2\), and realize the adjusted moment by scaling
the deterministic profile \(f\). Each displaced branch is a coherent
displacement of the same centered Hadamard reference, so this finite
positive mixture is itself a legitimate Hadamard state.

For a real smooth, compactly supported spacetime smearing of the stress,
write the resulting self-adjoint observable as A. Let \(A_f\) be its
classical stress value for profile f, and \(Q_{\rm ref}\) its expectation in
the centered reference. The conditional expectation is

\[
 \mathbb E[A\mid Y]=Q_{\rm ref}+Y^2A_f .
\]

The positive mixture obeys the total-variance identity, hence

\[
 \operatorname{Var}(A)
 \geq\operatorname{Var}(Y^2)\,A_f^2 .
\]

For any symmetric X with \(\mathbb E X^2=3/4\) and finite fourth moment,

\[
 \mathbb EY^2=1,\qquad
 \operatorname{Var}(Y^2)=\mathbb EX^4+\frac3{16}\geq\frac34 .
\]

The last inequality follows from
\(\mathbb E(X^2-3/4)^2\geq0\), and the bounded A candidate attains equality.
Thus, when \(A_f\ne0\), the relative variance compared with the **classical
displacement source's mean contribution squared** is at least 3/4.
This is not an unconditional bound relative to the squared total mean
\((Q_{\rm ref}+A_f)^2\). When a fourth moment or smeared stress variance is
infinite, finite-variance conclusions do not apply; the obstruction is
stronger, not removed.

Homothety and source retuning rescale \(A_f\) and do not reduce this ratio.
The certified small defect of the mean semiclassical equation consequently
does not certify small source stress fluctuations. The reference state's
own fluctuations and the conditional fluctuations are additional
nonnegative terms.

For the specific retuned construction, more can be certified. With a
nonzero nonnegative smooth density smearing supported in the certified
inner domain, \(A_f=(1-\delta)A_{\rm geom}\), where
\(\delta=2Q_0/\lambda^2\). The uniform relative density defect
\(\epsilon_\rho<1\) implies
\(|\mathbb EA|\leq(1+\epsilon_\rho)A_{\rm geom}\).
Consequently

\[
 \frac{\operatorname{Var}(A)}{(\mathbb EA)^2}
 \geq\frac34\frac{(1-\delta)^2}{(1+\epsilon_\rho)^2}.
\]

The independent aggregate certificate ../review.py gives a lower bound
greater than 0.7495 at lambda=8192, alpha=0, both for the exact correlated
source and its separately certified rational approximation. This statement
uses the bounded original A mixture and the geometric mean comparison;
it still does not infer a metric fluctuation bound.
 A deterministic displacement with \(Y=s\) has the same
second moment but a different first mean, and is a different complete
source and readout contract.

## 6. Metric jets and the actual scope of existence results

The relevant original sources were checked directly, including published
versions where available.

| Source | Established result or stated status | Consequence for this project |
|---|---|---|
| Juarez-Aubry, Kay, Miramontes, Sudarsky (2024), JCAP 10, 002 | The initial renormalized stress can be computed from Cauchy two-point data and geometric data including the first four transverse metric derivatives | h and K alone do not provide the subtraction data; four-jet information for stress is not a theorem that four jets suffice for the full Hadamard condition |
| Same authors, arXiv:2205.11671, section 3 | Surface-Hadamard semiclassical data involve equations and a hierarchy of compatibility conditions; full well-posedness and the physical-branch reduction are presented as conjectures | A Hadamard state on a chosen background plus one constraint root must not be renamed a proved surface-Hadamard solution of the coupled theory |
| Meda, Pinamonti, Siemssen (2021), Theorem 5.9 and Remark 5.2 | Local existence for flat cosmology, a massive field, positive initial mode frequency squared, and a sufficiently regular compatible chosen state; the stated result first gives a C3 mild solution | It does not directly authorize our closed-S3, massless, fixed-full-kernel candidate or a smooth full-Hadamard future |
| Gottschalk, Siemssen (2021), Theorems 5.7/5.11 and section 5.6 | Smooth Hadamard local solutions and a smooth switching construction of compatible data in flat FLRW, with specified moment-space hypotheses | It supplies a constructive strategy; extension to non-flat cosmology is explicitly left as requiring further work in their outlook |
| Meda (2026), author review | Reviews the flat massive construction and the inverse problem for the derivative-losing operator | It does not remove the closed-space or fixed-state hypothesis gap above |

The distinction is precise. In a fourth-order formulation one ordinarily
supplies metric jets through order three; the stress depends on order four,
which must be determined consistently with the equations and state
regularity. In a reduced-order or physical-branch formulation one must
instead justify the reduction and its error. A prescribed full homothetic
jet already makes the transported state legal on that background, but it
does not force those jets to satisfy the full semiclassical field equations.

The sources checked here do not establish the missing theorem for this
particular closed, massless preparation. This is not a claim that no
closed-space theorem exists anywhere. The concrete usable exits are the
exact state maps, the finite-mode repair, and the controlled-defect
construction above; a nearby exact self-consistent future remains a
separate mathematical task.

### Primary references

- Anderson and Eaker, equations (9)--(12), for the consistent mode
  subtraction and local additions:
  https://arxiv.org/pdf/gr-qc/9906055
- Juarez-Aubry, Kay, Miramontes, Sudarsky, *The Hadamard condition on a
  Cauchy surface and the renormalized stress-energy tensor*:
  https://arxiv.org/pdf/2406.01498
- The same authors, *On the initial value problem for semiclassical
  gravity without and with quantum state collapses*:
  https://arxiv.org/pdf/2205.11671
- Meda, Pinamonti, Siemssen, published theorem and regularity caveat:
  https://doi.org/10.1007/s00023-021-01067-8
- Gottschalk and Siemssen, published flat-FLRW existence and construction:
  https://doi.org/10.1007/s00023-021-01060-1
- Meda, 2026 author review of those results:
  https://doi.org/10.1007/s10773-026-06339-9
- Junker and Schrohe, finite adiabatic order versus Hadamard regularity:
  https://arxiv.org/pdf/math-ph/0109010

## 7. Reproduction and safeguards

```sh
/Users/murphyhoops/Documents/ueot-physics-closure-20261111/.physics-venv/bin/python -B \
  /Users/murphyhoops/Documents/ueot-physics-continuation-20261119/physics/qm/null_source/timelike/compatibility/state/check.py --check
```

Use `--write` separately only to regenerate this directory's receipt.
The script checks the symplectic map, full zero-mode covariance determinant,
the exact logarithmic subtraction identity, the tuned-source identities,
the original mixture source variance bound,
the static binomial tail, and the two finite-rank repaired states. It
verifies hashes of the frozen mode receipts and their source files, uses
70-digit directed interval arithmetic, and serializes exact binary endpoints
as rational numbers. Assertions are mandatory. No new mode integration,
synthetic observations, Core changes, or edits to the frozen evolution
results are performed.
