# C — Joint calibration and a nominal finite predictor

Research baseline: `cb17211653fde30aa50e0e9848798a6a5b3b3f12`, science
v31.12 / Kernel 1.12 / book 3.9. Author: native research agent C, 2026-11-12 UTC.
This draft supplies the calibration part of **P-ROB-04** and the complete
certificate interface for **P-ROB-05**. Root owns the public integration.
Core and the existing formalized declarations remain read-only.

## 1. Result and exact scope

The previous controlled simultaneous-dynamics bridge can be made into an
actual **data-selected nominal prediction**, without supplying the unknown true
pulse parameter to a finite simulator. A binary momentum calibration identifies
the signed pulse area within the declared ideal preparation/readout model.
Its finite-sample confidence set, a legal fixed visible-history policy and a
source-derived Galerkin bound give one complete CQ error certificate.

At the frozen synthetic execution, the observed counts give

\[
 \widehat q=0.5006,\qquad C_q=[0.4906,0.5106],\qquad
 \widehat p=0.547267,\qquad \widehat x=2969/50000=0.05938.
\]

The independently enclosed parameter interval and displacement are

\[
 C_x\subseteq[0.0568560627871193,\;0.0619048193329946],\qquad
 \Delta_x\le0.0025248193329946.
\]

Decimal endpoints here are explanatory rounded enclosures; the executable
certificate stores the exact outward rational endpoints. The upper bound for
the exact finite nominal predictor is

\[
 \varepsilon_{\rm finite}
 \le0.0419301587941104<0.05.
\]

An additional numerical allowance of `1e-8`, **if independently established
for the particular returned numerical output**, leaves an upper bound below
`0.0419301687941104`. C's calibration analysis does not establish that numerical
allowance. The uniform theorem covers all input states in the stated mean-G
and finite-reference domain; a separate numerical output receipt may cover
only a specified input. These scopes must not be conflated.

These are conditional mathematical and synthetic pipeline results. No device
calibration, external raw measurement, or project hardware measurement was
obtained. The standard complex quantum structure, ideal source/filter/gates,
fixed shared parameter, iid calibration trials and ideal quadrature tester
remain explicit physical inputs.

## 2. Shared model, output and dependency contract

Use the public `SHARED_MODEL.md` and `frozen_model.json` as the authority. The
local `FROZEN_CERTIFICATE_PLAN.json` specifies the reproducible statistical
implementation and synthetic streams. It is a supplement for root to integrate,
not a second scientific state entry.

The system is a complex qubit and a Fock oscillator, with
`G=n+P_e`; an arbitrary finite positive-dimensional reference is untouched and
may be initially entangled. The force gate and phase gate are

\[
 U_x=e^{-ix\sigma_x(a+a^\dagger)},\qquad
 V_0=e^{-i\pi P_e/3}.
\]

The source events are `sqrt(s(1-q)) V0`, `sqrt(sq) Ux` and
`sqrt(1-s) I`, with the same relation `s=1-q/2` everywhere. Two source slots
stop at `f`. Keep all seven words `f,0f,1f,00,01,10,11`, the stopping label and
the terminal SR state. The last four words are accepted. The acceptance effect
is derived from these events as `s² I`, so the specified conditional target
`T_infinity(q,x)` is a CPTP channel. Raw-source failure masses are not replaced
by the accepted distribution in a claim about the raw source.

The actual compiler uses those same physical gates. Its frozen legal policy is
`w1(empty)=1/2`, `w1(0)=312/625`, `w1(1)=313/625`; therefore

\[
 Q_{00}=Q_{11}=313/1250,\qquad Q_{01}=Q_{10}=312/1250,
 \qquad \sum_r Q_r\,\#1(r)=1.
\]

Every observation fibre uses a single weight. The controller reads only past
visible labels. The pre-existing full-labelled error `1/50` is uniform on
`q in [12/25,13/25]`; this iteration does not reinterpret it as minimax optimal
on every smaller data-derived interval.

The input satisfies `Tr(G rho_S)<=1`. The physical filter is `Pi_4095`. Its
failure output is the distinct `prep_fail` block, with only S reset to vacuum
and with the **actual unnormalized failure-conditioned R marginal** preserved.
The common output alphabet contains this block as well as the seven source
words, including the appropriate zero-mass blocks. All distances mean one half
of the full trace norm on this complete CQ output.

The finite predictor uses the true compressed generator `P_K H_xhat P_K`,
`K=4175=4095+2*40`. It is not assumed to be a physically available gate. The
comparison passes from the physical actual gate to the mathematical nominal
infinite gate, then to its exact Galerkin predictor. This order is essential.

Dependency categories are separate from proof/verification categories:

| Category | Inputs or consequences in this claim |
| --- | --- |
| C | Read-only existing Core mathematics; no complex-sector choice is derived here. |
| B | Normal CP instruments, complete record composition, spectral filter and common output embeddings. |
| S | No new independent sector-selection principle. |
| P | Complex Fock quantum model, Born probabilities, the selected source, phase gate and driven force. |
| E | Exact common pulse area, ideal reset/filter/calibration readout, bounded input mean, finite tree and reference, fixed iid calibration design. |
| O | Conditional complete-CQ error bound; source and two-dose tester probabilities; explicit tester rejection rule. |
| X | Hardware membership, extra detector/gate errors and more general dynamics remain open until independently constrained. |

## 3. P-ROB-04: signed calibration, coverage and deployment quantifiers

### 3.1 What the original flags cannot identify

All source branch probabilities are scalar coefficients multiplying unitary
channels. Consequently their one-slot and complete seven-word probabilities
depend on q and not x. For a fixed q, any two different pulse areas produce the
same entire visible flag law. Quantum terminal states can differ. Thus even
unlimited flag counts alone cannot identify x. No estimate of the force is
inferred from an original-source success or failure frequency.

### 3.2 A finite binary tester for the signed force

Independently prepare the probe in the +1 eigenstate of `sigma_x` and the
oscillator in vacuum, apply the **same one-slot physical pulse** as in the
source/compiler, and measure the two effects `P<=0` and `P>0`, where

\[
 P=(a-a^\dagger)/(i\sqrt2).
\]

The oscillator output is the coherent state `|-ix>`, so P has mean
`-sqrt(2)x` and variance `1/2`. Hence

\[
 p(x)=\Pr(P\le0)=\Phi(2x)
 =\frac12+\sqrt{\frac2\pi}\int_0^x e^{-2t^2}\,dt.
\]

The derivative is strictly positive. This tester therefore identifies the
signed x in the declared ideal model. The tester has two outcomes, although
the underlying oscillator observable is continuous. No infinite continuum of
observed bins is silently assumed. The standard Gaussian/error-function
identity is also documented by NIST DLMF §7.2,
<https://dlmf.nist.gov/7.2>; the exact formula and the finite arithmetic bounds
needed here are given explicitly above and below.

This conclusion requires the preparation, zero threshold, scale and pulse
connection. For example, let observed momentum equal physical momentum plus
an unknown additive bias b. The one-dose probability becomes
`Phi(2x-sqrt(2)b)`. The transformation
`(x,b)->(x+c,b+sqrt(2)c)` leaves that one-dose response unchanged.
Thus single-dose calibration alone is nonidentifying if b is unrestricted.

This obstruction is **access-dependent**. With the same fixed b and two
consecutive same pulses, the second response is `Phi(4x-sqrt(2)b)`.
Writing the inverse-normal arguments as z1 and z2 gives
`x=(z2-z1)/2` and `b=(z2-2z1)/sqrt(2)`. Thus the two settings jointly identify
fixed x and fixed b in the ideal two-parameter family. The present analyzer
assumes b=0 and holds out the second setting; it does not fit b from it.
Unrestricted setting-dependent biases `b_k` would instead retain the symmetry
`(x,b_k)->(x+c,b_k+sqrt(2) k c)` at every k-dose binary tester. These are distinct
nuisance models, not one universal impossibility claim.

### 3.3 Fixed sample sizes and the joint confidence set

The frozen calibration sizes are `n_q=120000` original one-slot flags and
`n_x=1000000` one-dose binary momentum outcomes. Count every original `f` and
every binary outcome. Unknown failure/leakage labels or missing trials cause
an insufficient ideal-model certificate; they are not deleted.

Set `qhat=2 n_f/n_q`, `phat=n_minus/n_x`,

\[
 C_q=[\widehat q-0.01,\widehat q+0.01]\cap[0,1],\qquad
 C_p=[\widehat p-0.002,\widehat p+0.002]\cap[0,1],
 \qquad C_x=p^{-1}(C_p).
\]

The s coordinate is always `s(q)=1-q/2`, not an independently varying box
coordinate. All source instruments, accepted targets and cost probabilities
use this same q. Likewise, calibration, force gates, finite generator and
two-dose forecast use the same x. The product `C_q times C_x` is a transparent
joint confidence region obtained by a union bound, without assuming statistical
independence between the two confidence events.

For completeness, the concentration bound follows directly for a Bernoulli
variable Y of mean p. Let
`psi(t)=log E exp[t(Y-p)]`. Then `psi(0)=psi'(0)=0` and
`psi''(t)=p_t(1-p_t)<=1/4`, so `psi(t)<=t²/8`. Independence within a fixed
n-shot stream gives the product moment bound. Chernoff optimization at
`t=4 epsilon` yields each upper/lower tail `exp(-2n epsilon²)`.
Applied to the failure frequency and the momentum frequency,

\[
 \Pr(q\notin C_q)\le2e^{-6},\qquad
 \Pr(x\notin C_x)\le2e^{-8},\qquad
 \Pr((q,x)\notin C)\le2e^{-6}+2e^{-8}<0.01.
\]

This is a fixed-sample statement uniform in the allowed parameters. It implies
that the probability of emitting an invalid certificate because calibration
missed the true parameter is at most this same bound. It does **not** establish
99% coverage conditional on the event that the program admitted this particular
dataset. Repeatedly sampling until admission or using optional stopping is not
covered by this protocol.

The entire untrimmed data-derived C must lie inside the frozen design
`q in [12/25,13/25]`, `|x|<=1/10`; the nominal representative must lie there too.
Otherwise the analyzer returns insufficient certification. It never cuts C
down to the design merely to force a precision pass. Inconsistent physical
probabilities or a failed certified inversion also produce no certificate.

The outer inverse is computed with rational Gaussian integrals and bisection.
The independent checker uses a different pi identity and a standard-normal
integration variable. The deterministic nominal rule rounds the midpoint of a
certified inverse bracket for phat to a `1e-5` rational grid. Its actual outer
displacement is

\[
 \Delta_x=\max\{|x_{\rm lo}-\widehat x|,|x_{\rm hi}-\widehat x|\}.
\]

Thus both inversion enclosure and grid displacement are retained. The
computational inverse bracket `[-1/4,1/4]` is not a hidden physical prior; if it
cannot enclose the requested probability, the implementation returns no
certificate.

The deployment statement is one legal policy and one data-derived nominal
value for every theta in C. In fact the particular physical policy Q is fixed
before calibration, and therefore satisfies the stronger requirement of
not varying across admitted datasets. The simulator uses xhat; it receives
neither hidden physical x nor synthetic generating truth. qhat is not silently
plugged into Q: q calibration establishes membership in the robust q domain,
whose full `1/50` path-law allowance is retained.

## 4. The nominal parameter error, including its form domain

Let `X=a+a†`. On the oscillator form domain,

\[
 X^2\le4n+2I\le4G+2I.
\]

One way to see the first inequality is to combine
`||(a+a†)psi||<=||a psi||+||a† psi||` with
`2 sqrt(n(n+1))<=2n+1` at the level of the two squared norms.
The expectation `Tr X² rho` denotes the positive quadratic form; finite mean n
places a purification in D(X), and D(X²) is not required.

The exact force commutes strongly with X's spectral projections, and the phase
acts on the probe only. Every true or nominal **infinite** prefix preserves
`||X psi||²`. Spectral calculus gives

\[
 \|(U_x-U_y)\psi\|\le|x-y|\,\|X\psi\|.
\]

Telescope each word using exact nominal prefixes and exact true unitary
suffixes. A word with k force calls has joint-state trace distance at most
`k |x-y| sqrt(4E+2)` on mean-G budget E, including arbitrary finite references.
The output's record blocks are orthogonal and share the same Q law, whose mean
k is one. Therefore

\[
 D(C_\infty(x)(\rho),C_\infty(\widehat x)(\rho))
 \le\sqrt6\,\Delta_x
\]

on the supported passing input in the present E<=1 model. Retaining its mass
would sharpen the estimate; bounding that mass by one is conservative.

The physical low-G projection does preserve the required mean bound **on its
pass branch**. Since G commutes with the spectral filter, the normalized
low-spectrum conditional mean is at most the high-spectrum conditional mean,
and thus at most the original mean. Markov also gives positive passing mass,
`s_N>=1-1/4096`. These facts concern this exact spectral filter, not arbitrary
postselection.

The finite Galerkin force need not conserve the full X² form. A's K=1 witness
from initial `|e,0>` gives `1+2 sin²x` under the finite evolution, whereas the
exact model preserves one. Thus the preceding parameter proof cannot be
applied directly to finite prefixes. The certified triangle compares exact
true and exact nominal processes first, then separately approximates the
nominal process by the compressed dynamics.

## 5. P-ROB-05 interface: the complete error budget

Let `e=1/(N+1)=1/4096` and

\[
 F(e)=\frac{\sqrt{4e-3e^2}+e}{2}.
\]

This inherited sharp physical-preparation allowance includes the probability
and disturbance of the explicit failed-filter branch. It is not only the
distance to a free normalized projection. Here the specified accepted source
target is CPTP because its effect is `s²I`; applying that channel contracts the
preparation error. There is no omitted state-dependent posterior amplification
in this particular comparison. General posterior conditioning retains its
separate positive-success and sharp amplification contract.

For `j=L+1`, A/B's source-derived finite Duhamel proof gives

\[
 d_{N,L}(z)=\min\!\left(1,
 \frac{2z^{L+1}}{(L+1)!}\prod_{r=1}^{L+1}\sqrt{N+2r-1}\right).
\]

This compares the actual infinite propagator with `exp(-i P_K H P_K)` on the
same low-support input. It is not a state-tail bound and has no unproved
infinite Dyson-series substitution. The square of its uncapped argument is an
exact rational for rational z, allowing an integer square-root enclosure.

For the complete compiler, the nominal Galerkin error is

\[
 \varepsilon_G(\widehat x)
 \le\frac{624}{1250}d_{4095,40}(|\widehat x|)
    +\frac{313}{1250}d_{4095,40}(2|\widehat x|).
\]

The zero-drive word contributes zero; the other coefficients are their actual
complete record probabilities. Filtering fails identically in both compared
predictors, so its block contributes no additional dynamics/parameter error.

Consequently, for every theta in the admitted data-derived region and every
joint input in the stated mean/reference domain,

\[
 \boxed{D\!\left(T_\infty(q,x)(\rho),C_K(\widehat x)(\rho)\right)
 \le F(e)+\frac1{50}+\sqrt6\,\Delta_x+
       \varepsilon_G(\widehat x).}
\]

Every term is attached to the same complete output and same original source.
The actual physical compiler at the unknown true x needs only the first two
terms for its target error; the last two quantify predictive replacement by a
data-selected finite model. The physical gate is never asked to know xhat or
implement the finite cutoff by assumption.

The actual synthetic certificate has the following explanatory values:

| Term | Independently enclosed value |
| --- | --- |
| Physical filtering, including failure | approximately 0.0157456397355358 |
| Fixed legal robust path law | exactly 0.02 |
| Unknown true to data-selected nominal parameter | approximately 0.00618451905855074 |
| Nominal exact Galerkin dynamics | approximately 2.37940449846e-14 |
| Complete exact finite predictor total | below 0.0419301587941104 |
| Conditional total with separately certified 1e-8 arithmetic | below 0.0419301687941104 |

The entire design interval, without using this narrower nominal value, has
Galerkin bound below `0.000045417199841841`. This uniform truncation result is
kept separately from the data-selected nominal total.

Changing only the drive probability half-width to 0.01 in a declared negative
control gives a sufficient upper bound approximately `0.0667116625571`, above
the unchanged 0.05 precision. The analyzer returns `INSUFFICIENT_BOUND`. This
is a failure of the sufficient precision certificate, not a proof that the
physical task is impossible.

## 6. Disjoint held-out settings and failure controls

The final synthetic holdout protocol was frozen during software development
before generating its final streams. It is not represented as experimental
preregistration. The earlier one-dose repeat was replaced by a two-dose
setting; calibration seeds, sample sizes, half-widths and nominal rule were
not tuned in response to the final holdout.

Three independent logical streams have 50000 trials each: complete raw-source
words, complete compiler words on the declared vacuum input, and the binary
momentum tester after **two consecutive same force gates with no intervening
phase**. The first two include all seven word cells, including zero predicted
failure cells for the compiler. Physical `prep_fail` has probability zero on
this specified vacuum holdout input; unexpected loss/leakage is not silently
merged into an accepted record. These limited holdouts do not measure arbitrary
terminal quantum states or references.

The two-dose forecast is

\[
 p_2(x)=\Phi(4x),\qquad p_2(C_x)=[\Phi(4x_{\rm lo}),\Phi(4x_{\rm hi})].
\]

It uses only the one-dose calibration set. No two-dose count is fitted into it.
The frozen decision accepts a cell only if its observed frequency is within
0.01 of the predicted outer interval. The 15 declared probability cells have
sampling-error family bound `30 exp(-10)<0.01`. False rejection of a true shared
model also allows for calibration failure, giving the conservative total
`2 exp(-6)+2 exp(-8)+30 exp(-10)<0.01`. This does not turn nonrejection into model
identification or full-CQ tomography.

In the final generated streams, the two-dose count is `29878/50000=0.59756`.
Its independent outer prediction is approximately
`[0.5899530676992,0.5977855030013]`, so the declared tester does not reject.
The source and compiler word checks also do not reject.

A separate synthetic alternative uses pulse area x+0.03 per call for this
held-out drive setting, with the original calibration unchanged. Its fixed
seed gives `32050/50000=0.641`, at distance approximately `0.0432144969988`
from the same predicted interval. The unchanged 0.01 rule rejects it. This is
an actual executed failure control for the shared-pulse assumption in this
tester family, not evidence about a physical apparatus.

Further controls preserve their logical scopes:

- Original flags are x-independent, even when their complete record law is
  retained. This cannot be repaired by simply increasing their count.
- An unrestricted one-dose detector bias confounds x; two doses with a shared
  fixed bias can identify it, while arbitrary dose-dependent biases need
  separate restrictions.
- At K=N=0, input `|g,0>` has zero initial mean and zero initial projection
  tail. The finite generator is zero, so a matrix exponential can have zero
  numerical residual. The true force has overlap `exp(-x²/2)` with that state,
  giving `sqrt(1-exp(-x²))>0` trace distance for x nonzero. Initial mean/tail and
  solver residual therefore do not supply the missing Galerkin error.
- Repeating one latent Bernoulli bit n times preserves one-shot marginals but
  destroys the fixed-iid concentration argument. Fresh fixed-parameter trial
  assumptions are substantive.

## 7. Full costs and evidence needed for a laboratory claim

For a fresh original-source attempt, physical filtering precedes the source.
Its success probability is `s_N s(q)²`; the calibration set gives the lower
bound `(1-1/4096)(1-q_hi/2)²`, approximately `0.5544426949585` here. Omitting s_N
from the denominator would omit failed preparation. The corresponding physical
compiler succeeds after filtering with probability s_N in this ideal model.

If complete attempts are truly independently reset and a new intended input
can actually be supplied each time, the expected cost per delivered accepted
source sample is `mu_source/(s_N s²)`, where mu is the **unconditional complete
attempt cost**, including failed filtering, reset, control, readout, records
and classical work. For the compiler it is `mu_compiler/s_N`. Unknown quantum
inputs and their references have no free-repeat permission.

The compiler's expected visible count of force labels is one. It is also the
expected number of physically executed force gates only under an explicit
flag-first, then-gate schedule. Coherently controlled implementations may
schedule a pulse in every slot; their actual schedule costs must be counted.
The same distinction applies when deriving gate costs from source labels.

The synthetic files contain 1120000 calibration trials, 150000 held-out trials
and 50000 explicitly alternative-model control trials. They are logical
simulated shots, not measured hardware use. Once-only calibration and any
shared audit setup are amortized over delivered outputs, not divided again by
the source retry probability. Time, energy, monetary and memory costs were not
measured, and no cost advantage is certified.

A device claim still needs the following concrete inputs: time-ordered raw
calibration and holdout streams with failures/leakage; independent evidence
for the common pulse and its drift; vacuum/probe preparation and quadrature
gain/offset/efficiency calibration; a justified effective Hamiltonian and
phase-gate error; characterization of the low-spectral filter and failed
reference handling; independent input mean-G certification; and measured
preparation, reset, gate, readout, classical, storage and calibration costs.
Finite record/tester data alone remain insufficient to certify the universal
full-CQ trace distance without the corresponding model or tomography contract.

## 8. Actual execution and verification classification

`generate_synthetic.py` writes six complete ordered streams and a clearly
labelled provenance file. Its declared generating values are q=1/2 and x=3/50.
The generator's PRNG is a reproducibility device, not an empirical randomness
claim. `certify_from_records.py` reads only the six record files and frozen
plan; it neither opens provenance nor receives the hidden generating values.
Its nominal value is recomputed from observed counts.

`independent_certificate_check.py` imports none of those production modules.
It uses `pi=4(arctan(1/2)+arctan(1/3))`, an independent normal-variable Gaussian
series, rational exponential enclosures and integer square roots. The
production helper uses Machin's identity and a different integral variable.
The checker verifies raw identities/counts, inverse endpoints, deterministic
nominal rounding, all budget arithmetic, the actual different-setting holdout
and nonshared-pulse rejection, and consistency with the public frozen model.
Its final actual receipt is `C_INDEPENDENT_CERTIFICATE_CHECK.json`.

The theorem and concentration/identifiability arguments are paper proofs.
Rational inequalities and finite raw-record accounting have actual independent
computational checks. The generated records are synthetic. No new Lean proof,
external real measurement, project experiment or hardware certification is
claimed. Counts of checks are execution inventory, not a physics completion
percentage.

The next empirical acceptance step is a declared real preparation/readout and
common-pulse calibration with the same two-dose held-out protocol, including
nuisance bounds and full failure/cost records. The next theoretical expansion
must pay new same-output errors for nonideal gates, arbitrary memory or more
general drive families; none is obtained from this ideal finite example by
renaming its certificate.
