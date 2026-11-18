## Joint identification, finite-sample coverage, and same-source certification

**P-ROB-06 (joint identification and coverage from two trusted settings).**
For the declared two-mode vacuum source, let `lambda in [1/5,2/5]` be the
common coupling scale and `eta in [9/10,1]` a fixed symmetric visibility
shared by the declared binary readouts. A fresh trial prepares `|+X>`,
evolves for t, and measures X. Its observed mean is

\[
\mu_t=\eta e^{-a(t)\lambda^2},\qquad
a(t)=4\left[1-\cos t+\frac4{25}(1-\cos(3t/2))\right].
\]

The zero-time setting and `t=3/2` therefore determine

\[
\eta=\mu_0,\qquad
\lambda=\sqrt{\frac{\log\mu_0-\log\mu_{3/2}}{a(3/2)}}.
\]

The identification domain requires positive visibility, the nonnegative
coupling convention, known frequencies and relative couplings, vacuum
preparation, and trusted preparation/readout structure. A single nonzero
time admits the exact equivalence curve
`eta'=eta exp[a(t)(lambda'^2-lambda^2)]`; more shots at that setting cannot
remove the degeneracy. With an unknown common thermal occupation n, all
single-slot coherences identify only `(2n+1)lambda^2`. An unknown detector
bias or unrestricted setting-dependent drift requires additional independent
anchors and an appropriate error model. These quantities are not silently
treated as identified by the present calibration.

Each calibration setting generated 200,000 synthetic independent trials.
For the plus-outcome frequency, use the Hoeffding radius

\[
r_p=\sqrt{\frac{\log(4/0.01)}{2\cdot200000}}+10^{-9},
\]

and transform it into expectation intervals `I_0,I_1`. The joint set is

\[
C(D)=\{(\lambda,\eta)\in[.2,.4]\times[.9,1]:
\eta\in I_0,\;\eta e^{-a(3/2)\lambda^2}\in I_1\}.
\]

Under the declared independent stationary sampling assumptions, coverage
is at least 99%. The `10^-9` term is a numerical sampling-probability
allowance frozen in advance. An independent interval implementation checked
all 98 probabilities actually used by the generator; the largest discrepancy
was below `1.011e-16`. Coverage is a statistical theorem: one fixed-seed
synthetic run does not empirically establish the coverage frequency.

The realized joint set is nonempty. Calibration alone selected

\[
\widehat\lambda=0.299314119192,\qquad
\widehat\eta=0.959480000000.
\]

Outward projections satisfy

\[
\lambda\in[0.292143974948,0.306484263435],\quad
|\lambda-\widehat\lambda|\le0.007170144244,\quad
|\eta-\widehat\eta|\le0.007740457121.
\]

Interval arithmetic verifies that the nominal point belongs to the joint
set. The displayed rectangle is only an outer enclosure. The generator's
truth file is read solely by generation and a separate generator audit; it
is not an input to estimation or held-out decisions.

**P-ROB-07 (a complete CQ certificate and independent holdout).** Combining
the same-source all-input parameter bound, the K=20 Galerkin bound, and the
interval-validated exact rational CP/TP repair gives

\[
\begin{aligned}
D_{\rm full}
&\le\frac{51}{10}(0.007170144244)+0.00001344+10^{-8}\\
&=0.0365811856444\le0.036581185645<0.05.
\end{aligned}
\]

This inequality retains an arbitrary finite untouched reference and every
`f,pf,ppf,ppp` record. Preparation, control, and effective-model errors are
zero here as assumptions of the selected synthetic source; corresponding
device certificates have not been established. Normalized successful
conditional states do not inherit this precision without accounting for
the acceptance probability.

For each fixed binary terminal tester, uncertainty in the shared visibility
adds at most `|eta-etahat|/2`. Thus the complete readout distribution obeys

\[
D_{\rm measured}\le0.0404514142049\le0.040451414205<0.05.
\]

The quantum-output and readout-distribution metrics are recorded separately.
The four terminal observables actually used, `XX,XY,YZ,ZZ`, are contracted
with the repaired rational Choi matrices in exact rational arithmetic; an
unbudgeted later floating contraction is not included in this certificate.

The nominal model, statistical rule, and program were hash-bound before
holdout generation. Each family used 100,000 trials for each of the four
observables, retaining all eight stopped-record/sign events:

| Holdout family | Timing/control change | Result |
|---|---|---|
| Original three-slot deployment | `(2/3,3/4,1/2)` with noncommuting intermediate rotations | Frozen contract not rejected |
| Changed intervals | `(3/4,2/3,1/2)`, same total duration and controls | Frozen contract not rejected |
| Shared-detector violation | Original timing, generator visibility eta=.70 | Frozen model contract rejected |

An independent interval history-pair implementation encloses the continuous
parameter set using 288 lambda grid points, the eta endpoints, and a
`5.1 mesh/2` covering allowance. Simultaneous confidence intervals cover the
96 events. When the frozen model holds, the combined calibration/holdout
false-rejection probability is at most `.02`. Non-rejection establishes
neither model uniqueness nor device validation.

## Strong baseline, cost, and real-data qualification

Standard persistent joint evolution, the Gaussian influence functional,
and the process used here describe the same conditional quantum map. With
the same calibration data, parameter set, controls, and robust rule, their
predictions agree. The independent K=20 Galerkin and Weyl backends differ
in the full CQ floating calculation by approximately `8.93e-16` and
`9.32e-16` for the two normal timings; interval enclosures and exact physical
repair separately supply the numerical guarantee. The method verdict is
**`EQUIVALENT_NO_ADDED_GAIN`**. This iteration does not establish an additional
physical prediction or an advantage over a strong standard quantum method
under equal resources.

Resetting the bath between slots changes the full CQ nominal output by
approximately `.100895` and `.104952`. This confirms that the ablation loses
memory; it is not a substitute for the strong-baseline comparison and does
not reject every possible Markov model. The retained synthetic data contain
1.6 million trials: 400,000 calibration and 1.2 million holdout trials. No
failed attempt was filtered out. The holdout trials consumed 2,966,811
interaction slots when charged through their actual stopping prefixes.
These are simulated protocol resources, not hardware calls or laboratory
wall time.

A separate, predeclared reproduction used one author-published processed
observable from Zhu et al.,
`O=X tensor (2Z+Y)/sqrt(5) tensor I tensor ...`. All 5-by-11 values in the
original HDF5 member were retained. The mean-curve RMSE is `0.01860965`
against the authors' noisy simulation and `0.03351389` against the ideal
simulation on matching grid points. The original HDF5 member, archive
SHA256/MD5, source, and visible license status are preserved. These are not
raw trials for the oscillator source: the protocol-specific failure,
timing, vacuum, reference, reset, and calibration/holdout records are absent.
They cannot provide the device certificate required by this chapter.

Three conclusions therefore coexist: the declared source has a mathematical
and synthetic certificate; an external processed experimental observable has
been reproduced; the matched device contract remains **`NOT_CERTIFIED`**.
Independent physical selection and the broader unification task remain open.
