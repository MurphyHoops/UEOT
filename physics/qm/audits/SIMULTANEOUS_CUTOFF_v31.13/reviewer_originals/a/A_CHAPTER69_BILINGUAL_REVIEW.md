# A — Chapter 69 scientific and bilingual scope review

Baseline: main `cb17211653fde30aa50e0e9848798a6a5b3b3f12`.
Review author: native research agent A. Internal AI review only.
Reviewed sources: `iteration_v31_13/chapter69.zh.md` and
`iteration_v31_13/chapter69.en.md`, all nine sections in both languages.

## Result

The chapter joins the correct statements to the same source, same parameter,
same record alphabet, same finite untouched reference and same physical
preparation contract. The two languages have matching substantive scope.
The chapter preserves the difference between genuine Galerkin evolution,
normalized projected evolution and finite-matrix residuals. It neither treats
the finite predictor as a permitted hardware gate nor upgrades a synthetic
tester check to an empirical full-CQ guarantee.

The reviewed version already includes the two prior substantive scope
corrections: fixed-sample coverage is not confidence conditional on certificate
admission, and the additive-offset nonidentifiability claim is limited to
single-dose access. Two-dose access with one shared fixed offset is correctly
stated to identify both ideal parameters.

## Corrections sent to the integrator

1. Section 69.6 should say `D(X), the quadratic-form domain of the positive
   operator X^2`. The reviewed phrase “form domain of X / X 的型域” is
   ambiguous and could denote a weaker domain. The actual estimate requires
   `||X psi||`, not `D(X^2)`. The same shorthand in A's draft was corrected.
2. Section 69.3 should declare nonnegative physical durations t. If retaining
   a negative-t claim, an integral up to `|t|` must evolve its finite prefix
   along the signed time direction. The signed coupling already supplies
   the required control signs, so restricting physical duration to t>=0
   changes no intended application.
3. Specify additive measured-momentum bias as `P_observed=P+b` when giving
   `Phi(2x-sqrt(2)b)`. A generic “threshold bias” label does not fix the sign
   convention; the current C proof uses the additive convention explicitly.

These corrections concern precise domains and conventions, not a new
numerical or experimental result. Final source hashes and inspection of the
integrated revisions are recorded separately.

## Strongest claims checked

- P-OPT-05 uses unnormalized reference prefixes and actual complete CPTP
  suffixes; state-dependent branch masses and zero events are handled without
  granting hidden-history access.
- P-MICRO-06 uses a separate zero-frequency force realization and a
  noncircular finite-matrix/strong-convergence/lower-semicontinuity energy
  proof. The mass in the boundary-flow square root is retained.
- P-MICRO-07 is a finite Duhamel remainder, not an asserted infinite Dyson
  convergence. The true suffix stays left, the finite right factors have
  controlled support, and the same cutoff applies to the entire word.
- C-MICRO-03 accurately defeats automatic inheritance of X^2, without
  defeating the trace-distance approximation theorem.
- P-ROB-04's coverage is fixed-n and model-conditional; the nominal area uses
  observed data and its entire outer displacement. Flags alone cannot identify
  x, while the ideal quantum tester can.
- P-ROB-05 charges the physical filter once, including its failure-conditioned
  reference, and then compares true infinite, nominal infinite and exact
  finite processes in that order. Its uniform theorem is distinct from the
  later concrete-input interval calculation.

The result table, machine-proof scope and experimental status remain
conservative: no new Lean, no protocol-matched real device data, and no closing
of the retained field, particle, gravity, reconstruction or mechanism tasks.
