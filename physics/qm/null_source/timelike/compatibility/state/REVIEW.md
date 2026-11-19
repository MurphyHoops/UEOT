# Independent review by A: state and semiclassical compatibility

Date: 2026-11-19. Frozen predecessor:
`1a90c68b6178968e6b8239fc97a8b26200f8d59d`.
All actions were scoped to the authorized Local Mac project.
No frozen evolution calculation was changed or rerun wholesale.

## Own result and independent review received

The current state certificate was regenerated after adding the original
bounded-mixture variance identity, then replayed successfully:

- `state/check.py --write`: PID 60086, passed.
- `state/check.py --check`: PID 60177, passed.
- Current code SHA256:
  `8a3af529b17af56b5b09c1be678d2a4ac6797cff8e6351d3387f7fdd95d802a3`.
- Current receipt SHA256:
  `f9715ca5e4a5d110678844a941dd8899a129db344b4a56df924b6331046483e2`.

B independently checked the exact subtraction mismatch, static reference
including the regular zero mode, finite-rank state construction, finite
pressure envelope, and nonzero unique-frequency pressure obstruction.
No formula issue remained. The pressure frequency is explicitly a conformal
time frequency: 2 sqrt(3), or proper-time frequency 2 on static a=sqrt(3).

The logarithmic obstruction is an exact comparison of renormalized cutoff
stresses on two independent smooth metrics, not an argument from divergent
bare particle number. Equal h and K leave the relevant E3 subtraction
coefficient different by 1/2; the actual old kernel therefore produces
H_N/(72 pi^2) plus a finite local offset on the new static geometry.
Finite curvature constants cannot cancel that cutoff divergence.

The finite-mode repairs retain exact old canonical blocks, not rounded
numerical centers. Their high modes belong to a Hadamard state appropriate
to the new static geometry. They are legal states with finite stress, but
their unique k=2 pressure oscillation rejects an exact static semiclassical
future with the stated constant classical source.

## B: scaling and uniform full-field defect

I read the complete scaling program, checked its formulas independently,
and actually ran `scaling/check.py --check`: PID 58136, passed.

Reviewed code SHA256:
`cdd9f424040b1fb35687dff71e3fa2ac713de02d837d2e8c12b6ae7574d98452`.

Reviewed receipt SHA256:
`28e81cae349be501bffa3c310b336e488b295c4c260f1673baa610c7cf31969b`.

The fixed-physical-mu logarithm has coefficient H1/(576 pi^2).
Source-side alpha must shift by minus s/(576 pi^2) when mu changes by
exp(s). Thus changing the subtraction scale alone is not a physical repair.
The stated constant homothety, including its full metric jets and all
canonical mode data, is a genuine Hadamard transport.

The instantaneous canonical A,B equations give the claimed rapidity
bound. Energy has no A-B cross term, while pressure retains its cross
term. The nonzero-mode multiplicity k^2, regular zero-mode energy, local
additions, and the inherited uniform ultraviolet tail are all present.

The initial diagonal zero-mode covariance belongs to the preparation seed.
Its propagated physical covariance generally has a nonzero q-p term.
The correction to the README makes the full transformation V_lambda =
S_lambda V S_lambda^T explicit. The numeric stress uses the conserved
p variance, so this clarification does not alter its bounds.

The reported lambda=8192 equation defects are uniform component bounds,
less than 0.000286660 for density and 0.008066751 for pressure. They apply
to a declared positive retuning of the source moment correlated with the
same exact initial quantum density. They are not bounds on distance to
an exact metric or a proof of coupled existence.

## C: initial roots, source correlation, and exterior scope

I read the complete constraints program, independently checked the two
root equations and their monotonic domains, and actually replayed the
final corrected program: `constraints/constraints.py --check`,
PID 59814, passed.

Reviewed code SHA256:
`27f95cc4bd8267845dc902903a3b2d384e387f54f6a950bbb9ad3f326e7566be`.

Reviewed receipt SHA256:
`0572e61ebbaa2ab388a9af0c84adff52dabdc0fffcd618b36b5c6cb8c4a8f903`.

For fixed M2, x - 1/x - C log(x) is strictly increasing for positive x.
For whole-field transport, x - C log(x) is increasing on the explicitly
selected x >= 1 branch. The program does not claim to exclude all small-x
roots of the latter equation. The interval roots and their quantum-fraction
bounds are correctly correlated with the old quantum-density interval.

The exact retuned moment and a rational approximation are separate
contracts. Choosing an interval midpoint independently is not an exact
initial solution. The finite nonzero residual of the rational instance is
correctly exposed and propagated into the later defect certificate.

Two terminology corrections identified during review were adopted:
the classical momentum field is an RMS quantity for the retained random
source, and zero-mode covariance at an arbitrary slice preserves the old
q-p correlation rather than resetting to the diagonal preparation seed.

The no-trapping and ADM calculations are conditional on a specified
total-density profile. They do not supply the unknown exterior quantum
state, its RSET, or a global semiclassical solution. The inherited quintic
taper is C2; a global smooth Hadamard completion would need a new smooth
matching construction and new mass accounting.

## Root: retained source noise and the actual meaning of the mean defect

I read the new `source_noise` and `retained_source_mixture_noise`
calculations in `../review.py`. Their assumptions and inequalities agree
with the independent symbolic identity in this directory.

For the bounded original A source Y=s/2+X, X=+/-sqrt(3)/2 equiprobably,
E Y^2=1 and Var(Y^2)=3/4. More generally symmetric X with E X^2=3/4 has
Var(Y^2)=E X^4+3/16 >= 3/4. The centered reference and positive mixture
give Var(A) >= Var(Y^2) A_f^2 for smooth spacetime stress smearing.

For a nonzero nonnegative density smearing in the certified inner domain,
A_f/A_geom equals the constant classical density fraction. The independent
uniform density mean-defect bound then supplies the upper bound on
|E A|/A_geom needed to transfer this to a variance bound relative to the
total mean squared. Both exact and rational source certificates exceed
0.7495 at lambda=8192. Neither the construction nor this noise lower bound
implies a geometry fluctuation estimate.

## Literature and logical boundary

The primary-source audit is detailed in README. In particular, the
surface-Hadamard coupled well-posedness assertions reviewed in
arXiv:2205.11671 are conjectural; the 2024 surface stress theorem requires
metric derivative information beyond h and K. The checked local existence
results of Meda-Pinamonti-Siemssen and Gottschalk-Siemssen are flat-space
cosmological results with specified state and regularity hypotheses.
They cannot be silently applied to the present closed-S3, massless,
fixed-preparation problem.

The constructive exits completed here are exact legal state transport,
an explicit legal finite-mode repair with finite stress, and the team's
controlled full-field equation-defect construction. A nearby exact
self-consistent closed-space evolution remains a separate existence and
stability problem.
