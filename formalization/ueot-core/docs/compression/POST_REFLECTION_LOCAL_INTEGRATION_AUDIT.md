# Post-reflection scientific tightening — local integration audit

Status: **LOCAL FINAL AUDIT PASS**

Date: 2026-10-04

Canonical remote base: `origin/main@3cbec434411980af701d0342bbdd9531e1a9a813`

Local integration branch: `local/post-reflection-scientific-audit`

Validated integration tree: `dc7fc2f55cc541fbf528dac5dc61002a8db71e01`

This document is local integration evidence only. The integration branch is not a
registered research branch and is not intended for remote push. The two governed
source branches remain the cloud candidates if the user later authorizes push.

## 1. Governed source branches

### Track O

Branch: `compression/objecthood-post-qt-tightening`

Local tip after proof-lint closure: `2530543`

Stages completed:

- O-A: canonical RH certificate margin optimality endpoint;
- O-B: general-causal same-parent Objecthood terminal endpoint;
- O-C: least fixed-`kappa` canonical joint mixed-drift residual;
- O-D: finite strict-separation witness;
- O-E/O-G: finite-horizon, asymptotic-mean, Cesaro-invariant and Objecthood
  downstream propagation;
- public Track-O root import only.

Governance validator against `origin/main`: PASS.

### Track S

Branch: `compression/goa-primitive-defect-closure`

Local tip after theorem-scope lint closure: `f654a99`

Stages completed:

- S-A/S-B: actual reward bound -> Bellman optimal-value norm/span bound;
- S-C: primitive reward/transition defects -> `D_n -> 0`;
- S-D/S-E: primitive-input optimal-policy near-GOA terminal endpoints with no
  external `D_n -> 0` or uniform-span premise;
- public Compression root imports only.

Governance validator against `origin/main`: PASS.

## 2. Scientific findings that are genuinely stronger

### 2.1 RH certificate-class optimality

For one fixed recurrent-homeostasis system and potential, the QT canonical fault
certificate is not merely no worse than another certificate. Its real
homeostatic margin is the greatest margin attained by the existing RH1
`FaultBurdenCertificate` class. Consequently the canonical margin is positive iff
some certificate in that class has positive margin.

This is certificate-class completeness only. It is not a necessary-and-sufficient
physical homeostasis threshold because the potential, repair law, carrier, fault
kernel and parent remain fixed.

### 2.2 General-causal terminal Objecthood closure

The already-proved GCR equivalence now feeds the strongest same-parent terminal
API directly. Within the finite controlled-PMF semantics, arbitrary randomized
complete-history causal almost-sure repairability implies that the unchanged
canonical deterministic-stationary architecture supplies eventual-permanent
legitimacy. For a failing deletion this composes with the existing minimal-failure
witness and Track-X semantic bound.

No new repair law, path law or stronger causal completeness claim is introduced.

### 2.3 State-coupled canonical mixed drift

For fixed `kappa`, the new residual is the finite carrier supremum of the actual
mixed-kernel positive drift excess

`(E_mixed W + kappa * 1_damaged - W)_+`.

It is proved to be the least uniform residual satisfying exactly the statewise
mixed-drift inequality consumed by the RH occupation telescope.

At the standard RH coefficient

`kappa = (1 - faultHazard) * repairDrift`,

the old separated repair/fault certificate is a feasible point, hence the new
residual is never larger than `faultHazard * C.burden`, and in particular never
larger than the QT canonical fault envelope.

The three-state witness proves strict gain:

- `canonicalFaultBurden = 1`;
- `faultHazard = 1/2`;
- the separated canonical envelope is therefore `1/2`;
- `canonicalJointMixedDriftResidual = 0` at the same standard `kappa`.

Thus the strengthening is not cosmetic. It captures state correlation discarded
by separate worst-case repair/fault compression.

The joint residual is propagated through the existing RH3/RH4 machinery to:

- finite-horizon damaged occupation;
- asymptotic mean damaged occupation;
- invariant Cesaro cluster-point damaged-mass bounds;
- an existence theorem for an invariant Cesaro cluster point;
- an Objecthood specialization of the asymptotic mean theorem.

### 2.4 Primitive reward defects automatically close the value-span gap

For a finite discounted control model with actual reward envelope `|r| <= R`, the
new theorem derives

`|V*(s)| <= R / (1 - beta)`

and then

`span(V*) <= 2 R / (1 - beta)`.

For approximate quotients of one common literal finite micro model,

`|r_macro,n| <= R_micro + epsilonReward_n`,

so the moving macro optimal-value span has an explicit primitive envelope. This
removes the independent uniform-span assumption from the P-QUO radius closure.
Primitive reward and transition defects converging to zero now imply `D_n -> 0`
directly.

The strongest moving optimal-policy near-GOA endpoints therefore no longer need
an external `D_n -> 0` certificate or an external uniform optimal-value-span
bound.

## 3. Redundancy/deletion audit

### 3.1 Existing QT / RH certificate API is not deleted

The joint certificate is sharper, but the old separated
`FaultBurdenCertificate` interface remains a useful modular sufficient
certificate and supplies a generic comparison theorem. The new construction is
an additive strengthening, not a reason to rewrite historical RH/QT files.

### 3.2 `ValueSpanClosure` is not deleted

`PrimitiveRewardSpanClosure` removes its external span premise only under the
stronger structural condition that the moving quotients share one literal finite
micro model. The older theorem remains more general when a uniform span bound is
available independently or the underlying micro system is not literally fixed.

### 3.3 No historical Objecthood/GCR theorem is rewritten

The general-causal terminal theorem is a higher-level endpoint composed from the
existing GCR equivalence and existing same-parent terminal results. Historical
proof surfaces remain valid and independently useful.

## 4. Counted-core 4 -> 3 re-audit

Result: **NO JUSTIFIED DELETION**.

The frozen counted core remains

`{M-QD-01, M-TC-01, M-PE-01, M-OI-01}`.

The new results do not supply any missing ablation primitive:

- M-QD-01 still uniquely supplies the registered countable a.e. quotient/common
  measurable-decoder primitive used by P-PRED-01;
- M-TC-01 still uniquely supplies the registered multiplicative certificate
  recurrence used by P-DYN-03;
- M-PE-01 still uniquely supplies the registered positive-eigenvector stochastic
  martingale calculus used by P-EVO-04;
- M-OI-01 still supplies the registered continuous-observable vanishing-residual
  to invariant-limit interface used by P-GOA-01.

The primitive GOA closure feeds existing long-run machinery; it does not replace
M-OI. The joint mixed-drift results are downstream Objecthood/RH results and do
not reconstruct any counted generator surface. No ledger, coverage, source P-ID,
or minimal-core membership is modified.

## 5. Hard boundaries retained after the new proofs

The audit finds no basis to weaken these boundaries:

1. mean/Cesaro/invariant damaged-mass control does not by itself imply pathwise
   recurrent legitimacy;
2. neither QT nor the joint mixed-drift residual is a necessary physical phase
   transition threshold;
3. repair-law self-reconstruction remains outside these results and still needs
   the separate trusted-substrate/reconstruction lifecycle;
4. primitive GOA closure still assumes one common literal micro model, exact
   reference defects, a positive source action gap, and source closed-loop
   contraction;
5. the joint homeostasis result canonicalizes `lambda` for fixed `kappa`; global
   optimization over `kappa` is a distinct future research problem, not needed
   to establish the present strict improvement.

## 6. Formal validation

For the exact validated integration tree:

- `git diff --check origin/main...HEAD`: PASS;
- proof-escape scan over all new theorem files: CLEAR;
- research-governance regression suite: PASS;
- Track O exact candidate governance validation: PASS;
- Track S exact candidate governance validation: PASS;
- `lake build UEOT.V3.Compression`: PASS, 9131 jobs;
- `lake build UEOT`: PASS, 9150 jobs;
- representative `#print axioms` for endpoint, joint-drift, strict-witness,
  Cesaro, primitive-span and primitive-GOA theorems: only `propext`,
  `Classical.choice`, `Quot.sound`;
- the Lean/source integration tree immediately before this docs-only final audit
  commit equals the exact tree that received the full build:
  `dc7fc2f55cc541fbf528dac5dc61002a8db71e01`; current HEAD adds only this
  local audit document.

Warnings emitted during full builds are pre-existing repository linter warnings;
the new proof-lint warnings discovered during integration were cleaned and the
fixes were propagated back to both governed source branches.

## 7. Final assessment

The post-reflection cycle achieved two substantive improvements rather than a
wrapper expansion:

1. RH/QT was sharpened from separate worst-case fault certification to a least
   state-coupled mixed-drift residual with a machine-checked strict-separation
   witness and downstream occupation/invariant consequences.
2. Moving quotient/GOA closure lost a genuine auxiliary uniform-span hypothesis;
   primitive defect convergence now supplies the needed value-span and `D_n`
   control internally under a common finite micro model.

The endpoint additions merely expose already implied strongest semantics and are
kept small. No further theorem is required to close the scope of this cycle.

The natural next mathematical questions — optimizing the joint ratio over
`kappa`, relaxing the common-micro condition, pathwise recurrent legitimacy, or
repair-law self-reconstruction — are separate research objectives and should not
be smuggled into this completed tightening cycle.

## 8. Cloud state

No new research branch or integration branch has been pushed. `origin/main`
remains `3cbec434411980af701d0342bbdd9531e1a9a813`.

Cloud action is intentionally blocked pending explicit user approval.
