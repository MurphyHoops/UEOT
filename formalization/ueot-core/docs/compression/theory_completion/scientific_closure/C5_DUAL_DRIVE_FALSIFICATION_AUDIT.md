# C5 — Π/Φ Common-Dimension Falsification Audit

Package status: **LOCAL COMPLETE / PORT OPEN**
Conclusion classes: **THEOREM + NECESSARY CONDITION + METHOD**
Mechanism identification: **NOT ESTABLISHED**
Real-world support: **UNVERIFIED**

## 1. Canonical Core inputs reused

C5 does not re-prove the frozen DDH lane.

- P-DDH-04 (`CommonBottleneckRank.p_ddh_04`) proves that at one fixed budget
  point, if all stacked response coordinates factor through the **same**
  differentiable two-dimensional latent map `z(B)`, the stacked Jacobian rank is
  at most two.
- P-DDH-05 proves genuine operator-2-norm singular-value perturbation stability
  and the exact-two-above-threshold conclusion under the registered spectral
  window.

The same-budget and common-latent requirements are mandatory. Environment-wise
rank-two fits with different latent maps are not accepted.

## 2. New Scientific-Closure decision layer

`C5DualDriveTest.lean` adds `DualDriveVerdict`:

- `rejected`: estimated third singular value exceeds the operator-norm error
  radius;
- `compatible`: estimated third singular value plus error lies below the
  registered practical-zero tolerance;
- `ambiguous`: neither statement is certified.

`matrixSingularValue_perturbation` exposes the generic indexed perturbation
bound from the already proved P-DDH-05 infrastructure.

On that good event:

- `dualDrive_rejected_sound` proves the true third singular value is strictly
  positive;
- `dualDrive_compatible_sound` proves only that the true third singular value is
  below the practical-zero tolerance;
- `dualDrive_ambiguous_iff` preserves abstention.

`commonTwoDrive_rankNecessary` directly exposes P-DDH-04 as the exact common-2D
necessary rank condition.

## 3. Synthetic positive/negative controls

`evidence/c5_dual_drive_benchmark.py` freezes `eta=0.10`, `tau0=0.15`, one
coordinate normalization and same-budget semantics. Exact diagonal linear
benchmarks provide:

- 2-drive positive controls → COMPATIBLE;
- 3-drive negative controls → REJECTED;
- boundary case → AMBIGUOUS;
- separate 2-drive/3-drive held-out controls with the same expected behavior.

This is a synthetic method/power check, not physical Π/Φ evidence.

## 4. Hard interpretation boundary

Low rank is necessary for the declared common two-dimensional bottleneck but is
not sufficient to identify the coordinates as UEOT Π/Φ. Any two-dimensional
latent reparameterization or unrelated mechanism can satisfy the same rank
condition. C5 therefore requires an independent metrological/semantic anchor
before any mechanism-identification claim.

No such independent physical anchor or registered natural-system dataset is
present in this local package.

## 5. Verdict

The local C5 falsification method is closed. The broader Core §31.2 C5 port
remains OPEN for independently anchored physical measurements and registered
real-system 2/3-drive held-out tests.
