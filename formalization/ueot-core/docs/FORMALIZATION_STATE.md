# UEOT Core Lean — Live Formalization State

> Recovery entry point. Machine-readable lane state is `PID_STATUS.yaml`.
> Integrated source-count truth is `V3_COVERAGE_STATUS.md`.

Last synchronized: **2026-09-13**

## Environment

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- canonical source object: available for semantic audit in the project File Library
- exact source bytes in public repo: **pending synchronization**
- current audit did **not** recompute the SHA from local raw bytes
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`

## Current checkpoint

| operational state | count |
|---|---:|
| integrated proved | **57** |
| active proof | **3** |
| blocked | **0** |
| pending unclassified | **46** |
| total | **106** |

The authoritative source-level ledger is **57 proved / 49 not yet counted**.
The operational partition splits those 49 into 3 active proof lanes and 46
still-unclassified/audit-queue P-IDs.

## Latest counted promotions — P-OMG-01 / P-OMG-02

P-OMG-01 formalizes the frozen finite monotone-failure reconstruction theorem:
a failing deletion set is exactly a superset of an inclusion-minimal failing
deletion set. It reuses `UEOT.Finite.exists_minimal_subset` rather than
rebuilding blocker theory.

Canonical theorem:

- `UEOT.V3.OmegaMinimalFailure.p_omg_01`.

P-OMG-02 formalizes the source causal-integrity margin
`Gamma(T)=infDist(T,F)` and its 1-Lipschitz bound, reusing
`Metric.lipschitz_infDist_pt`.

Canonical theorem:

- `UEOT.V3.OmegaIntegrityMargin.p_omg_02`.

Promotion evidence:

- P-OMG-01 feature head `effa5bf10787095b2dd1bb86e68f100cb907f0af`,
  CI `34750708593`: success;
- P-OMG-02 feature head `8d5ddee1faff1ae588a478e2a1c58235852d7500`,
  CI `34750765181`: success;
- combined clean integration/main proof commit
  `4db94c39dddce53a5543e40568e5fc104321e88b`;
- integration CI `34751042701`: success;
- post-main CI `34751300612`: success;
- prohibited-proof audit: zero `sorry`, `admit`, `native_decide`, unsourced
  `axiom` in the new proof files;
- canonical-source semantic audit: complete.

Do not reopen these lanes absent a substantive source mismatch or CI regression.

## Active proof lane — P-DDH-01

Frozen theorem: the gauge transformation
`Pi'=Pi+lambda*chi`, `Phi'=Phi+chi` leaves `Pi-lambda*Phi` invariant.

- branch: `formal/pddh01-gauge-cancellation`;
- current head: `d1528ed40748ed8163af3565575c8a3465124818`;
- candidate theorem: `UEOT.V3.DualDriveGauge.p_ddh_01`;
- first CI `34751185618`: failed;
- failure was addressed by replacing the Unicode `Pi` binder token with a
  nonreserved Lean identifier; theorem semantics were unchanged;
- current CI `34751461041`: in progress at synchronization time.

Do not promote until the current feature CI is green, source semantics are
re-audited, and the clean latest-main integration lifecycle is complete.

## Active proof lane — P-ALI-03

Frozen theorem: for the coordinated field
`G_eta=(1-eta)G+eta g`, with `0<=eta<=1` and `<g,G><0`, the parent-value
instantaneous derivative is positive iff

`eta > -<g,G>/(||g||^2-<g,G>)`.

- branch: `formal/pali03-coordination-threshold`;
- head: `5a85a3321bf3639a59996be8cea59357fe6cddab`;
- candidate scalar-normal-form theorem:
  `UEOT.V3.AlignmentThreshold.p_ali_03`;
- feature CI `34751255136`: in progress at synchronization time.

Semantic guard: before promotion, decide whether the frozen Hilbert-space
statement requires an explicit Hilbert wrapper connecting the scalar variables
to `<g,G>` and `||g||^2`. Do not count a merely algebraic scalar restatement if
that wrapper is needed for source-facing closure.

## Active proof lane — P-EVO-01

Frozen theorem: finite-type deterministic mean-intensity Price decomposition
with parent frequencies, reproduction intensities, row-stochastic transmission
kernel and parent/offspring traits.

- branch: `formal/pevo01-price-decomposition`;
- head: `bc5f4d55e5feecf7f2fbcf09521943a551e179b2`;
- candidate theorem: `UEOT.V3.EvolutionPrice.p_evo_01`;
- feature CI `34751340890`: in progress at synchronization time.

Semantic guard: before promotion, audit whether the direct algebraic theorem
must be supplemented by an explicit source-facing `M=D_b K`,
`p'=pM/bar_b` wrapper. Preserve the source distinction between deterministic
mean frequency dynamics and expected random frequency ratios.

## Grounded audit findings

Known non-A fronts include:

- P-PER-02: Feller/Krylov–Bogolyubov occupation theorem;
- P-PER-04: Bouligand tangent-cone viability necessity;
- P-REC-03: hitting-time potential `PV_A-V_A=-1` off the target;
- P-REC-04: negative-drift expected hitting-time bound;
- P-QSD-01: conditional-survival stabilization implies QSD/exponential survival;
- P-QSD-03: simultaneous mixing/survival persistence window;
- P-QSD-04: self-adjoint compact-resolvent killed-diffusion spectral theorem.

Do not swap P-QSD-01 and P-QSD-03: the numbering above is frozen-source truth.

Potential short closures still requiring careful API/source audit include
P-COMP-03. P-DDH-04/05 are not treated as quick algebraic lanes because they
need rank/stacked-Jacobian and singular-value perturbation infrastructure.
P-REF-03 must retain arbitrary signal-space conditional expectation rather than
being weakened to a finite signal table.

## Closed lanes

Do not reopen without a substantive source mismatch or CI regression:

- all 57 P-IDs listed in `V3_COVERAGE_STATUS.md`, including P-INT-01,
  P-INFO-03, P-ID-02, P-OMG-01 and P-OMG-02.

## Current phase

Continue the remaining source-to-main A/B/C/D audit while active feature CIs
run. Open only source-faithful high-leverage lanes. When a feature goes green,
re-audit exact frozen semantics before clean-porting to the latest `main`.
Feature green never increments coverage.

## Public canonical-source synchronization

The exact canonical source bytes are still not present in the public repository.
Required for third-party self-contained reproduction:

1. synchronize exact bytes without regeneration;
2. independently recompute SHA-256;
3. verify the frozen manifest value.

This is separate from theorem proof status.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, GitHub Issue #56,
   `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch current main SHA and relevant Actions runs/branches/PRs.
3. Distinguish source audit, theorem closure, official import reachability,
   feature CI, main integration, post-main CI, ledger counting, and public
   source-artifact reproducibility.
4. Read the frozen source statement before writing Lean.
5. Audit existing main code before creating new infrastructure.
6. Never use `sorry`, `admit`, unsourced axioms, `native_decide`, or
   kernel-skipping devices as proof completion.
7. While CI runs, advance another independent audit/proof lane.

## Repository truth hierarchy

1. frozen canonical source specification;
2. `docs/V3_COVERAGE_STATUS.md`;
3. `docs/PID_STATUS.yaml`;
4. GitHub Issue #56 for live construction intent;
5. `docs/FORMALIZATION_STATE.md`;
6. official imported Lean source on `main`.