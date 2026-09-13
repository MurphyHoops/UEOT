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
| integrated proved | **59** |
| active source-facing lanes | **2** |
| blocked | **0** |
| pending unclassified | **45** |
| total | **106** |

The authoritative source-level ledger is **59 proved / 47 not yet counted**.
Feature-green work is not included in the 59 until the full promotion lifecycle
has completed.

## Latest counted promotions — P-DDH-01 / P-ALI-03

### P-DDH-01

Frozen source: `Pi'=Pi+lambda*chi`, `Phi'=Phi+chi` leaves
`Pi-lambda*Phi` invariant.

Canonical theorem:

- `UEOT.V3.DualDriveGauge.p_ddh_01`.

Evidence:

- feature `formal/pddh01-gauge-cancellation`;
- source-closed head `71a26d2fce4087fb4c7ed763b42f74118186a739`;
- feature CI `34751815827`: success.

### P-ALI-03

Frozen source: for `G_eta=(1-eta)G+eta g`, `0<=eta<=1`, and
`inner(g,G)<0`, the parent-value derivative is positive iff

`eta > -inner(g,G)/(||g||^2-inner(g,G))`.

Canonical theorem:

- `UEOT.V3.AlignmentThreshold.p_ali_03`.

Evidence:

- feature `formal/pali03-coordination-threshold`;
- source-closed head `bbb9f7b1cc8f202fedf5d096fe2707f760d83c4a`;
- feature CI `34751936845`: success;
- final source-facing theorem is Hilbert-space level, not merely the scalar
  helper.

### Joint promotion

- authoritative clean integration branch:
  `formal/pddh01-pali03-integration-v3`;
- clean integration/main proof commit:
  `9bff83a544929a0191596f6a1b9c7c8d2a6f87b7`;
- integration CI `34752277556`: success;
- post-main CI `34752528830`: success;
- prohibited-proof audit: zero `sorry`, `admit`, `native_decide`, unsourced
  `axiom` in both proof files;
- exact frozen-source semantic audit: complete.

Scratch branches created during GitHub contents/ref staging are not authoritative
and must not be merged:

- `formal/pddh01-main-integration`;
- `formal/pddh01-main-integration-clean`;
- `formal/pddh01-pali03-main-integration`;
- `formal/pddh01-pali03-integration-v2`.

## Active proof lane — P-EVO-01

Frozen source: finite deterministic mean-intensity dynamics with
`M=D_b K`, deterministic `p'=pM/bar_b`, `b_i>=0`, `bar_b>0`, row-stochastic
transmission, and the exact Price selection/transmission identity. The source
explicitly distinguishes this deterministic ratio from an expected random
population-frequency ratio.

- branch: `formal/pevo01-price-decomposition`;
- current head: `1a17175b7a7bf2338c5bcc648085bf5e7ef09a30`;
- candidate theorem: `UEOT.V3.EvolutionPrice.p_evo_01`;
- explicit source interface includes `meanOffspringEntry`, `nextFrequency`, and
  `offspringTraitMean`;
- previous CI failures were Lean elaboration/finite-sum rearrangement issues,
  not source-semantic failures;
- current CI `34752778143`: in progress at synchronization time.

If green, perform prohibited-proof audit and clean-port to latest main. If it
fails, read the decoded job log and fix only the exact compile issue.

## Active source-closed lane — P-COMP-03

Frozen source: finite nonempty cut family, each `K_pi` is
`L_pi`-Lipschitz, `Gamma_comp(T)=min_pi d(T,K_pi T)`, and
`L=max_pi L_pi`; the exact conclusion is `(1+L)`-Lipschitz.

- branch: `formal/pcomp03-composition-margin`;
- head: `7e074e694c26e52901342336b5e57b666df4fa8c`;
- theorem: `UEOT.V3.CompositionMargin.p_comp_03`;
- feature CI `34752374454`: success;
- source semantic audit: complete;
- the implementation keeps the finite minimum/maximum explicitly through
  `Finset.inf'` / `Finset.sup'` and does not silently replace `1+L` by `2`.

Exact next lifecycle step: clean-integrate to the latest `main`, then require
integration CI, safe main fast-forward, post-main CI, and ledger synchronization
before counting P-COMP-03.

## High-value source audit — P-KL-01

The repository already contains a likely A-class closure:

- `UEOT.V3.InformationEventBernoulli.map_eventIndicator_eq_bernoulliLaw`;
- `UEOT.V3.InformationEventBernoulli.bernoulliKL_event_le`.

These prove that a measurable event indicator pushes any probability law to
the Bernoulli law with success probability equal to the event probability, and
that KL data processing lower-bounds the original KL by the Bernoulli KL.

Before opening a proof lane, match the frozen source definition/conventions of
`d_Bern(p||q)` exactly. If it matches the measure-level Bernoulli KL already
proved on `main`, create only a source-facing wrapper; do not rebuild the
indicator or data-processing foundation.

## Other grounded audit findings

- P-EVO-02: B/C boundary; finite copied-label MI additivity likely reuses the
  existing KL/entropy foundation but the exact independent-product wrapper has
  not yet been found.
- P-EVO-03: primitive Perron–Frobenius asymptotic; not quick.
- P-EVO-04: genuine conditional-expectation martingale layer; not quick.
- P-DDH-02/03: finite exponential-family differential/KL projection theorems,
  not pure algebraic one-liners.
- P-DDH-04/05: rank/stacked-Jacobian and singular-value perturbation layers.
- P-ALI-01: global one-form integrability; heavy.
- P-ALI-02: potentially moderate, but source closure requires the actual
  derivative/chain-rule layer rather than assuming the desired equality.
- P-REF-01/02, P-ALG-01: not quick closures.
- P-REF-03: arbitrary signal-space conditional expectation; a finite-signal
  surrogate is invalid.
- P-PER-02, P-PER-04: not A.
- P-REC-03, P-REC-04: require hitting/stopped-process foundations.
- P-QSD-01, P-QSD-03, P-QSD-04: not A. Do not swap P-QSD-01/P-QSD-03.
- P-BRG-01 includes concentration/extinction/maximizer-relative-mass clauses,
  not merely its recurrence.
- P-API-01 requires process-interface composition and a TV defect bound.

## Closed lanes

Do not reopen without a substantive source mismatch or CI regression:

- all 59 P-IDs listed in `V3_COVERAGE_STATUS.md`, including P-INT-01,
  P-INFO-03, P-ID-02, P-OMG-01, P-OMG-02, P-DDH-01 and P-ALI-03.

## Public canonical-source synchronization

The exact canonical source bytes are still not present in the public repository.
For self-contained third-party reproduction:

1. synchronize exact bytes without regeneration;
2. independently recompute SHA-256;
3. verify the frozen manifest value.

This task is separate from theorem proof status.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, GitHub Issue #56,
   `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch current main SHA and active branches/Actions state.
3. Distinguish source audit, theorem closure, official import reachability,
   feature CI, integration CI, main integration, post-main CI, ledger counting,
   and public-source reproducibility.
4. Read the frozen source statement before writing Lean.
5. Audit existing main code before adding infrastructure.
6. Never use `sorry`, `admit`, unsourced axioms, `native_decide`, or
   kernel-skipping devices as proof completion.
7. While CI runs, advance another independent source audit/proof lane.

## Repository truth hierarchy

1. frozen canonical source specification;
2. `docs/V3_COVERAGE_STATUS.md`;
3. `docs/PID_STATUS.yaml`;
4. GitHub Issue #56 for live construction intent;
5. `docs/FORMALIZATION_STATE.md`;
6. official imported Lean source on `main`.
