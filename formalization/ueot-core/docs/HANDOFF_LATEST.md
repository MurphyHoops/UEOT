# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the single live cross-chat construction state. This file
> is the fallback archival snapshot on `main` and is updated only at meaningful
> lifecycle transitions.

## Recovery order

1. read `UEOT_CORE3_LEAN_OPERATIONS.md` from `main`;
2. read GitHub Issue #56;
3. read `PID_STATUS.yaml`, `FORMALIZATION_STATE.md`, and
   `V3_COVERAGE_STATUS.md`;
4. fetch live `main`, active branches, compare state, CI and PRs;
5. use prior-chat reasoning only as a supplement.

## Current lifecycle snapshot

- counted coverage: **59/106**;
- not yet counted: **47**;
- active source-facing lanes: **2**;
- pending unclassified/audit queue: **45**;
- newest counted promotions: **P-DDH-01 and P-ALI-03**;
- clean integration/main proof commit:
  `9bff83a544929a0191596f6a1b9c7c8d2a6f87b7`;
- integration CI `34752277556`: success;
- post-main CI `34752528830`: success;
- source semantic audit: complete for both promotions;
- prohibited-proof audit: `sorry=0`, `admit=0`, `native_decide=0`, unsourced
  `axiom=0` in both new proof files.

P-DDH-01 evidence:

- feature `formal/pddh01-gauge-cancellation`;
- head `71a26d2fce4087fb4c7ed763b42f74118186a739`;
- feature CI `34751815827`: success;
- theorem `UEOT.V3.DualDriveGauge.p_ddh_01`.

P-ALI-03 evidence:

- feature `formal/pali03-coordination-threshold`;
- head `bbb9f7b1cc8f202fedf5d096fe2707f760d83c4a`;
- feature CI `34751936845`: success;
- theorem `UEOT.V3.AlignmentThreshold.p_ali_03` at the frozen Hilbert-space
  level.

Scratch integration branches from staging are not authoritative and must not be
merged:

- `formal/pddh01-main-integration`;
- `formal/pddh01-main-integration-clean`;
- `formal/pddh01-pali03-main-integration`;
- `formal/pddh01-pali03-integration-v2`.

## Active construction lanes

### P-EVO-01

- branch `formal/pevo01-price-decomposition`;
- current head `1a17175b7a7bf2338c5bcc648085bf5e7ef09a30`;
- candidate `UEOT.V3.EvolutionPrice.p_evo_01`;
- explicit frozen-source interface now includes `M=D_b K` via
  `meanOffspringEntry` and deterministic `p'=pM/bar_b` via `nextFrequency`;
- allows source-valid zero-growth rows `b_i=0`; only `bar_b>0` is required;
- latest fix separates the finite numerator rearrangement from the common
  denominator instead of asking `field_simp` to solve both layers;
- current CI `34752778143`: in progress at snapshot time.

If the CI fails, read decoded logs and fix only the exact Lean error. If green,
run prohibited-proof audit and clean-port to latest main.

### P-COMP-03

- branch `formal/pcomp03-composition-margin`;
- head `7e074e694c26e52901342336b5e57b666df4fa8c`;
- theorem `UEOT.V3.CompositionMargin.p_comp_03`;
- feature CI `34752374454`: success;
- source audit: complete;
- exact source constant `(1+max_pi L_pi)` retained;
- next action: clean-integrate to latest main, then integration CI -> safe main
  fast-forward -> post-main CI -> ledger count.

## High-value audit candidate

P-KL-01 is likely A-class because `main` already contains:

- `UEOT.V3.InformationEventBernoulli.map_eventIndicator_eq_bernoulliLaw`;
- `UEOT.V3.InformationEventBernoulli.bernoulliKL_event_le`.

Before opening a lane, match the frozen source `d_Bern(p||q)` conventions
exactly. If semantically identical to the existing measure-level Bernoulli KL,
add only a source-facing wrapper; do not duplicate the indicator pushforward or
KL data-processing proof.

P-EVO-02 remains B/C boundary: existing mutual-information, KL chain-rule and
Shannon-copy infrastructure is relevant, but the exact independent shared-label
product wrapper has not yet been located.

## Exact next action

1. verify the main CI of the ledger commit that records **59/106**; only then is
   59/106 a full green checkpoint;
2. inspect P-EVO-01 CI `34752778143`; decode/fix if red, source-audit and
   clean-integrate if green;
3. clean-integrate source-closed P-COMP-03 onto the latest green main; it must
   not wait indefinitely for EVO-01;
4. exact-audit P-KL-01 against the frozen `d_Bern` definition and existing
   event-Bernoulli data-processing theorem;
5. continue the remaining 45-P-ID A/B/C/D audit while CI runs.

## Important grounded guards

- feature green does not increment coverage;
- P-QSD-01 is the conditional-stabilization/QSD theorem; P-QSD-03 is the
  simultaneous persistence-window theorem; do not swap them;
- P-REC-03/04 need a genuine hitting/stopped-process layer;
- P-REF-03 has arbitrary signal-space conditional expectations; a finite-signal
  surrogate is not source complete;
- P-DDH-04/05 require rank/stacked-Jacobian and singular-value perturbation;
- P-BRG-01 includes concentration/extinction and maximizer-ratio clauses, not
  just recurrence;
- P-EVO-03/04 require Perron–Frobenius asymptotics / martingale foundations.

## Persistence rule

Unfinished code belongs on its feature branch as pushed checkpoint commits.
Current intent/blocker/next action belongs in Issue #56. Formal status/coverage
files change only at actual lifecycle transitions. Never use this snapshot to
override newer live GitHub state.
