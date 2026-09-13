# UEOT Core Lean — Live Formalization State

> Recovery entry point. Machine-readable lane state is `PID_STATUS.yaml`.
> Integrated source-count truth is `V3_COVERAGE_STATUS.md`.

Last synchronized: **2026-09-13**

## Environment

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`
- exact canonical bytes in public repo: pending synchronization

## Current checkpoint

| operational state | count |
|---|---:|
| integrated proved | **61** |
| active source-facing proof lanes | **2** |
| blocked | **0** |
| pending/audit queue | **43** |
| total | **106** |

The authoritative source-level ledger is **61 proved / 45 not yet counted**.

## Latest counted promotions — P-COMP-03 / P-KL-01

### P-COMP-03

Frozen source: finite nonempty cut family; each `K_pi` is `L_pi`-Lipschitz;
`Gamma_comp(T)=min_pi d(T,K_pi T)`; the exact constant is
`1 + max_pi L_pi`.

- theorem `UEOT.V3.CompositionMargin.p_comp_03`;
- feature `formal/pcomp03-composition-margin@7e074e694c26e52901342336b5e57b666df4fa8c`;
- feature CI `34752374454`: success.

### P-KL-01

Frozen source: for `Q ≪ P0` and measurable event `A`, full-law KL dominates
the Bernoulli KL of the induced event indicator.

- theorem `UEOT.V3.PathEventKL.p_kl_01`;
- feature `formal/pkl01-event-bernoulli@c691145fc6ef8a1fa9332abebf09f3659a5cb2eb`;
- feature CI `34753031461`: success;
- source absolute-continuity hypothesis retained;
- existing `InformationEventBernoulli` foundation reused rather than duplicated.

### Joint promotion

- clean integration branch `formal/pcomp03-pkl01-integration`;
- integration/main proof commit `08ec1bfa1af3dd1d90ff0d046b8cf3472e16fdf9`;
- integration CI `34753554298`: success;
- post-main CI `34753815801`: success;
- source semantic audit complete;
- prohibited-proof audit clean.

## Active proof lane — P-EVO-01

Frozen source remains preserved explicitly:

- finite parent and offspring types;
- `M=D_b K`;
- `b_i >= 0`, including source-valid zero-growth rows;
- deterministic `p'=pM/bar_b`, with only `bar_b>0` required;
- exact Price selection/transmission decomposition;
- no identification with `E[Z/|Z|]` or another random ratio.

Current branch: `formal/pevo01-price-decomposition`.
Current checkpoint head: `dbf40a016377ad3689e4c88b0d5f67a2a675a9c5`.
Candidate theorem: `UEOT.V3.EvolutionPrice.p_evo_01`.
Last CI `34753626091`: failure only at the double finite-sum commutation line.
Both attempted identifiers `Finset.sum_comm` and `sum_comm` were unavailable in
this import/elaboration context. Next action is to use a verified product-sum or
finite-sum equivalence theorem from pinned Mathlib, without changing any source
semantics.

## Active proof lane — P-COMP-05

Frozen source: finite overlapping regions are canonically Booleanized by their
membership signatures; the nonempty signature cells are exactly the atoms of
the unique least Boolean algebra containing all original regions.

- branch `formal/pcomp05-boolean-atoms`;
- head `7f3c73fc8d801a17b79b86aa9b8c7402344d0562`;
- candidate theorem `UEOT.V3.CompositionBooleanAtoms.p_comp_05`;
- CI `34754028909`: running at synchronization time;
- implementation uses Mathlib `BooleanSubalgebra.closure (Set.range V)` and
  targets the full partition/reconstruction/atom/minimality package, not a weak
  partition-only surrogate.

## Audited next lane — P-KL-03

Existing main infrastructure materially shortens the source proof:

- `UEOT.V3.InformationKernelKL.klDiv_compProd_right_eq_lintegral`;
- pinned Mathlib `klDiv_compProd_eq_add`;
- `UEOT.V3.DynamicsKernel` Ionescu–Tulcea/history infrastructure.

The remaining source obligation is finite-horizon iteration for possibly
history-dependent kernels. Do not count a one-step or homogeneous-Markov-only
surrogate.

## Grounded non-quick fronts

- P-KL-02: event I-projection optimizer and Bernoulli-KL monotonicity;
- P-KL-04: CTMC compensator layer;
- P-KL-05: Girsanov/stochastic integral and observation data processing;
- P-EVO-03/04: Perron–Frobenius asymptotics / martingale foundations;
- P-REF-03: arbitrary signal-space conditional expectation;
- P-DDH-04/05: rank/stacked-Jacobian and singular-value perturbation;
- P-QSD-01/03/04: source-locked distinct non-A results;
- P-BRG-01: includes extinction/concentration/maximizer-relative-mass clauses.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56, `PID_STATUS.yaml`, this
   file, then `V3_COVERAGE_STATUS.md`.
2. Fetch live main, active branches and Actions state.
3. Never reopen counted green P-IDs without a substantive source mismatch or CI
   regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green never increments coverage.
6. No `sorry`, `admit`, `native_decide`, unsourced `axiom`, or kernel-skipping
   devices.
7. Use CI waiting time for another independent audit/proof lane.

## Repository truth hierarchy

1. frozen canonical source;
2. `V3_COVERAGE_STATUS.md`;
3. `PID_STATUS.yaml`;
4. Issue #56 live construction state;
5. this file;
6. official imported Lean source on `main`.
