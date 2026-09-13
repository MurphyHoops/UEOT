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

## Current counted checkpoint

| operational state | count |
|---|---:|
| integrated proved | **67** |
| integration/promotion lanes | **0** |
| active source-facing proof lanes | **1** |
| source-audited next lanes | **1** |
| blocked | **0** |
| pending/unclassified | **37** |
| total | **106** |

The source-level ledger is **67 proved / 39 not yet counted**. This ledger
commit itself must pass main CI before 67/106 is called full-green.

## Newly counted — P-COMP-04

Frozen source §15.4: with side information `(C_{1:m},U)`, exact
sufficiency/minimality gives `C_P = g(M_P,U)` and
`H(C_P | C_{1:m},U) ≤ H(M_P | C_{1:m},U)`.

- theorem `UEOT.V3.CompositionParentInformation.p_comp_04`;
- feature `formal/pcomp04-parent-info@d7b3446dcac54f62f7d28a141dd8649793b2586c`;
- feature CI `34757571535`: success;
- clean integration branch `formal/pcomp04-main-integration`;
- integration/main proof commit `412815d611fc3c20e867fdf245fc15fbf1f9266f`;
- integration CI `34758385777`: success;
- post-main CI `34758642764`: success;
- source semantic and prohibited-proof audits: complete/clean.

The source-facing map cannot inspect the child-core tuple; finite alphabets make
the frozen finite-conditional-entropy condition automatic.

## Active proof lane — P-KL-03

Frozen source §22.3: finite horizon; genuinely history-dependent discrete
kernels; exact path-space KL chain rule. For the same initial law, path KL is the
sum of expected one-step conditional KL terms. For different initial laws the
source explicitly adds the initial KL term.

- branch `formal/pkl03-path-chain`;
- `p_kl_03` same-initial theorem green at
  `ad67c92db2e9bf6fce561e16dcd0c9680072731f`, CI `34758129042`: success;
- current proof head `6f3e3e3a458da9ef3324783ae0e9423d48a78814` fixes the two exact errors in
  the distinct-initial extension `p_kl_03_general`;
- CI `34761786961`: in progress at synchronization;
- implementation uses Ionescu--Tulcea finite prefixes, measurable history
  append/split equivalence, Mathlib `klDiv_compProd_eq_add`, and UEOT
  `klDiv_compProd_right_eq_lintegral`;
- do not replace by homogeneous-Markov semantics.

## Source audit lane — P-EVO-02

Frozen target:
`I((F,T);(F',T)) = I(F;F') + H(T)` for finite `T` independent of `(F,F')`
and copied without error. Reuse existing deterministic-copy/product/KL chain
infrastructure before adding new foundations.

## Grounded non-quick fronts

- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds; Euclidean curl-free weakening is forbidden.
- P-DDH-02/03: finite exponential-family calculus and KL variational duality.
- P-KL-02: exact event I-projection requires the sharp infimum and explicit optimizer, including boundary cases.
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis.
- P-EVO-03/04: Perron--Frobenius asymptotics / martingale foundations.
- P-REF-03: arbitrary signal-space conditional expectation.
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation.
- P-QSD-01/03/04: source-locked distinct non-A results.
- P-BRG-01: includes extinction/concentration/maximizer-relative-mass clauses.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56, `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch live main, active branches and Actions state.
3. Never reopen counted green P-IDs without a substantive source mismatch or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green never increments coverage.
6. No `sorry`, `admit`, `native_decide`, unsourced `axiom`.
7. Use CI waiting time for another independent audit/proof lane.
