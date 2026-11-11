# Growth attainment: independent scoped review

Reviewer: native agent `growth_lean_rows`; foundation author, independent reader of the population/attainment consumers.

This is a mathematical and source-interface review. It does not replace the root coordinator’s Lean compilation receipts and is not an external academic peer review.

## Source binding

| File | SHA-256 |
|---|---|
| CoreRegenerativeGrowthClassification.lean | `ce5f6f1119a3a1c209148280200fed532377ba4b28a6745813ab3dcae0bd7dcb` |
| CoreRegenerativeGrowthPopulation.lean | `e69d2ef25be8a7ea0a74bc6e8c7d24580cd1d614691c5e38d9c5292848864b54` |
| CoreRegenerativeGrowthAttainment.lean | `952740533202112b37765f3a887dbe1e65dbee1864f386abb7b3abf759529edd` |
| CoreRegenerativeControlPopulation.lean | `533c9cdedccc2f5016cec438c5fcd9a84f00abd18dcd78c251e21df7ca6441aa` |
| CoreRegenerativeRepair.lean | `17c0306ea6547c9dfb67a45810d26b2ead8de52077b2dc35b7a5388403049e7d` |

## Final binding update

The final `CoreRegenerativeGrowthPopulation.lean` differs from the previously reviewed source only by one `end` immediately before the namespace-closing `end`, closing its `noncomputable section`. Removing that one line reconstructs the previously reviewed SHA-256 `afd16182710109c2b7315fa2460c248399ef8647964297d41d28cd7edfaab2c7` exactly. The foundation and attainment source hashes are unchanged. This update checks that structural correction and the final fingerprints; it does not repeat the unchanged mathematical proofs.

The root coordinator reports actual Mac Lean compilation with exit code 0 for all three new modules, the public import root, and the boundary-check file. The coordinator also reports that `#print axioms` on 15 key endpoints lists only `propext`, `Classical.choice`, and `Quot.sound`, with neither `sorryAx` nor `Lean.ofReduceBool`. Those executions were performed by the coordinator; their final receipts are supplied separately and remain the compilation evidence.

## Findings

No substantive mathematical or quantifier gap was found in the reviewed attainment statements.

1. `UniformExpectedUpper` uses a single constant for all original `Policy` kernels and all finite census times. Its constant may depend on the parameter and initial state. This is the required uniform upper bound even when different horizons select different history policies.

2. `optimalRate_isLeast_uniform_upper` explicitly requires a nonempty initial population. The exact attaining policy has positive two-sided exponential constants; comparison with any uniform upper bound forces its factor to be at least `optimalRate`. This proves exactness without assuming that every permitted history policy has an exponential limit. The empty initial state is correctly excluded from the least-factor assertion.

3. The definition does not explicitly require its constant C to be positive. This is harmless: at time zero, a nonempty initial population forces C to be at least its positive initial count. The proof of leastness needs the attaining policy’s positive lower constant and the competitor’s positive factor, both supplied.

4. `rate_le_of_bounds` does not need an assumption a > 0: its contradiction branch assumes a > b > 0. `expected_growth_unique` supplies positivity of both compared factors. `any_expected_growth_le_optimal` remains correct when its candidate factor is nonpositive.

5. The two program iff theorems use each program’s own positive first-moment ray. They do not require either program’s action map to equal the selected `optimalAction`. Consequently the tie gamma = delta is handled correctly even though the selected action map resolves that tie toward care.

6. The generic `programPolicy theta` statements apply the public stationary request rule to arbitrary canonical populations. They should be described as policy statements in that generality. The inherited-internal-program interpretation is valid at the declared founders: `founder_program`, the unchanged `reachable_program`, and `programPolicy_positive_branch_is_internal` show that all positive reachable branches execute the actual inherited code. The damaged-founder iff endpoints provide the correct concrete program-level result.

7. `same_damaged_program_repairs_and_attains_iff` uses each program’s own actual damaged founder body. `founder_is_same_repair_body`, the unchanged `programStep_uses_paid_repair`, and the actual repair-paid theorem bind recovery and growth to that same body and the existing six-unit transaction. The balance 3 in the repair theorem is the balance immediately after repair, before care and output reservation; it is not a claim that the final transaction refund is always 3.

8. The original request class, public observations, history, correlated real request kernels, original refusal row, identities, hereditary execution, and local wallets are reused. No statement extends the separate selection-feedback constants or claims almost-sure survival.

## Acceptance wording

The proved growth notion is positive two-sided constant multiples of an exponential for the selected/internal policies, together with a common exponential upper bound for every permitted policy. For these attaining policies the usual positive T-th-root limit equals the stated factor; the Lean endpoint currently certifies the stronger constant bounds and factor uniqueness, rather than a dedicated real-root limit theorem. Neither this result nor its critical case asserts optimal expected population at every finite horizon.

The mathematical book should use the damaged-founder endpoints when saying “the existing internal program attains”. This is a wording requirement already supported by the supplied proofs, not an additional research task.
