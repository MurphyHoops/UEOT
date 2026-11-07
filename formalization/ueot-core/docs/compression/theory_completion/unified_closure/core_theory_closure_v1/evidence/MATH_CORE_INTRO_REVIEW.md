# Independent mathematical review of the proposed Core introduction

Reviewed against `MATH_CORE_INTRO.md`, actual source, finite feedback, population,
control-population, quotient, lineage and formation source files on 2026-11-06.
This is a review of a draft, not an assertion that the publication gates have run.
The coordinator owns all book edits.

## Required wording corrections

1. **Finite kernel versus an infinite-space martingale.**

   The actual endpoints `actual_supermartingale` and `actual_martingale` prove
   nonnegativity and the one-step conditional finite weighted inequality/equality
   at each actual history node. `historyExpectation` gives all finite-horizon
   iterates. These are substantive actual-source results. They do not themselves
   construct a common infinite path probability space or a Mathlib
   `Supermartingale`/`Martingale` instance. Suggested replacement:

   > 在每一有限允许历史节点，W 满足非负性和一步条件均值不增；最优程序取等号。
   > 下称有限条件核意义的超鞅／鞅性质，各有限 T 的期望界由同一核递推。

2. **Individual continuation is not population non-extinction.**

   Replace the broad phrase “增长最优不等于存活最优” by
   “增长最优不等于同一身份的一步续存概率最优”. The actual native source has
   care/bloom original-identity continuation probabilities 3/4 and 5/8, but their
   next-census nonzero-population probabilities are 27/32 and 55/64. The latter
   ordering goes the other way. No permanent-survival comparison was proved.

3. **State the exact quotient endpoint and the finite induction.**

   Current public quotient lemmas include pointwise full `LocalResult`
   commutation for each same raw atom and equality of kernels on lists of allowed
   observations. The latter lemma is not, by itself, a theorem about the entire
   `CoreRegenerativeControlPopulation.PublicReceipt` history policy law.
   If the text claims all finite controlled joint laws, state the induction:
   equal initial allowed histories give the same action law; use the same action
   and raw atom; full receipts commute; append equal public receipts and iterate.
   Either attach the actual consumer theorem or identify the formal endpoint
   scope precisely. Do not rename `history_kernel_two_way` as a general theorem
   for arbitrary representations or arbitrary information-forgetting quotients.

4. **Normalize the lineage stationary distribution.**

   The source uses r=(k_b,k_c), while the normalized left vector is nu. Then
   nu dot r=lambda, so the actual stationary distribution is
   `pi_i=nu_i k_i/lambda`. The notation `l_i r_i` is correct only after choosing
   the compatible Perron normalization `l dot r=1`. State the source formula
   explicitly to prevent accidental use of the unnormalized earlier r.

## Scope clarifications

- The new actual feedback consumer is the open parameterized class with exactly
  the two hereditary programs theta_0 and theta_1. The generic finite probability
  lemma supports arbitrary count observables, but the actual selection consumer
  instantiates the lower-program count. The introduction should not suggest a
  new proof for every finite program family with arbitrary tied maximal blocks.
  The preserved earlier general conditional contracts remain valid.
- In the source resource paragraph, n counts founders. In the feedback paragraph,
  n counts two-founder cohorts. Add the explicit conversion: there are 2n actual
  founders and the initial-capital-plus-inflow bound is
  `n[2+10(2^T-1)]`.
- Faithfully carried tag coordinates make the full `(kind,tag)` expansion
  reducible. Each fixed-tag body block and the body quotient are primitive.
  The lifted vector `r composed with q` is a positive eigenvector of the expanded
  matrix with the same lambda; no whole-expanded-matrix primitivity is asserted.
- The many-to-one endpoint is for the actual optimal-program source and finite
  marked paths. Multiple optimal-program founders can be combined by finite
  linearity and reproductive-value initial weights. This is not an assertion
  that arbitrary hereditary programs share one eigenvalue or spine law.
- The numerical T=31, n=13,338 certificate uses exact second moments computed by
  the independent finite subtree recursion. Lean's simple finite-existence proof
  uses the source count bound `2^T`. The exact numerical certificate and the
  coarse existence estimate should not be identified with each other.

## Confirmed alignment

The following statements match the actual definitions and the verified feedback
consumer: the public positive class is nonempty and parameterized; nonzero
damage, birth and death are present; damaged bloom truly rejects; rejection
preserves the old wallet and body; stop has zero output; newborn wallets are
paid; newborns first act at the next census; copied program decoding is faithful;
source mean and variance are not naked input assumptions; zero population is a
failure in the finite proportion theorem; the horizon is selected before the
cohort count; a fixed finite population has no claimed almost-sure eventual
selection guarantee; the same theta_1 and damaged initial body can serve the
recovery/growth common witness. Empirical support remains UNVERIFIED.

The source formation consumer's explicit nontrivial response is necessary to
prevent a vacuous empty physical carrier. The coordinator and source agent were
already adding the empty-readout positive-defect endpoint when this review was
written; the final text should cite that completed endpoint once verified.

