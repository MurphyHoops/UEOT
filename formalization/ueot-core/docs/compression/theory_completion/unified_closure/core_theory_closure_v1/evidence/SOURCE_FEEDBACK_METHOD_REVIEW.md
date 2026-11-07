# Actual-source feedback: independent method review

## Status and source identity

The coordinator reported successful actual Lean compilation of
`SourceCohortFeedback.lean` (revision prefix `1afaa`) and
`CoreRegenerativeFeedback.lean` (revision prefix `8f8b`) on 2026-11-06.
Those two files are frozen pending public integration. The compiled consumer
calls `CoreRegenerativeSource.programStep` directly; it does not take a mean,
variance, fitness, recovery success certificate, or optimality assertion as a
source-constructor argument.

The independent exact checker is `source-feedback-probe.py`. It imports
`source-prototype.py` and binds its actual bytes in its JSON output. The source
probe hash for this run is
`793c3da74167d51d42f4c8410ee2b3a8b941200b2bd04538a96ad71b077b9203`.
The JSON contains every one of the 65 checked horizon moment records and repeats
the selected horizon's exact rational means and variances. The checker is a
separate exact executable check of the source specification; the Lean claims
come from the actual compiled source and tree consumers. This execution is not
empirical support. Empirical status remains **UNVERIFIED**.

## Which premise was removed

The finite probability lemma permits explicit atom weights and moments, as a
general algebraic theorem should. The actual-source consumer removes those
premises by constructing the following objects from the same transition:

1. A depth `T` finite tree whose node carries the source's 36-atom primitive
   noise. Its two recursive slots are exactly the actual result's retained
   option and newborn option. An unoccupied slot contributes zero and its noise
   remains unused. Each newborn first acts at the next recursive round.
2. The product atom weight, proved positive and normalized from the primitive
   source weights. There is no conditioning away of deaths or failures.
3. The literal terminal count, bounded samplewise by `2^T` per founder; the
   actual number of processed parents is at most `2^T - 1`.
4. A finite expectation recursion obtained from actual retained/newborn events.
   It yields, for every program `theta`, initial body `i`, and `T >= 0`,

   `E N_theta,i(T+1) = k_theta(i) lambda_theta^T`.

The row is `M_theta(i,j) = k_theta(i) nu(j)` with
`nu = (1-q,q)`. It is computed from the primitive survival, birth and damage
outcomes. The body code is faithfully copied, so the program-family population
matrix is block diagonal. Primitivity applies to a fixed program's body block,
not to the whole faithfully inherited family.

## What the finite feedback theorem says

One cohort contains one healthy founder of each actual hereditary program.
Let `L_T` count the lower-growth program and `N_T` count all descendants. Their
actual-source means are `nu_T` and `mu_T`; `mu_T > 0`. Independent, separately
funded copies of the whole cohort give a finite `n`-fold product law.

For `0 < epsilon <= 1`, the theorem proves

`P[N=0 or (N>0 and |L/N - nu_T/mu_T| > epsilon)]`
`<= 9 (Var(L_T)+Var(N_T)) / (n epsilon^2 mu_T^2)`.

The zero-population event is explicitly a failure. The constant follows from
the good event that both numerator and denominator differ from their means by
at most `epsilon n mu_T/3`. The denominator is then at least
`2 n mu_T/3 > 0`. The variance of each independent cohort sum is proved to be
exactly `n` times its one-cohort variance.

The same source gives `lambda_0 < lambda_1`, and the normalized mean share of
the lower program tends to zero. The order of choices is explicit: first
choose a finite horizon `T` with mean lower share at most `epsilon/2`; then
choose the number `n` of independent cohorts. The probability of extinction or
a realized upper-program proportion below `1-epsilon` is at most

`36 (Var(L_T)+Var(N_T)) / (n epsilon^2 mu_T^2)`.

This is a finite-horizon actual proportion result. It does not assert almost
sure eventual selection for any fixed finite founder population. In particular,
it does not turn a positive expected growth rate into certain survival.

## Exact numerical consumer and its resource bill

The executable check uses

`s=3/4, delta=1/8, b=3/8, gamma=1/4, q=1/3`.

The actual action rates are `k_care=9/8`, `k_bloom=5/4`; the hereditary program
growth rates are `lambda_0=9/8` and `lambda_1=29/24`. Thus, for the two healthy
founders and `T >= 1`,

`mu_0(T) = (9/8)^T`,

`mu_1(T) = (5/4)(29/24)^(T-1)`,

`mu_0(T)/mu_1(T) = (9/10)(27/29)^(T-1)`.

For `epsilon=1/5` and `eta=1/10`, the first acceptable horizon is `T=31`.
At this horizon:

| Quantity | Approximate value; exact rational is in the JSON |
|---|---:|
| Lower-program mean | 38.5237180689 |
| Upper-program mean | 365.184804983 |
| Total mean | 403.708523052 |
| Lower-program variance | 4336.65940735 |
| Upper-program variance | 232855.487013 |
| Total variance | 237192.146420 |
| Mean lower-program share | 0.0954245845 |

The checker calculates second moments from actual output records. Conditional
on a source atom with occupied child slots `y_1,...,y_k`, it uses

`E[X_next^2 | atom] = sum_j E[X_yj^2] + 2 sum_{j<l} E[X_yj] E[X_yl]`.

The cross term is justified by the independent future subtree tapes; it is
not inserted as an unexplained covariance premise. The two founder lineages
are independent, hence `Var(N_T)=v_0+v_1`, and the numerator for the selection
bound is `v_0+Var(N_T)=2v_0+v_1`.

Choosing `n=13,338` yields the exact rational failure bound approximately
`0.0999965217529`. This number uses the exact computed moments. It does **not**
come from the much coarser `D^T` variance bound. The latter is what establishes
finite existence with minimal probability machinery in Lean.

Every actual old individual brings its existing one-unit wallet and receives
five explicit environmental units. Every retained/newborn wallet is debited
from that local balance. With two founders per cohort, the source proves

`initial capital + all actual inflow <= n [2+10(2^T-1)]`.

For the numerical example this worst-case bill is
`286,431,368,863,536`. It is a conservative worst-case requirement; it is not
the expected bill and is not advertised as a feasible small-budget experiment.
If a real global budget is smaller, this bound supplies no success certificate
for that budget. No shared wallet is silently replaced by independent purses.

## Same-source negative results

The independent check obtains the one-step count distributions from actual
output records:

| Program | 0 outputs | 1 output | 2 outputs |
|---|---:|---:|---:|
| `theta_0` | 5/32 | 9/16 | 9/32 |
| `theta_1` | 9/64 | 15/32 | 25/64 |

For one healthy founder of each program, under their independent noise law:

| Actual statistic | Exact value |
|---|---:|
| Total population is zero | 45/2048 |
| Higher-growth program is zero, lower program is nonzero | 243/2048 |
| Expected higher-program fraction, explicitly extended by zero at zero population | 2095/4096 |
| Expected higher-program fraction conditional on nonzero population | 2095/4006 |
| Higher-program mean count divided by mean total count | 10/19 |

The three proportion values differ. The early-extinction event proves a
finite source counterexample to unqualified survival or realized-selection
claims. It does not show that the remaining lower-program population survives
forever. Faithful inheritance does ensure that a lost higher-program lineage
does not reappear without an additional, separately specified introduction.

## Red-team conclusions and remaining boundaries

- A rejected underfunded request retains the old organism, creating a genuine
  identity row. This behavior is preserved. The public positive class includes
  `s+b>1`, allowing the actual growth potential to dominate refusal/stalling.
  An argument that merely drops rejected requests would miss this case.
- The resource-limited action row remains real: on a damaged body,
  repair costs three, care costs one and two possible output wallets reserve
  two, reaching the six available units; bloom would require seven and rejects.
- The allowed diagnostic reads physical code cells and the gate, not the hidden
  ancestry label, fitness or a future atom. The trusted majority/bootstrap
  boundary is finite and explicit. Total code erasure is a separate exact
  non-identifiability boundary.
- The fixed-program count formula holds for the damaged initial body as well:
  the first rate is then `9/8`, followed by the same `lambda_1` growth factor.
  Thus a common damaged-initial-state regeneration/growth witness can use the
  same program and six-unit transaction. The two-founder numerical feedback
  example deliberately starts healthy and does not itself stand in for that
  common damaged-state witness.
- Independent cohort concentration requires independent source tapes and
  separately accounted local endowments. A shared weather variable or common
  wallet would need a different source proof; no such extension is claimed.
- Expected count growth, survival, actual census fractions, Perron-weighted
  ancestry, allowed control, and normative value remain distinct statements.

## Actual native export verification

The independent checker `check_native_source.py` subsequently read and verified
the coordinator's actual Lean export, not a mock. The input has 965,141 bytes and
SHA-256
`af8e82ff6a6f4b227cf4421b4b112a54c26fa3b071e16a8bf47497aeacada75b`.
It binds the source revision
`75e76b0673918186de3aac253e0c4810f9bd4895236f150d408cf27a9a8ed793`
and the native runner revision
`3c77f685af31126fdc54a530788f42a3311b1b0e39cb8c321a8cd4f5e395d44d`.

The actual input passes 864 complete request-port records and 288 complete
internal-program records, with exact Cartesian coverage. The comparison includes
all physical code cells, gate, bootstrap and silent tag; request caps and fees;
retained/newborn slots; permanent identities, actual parent pointers, birth times,
execution ages and the complete marked ancestry list. A real two-round run
produces 2 -> 4 -> 8 records, with no newborn acting in its birth census.

All 5,508 checked financial prefixes are nonnegative, with minimum zero. The
records contain 720 executions, 288 stops and 144 rejections. The two-round
resource totals are inflow 10 then 20, fees 5 then 11, refunds 3 then 5, and
terminal wallets 4 then 8. The checker derives L, B, M, both growth rates, and
the exact probability counterexamples above from the native output records.

The actual runtime source is also inspected: `programStep` tests the affordable
physical request, then reads the restored active code through `rawExecute`, and
only then passes the selected actual action and the private source atom to
`executedResult`. Its request and repair functions do not receive an intended
theta label, a mean, fitness, hidden tag or raw noise. This is a narrowly scoped
source-interface check, supplemented by the complete event-record comparison.

Five intentional record corruptions are rejected: an incorrect cap, a fabricated
newborn parent, age advancing on rejection, an incorrect inherited physical cell,
and conflation of retained/newborn ancestry marks. These negative controls do not
substitute for the real-input pass. The exact report is `native_source_check.json`.

The native records also distinguish two notions sometimes called survival. For
the same healthy theta_1 body, care retains its original identity with probability
3/4 and bloom with 5/8. However, the probability of at least one next-census
individual is 27/32 for care and 55/64 for bloom. Thus the precise counterexample
is growth optimality versus **one-step continuation of the same identity**;
one must not silently substitute population non-extinction.

