# Primary-agent integration review — v31.11 / book 3.8

This is an internal AI research and integration review, not external human
peer review. The authoritative state remains `physics/qm/status/CURRENT.json`.
The continuous exposition is chapter 67 of both existing physics books.

## Source and delegation identity

The actual entry main was `16a89154183c22030d4526413167d095d94e6890`.
All 155 historical proof/configuration inputs and nine runtime inputs matched
their original receipts. During this iteration main advanced to
`74081ffe13a59f551fa803e229d6cc7455e3f59d` through Core reference-supplement
PR #456. The 18 intervening paths are confined to `core/specifications/`;
the consumed physics and proof dependencies are unchanged. Publication must
overlay only this physics increment on the refreshed main tree. The frozen
Core, its production Lean statements, and the physics interface contract
are read-only. The supplement's downstream-adoption note was read and does
not automatically promote the supplement into a new physics premise.

Exactly three native research tasks were dispatched: A operational semantics,
B microscopic truncation, C robust calibration. They wrote isolated drafts;
the primary agent owns canonical source, book, ledger and integration edits.
A reviewed B, B reviewed C, and C reviewed A, each attacking two strongest
claims. The final B and C integration reviews separately inspect the primary
agent's common-source calculation and evidence identities.

## The interfaces actually connected

| Interface | Upstream object | Downstream consumption and checked identity |
|---|---|---|
| Mathematical event → operational identity | Positive-dimensional finite complex spaces, actual complex-linear CP TNI maps, raw probabilities | A proves all finite auxiliary contexts ⇔ single-system state/effect statistics ⇔ actual map ⇔ unnormalized input-first Choi. Zero events are retained; normalization is not performed before comparison. |
| Microscopic model → original instrument | Spectral direct-sum Jaynes–Cummings/phase controls, independent zero-excitation auxiliary, complete readout | B derives every visible/hidden Kraus and its cutoff preservation. No intertwining or error conclusion is accepted as an input field. |
| Original source → finite conditional target | The same `K0,K1,Kf`, first-failure stop, seven terminal labels, backward effects | The root's calculation invokes the inherited chapter-66 interpreter. Successful-prefix effects are `s^(2-t) I`; failure leaves have zero accepting effect. The source success probability is `s²`. |
| Target → legal robust implementation | Same actual `U0,U1`, same theta and retained reference, matching path order | C and root use one policy fixed by calibration and legal visible history. Conditional path states coincide for every input/reference, making full CQ distance exactly the record TV. A basis permutation is explicitly checked between B's oscillator-first blocks and the interpreter's probe-major convention. |
| Infinite source → finite full record | Joint input budget on `G`, normalized projected input and derived branch intertwining | Complete finite-tree CPTP contraction gives one initial `sqrt(nbar/(N+1))` error, without a step-count factor in the invariant-cutoff domain. This is a paper trace-class proof, not a finite-test extrapolation. |
| Mathematical projection → physical preparation | Actual pass/fail spectral filter | The preparation-failure label remains in the common output. The sharper pass/fail bound and its `sqrt(delta)+delta` sufficient bound replace an invalid use of normalized-projection error alone. |
| Parameter uncertainty → deployment | Joint set for theta, common source relation `s=1-q/2`, legal fixed weights | General residual bound uses `exists w(Dcal), forall theta in C`. Phase/exchange nuisance domains are retained; flags do not independently calibrate source/library gate identity. |
| Prediction → statistical and resource claims | Complete source and compiled records, independent reset contract, frozen synthetic model | Raw ordered flags and holdouts are synthetic. Full preparation/reset/control/readout/record costs remain explicit. A one-time calibration batch is amortized per delivery and is not divided by success twice. |

All actions act as identity on the finite reference. The classical controller
has a fixed finite maximum height, a fixed visible alphabet and observation
fibres. Hidden Kraus indices, unknown true theta, extra in-run parameter
queries, coherent controllers and reused hidden environments are not silently
added. Persistent memory must be included in the carrier or reset independently.

## Concrete result and error accounting

For `q in [12/25,13/25]`, the original source has `s=1-q/2` and
`p_src=s² >= 1369/2500`. Its full leaf alphabet is
`f,0f,1f,00,01,10,11`; the conditional target retains zero blocks at original
failure leaves. The deployment emits the same labels and actual gates.
First-step label-1 probability is `1/2`. The second-step probabilities are
`312/625` after visible label 0 and `313/625` after visible label 1.
The four success-word probabilities are `(313,312,312,313)/1250`.

The exact full-design worst-case CQ error is `1/50`, with a matching endpoint
lower bound for every parameter-independent record law in the declared
information class. Constant half-half weights give `51/2500`. The adaptive
policy's central error is `1/1250`; this is not a pointwise improvement at
every parameter. The minimax lower bound is not transferred to the narrower
realized calibration set. A separate exact counterexample checks that error.

For excitation budget 1 and cutoff 4095, the normalized projection bound is
`1/64`. The complete physical preparation bound is `65/4096`, already
including the projection and failure record. It is counted once. Combined
with the same-source strategy error, the sufficient full-output bound is
`3673/102400 = 0.035869140625 < 1/20`. The remaining `1447/102400` is an
unspent error budget, not a measured hardware margin. Statistical coverage
failure is a probability statement, not another additive trace-distance term.

The actual finite entangled-reference calculation is supported in `G<=1`,
so its cutoff/preparation error vanishes. The nonzero-tail physical-filter
control is separate. Neither finite computation claims to numerically solve
the entire oscillator at cutoff 4095 or prove universal input quantifiers.

## Cross-review corrections and dispositions

| Attack or finding | Actual resolution | Remaining boundary |
|---|---|---|
| Formal commutation might replace strong spectral conservation | B supplies direct-sum self-adjointness and spectral preservation, plus explicit readout Kraus completeness | Device derivation of the effective Hamiltonian remains independent |
| Average-energy nonincrease might be sufficient | Three-level mean-energy-preserving channel sends level 1 partly to level 2 | Positive theorem needs branch preservation or a new leakage budget |
| Physical filter failures might disappear | Retain `prep_fail`, prove the complete pass/fail bound, include its cost | A perfect spectral filter is an extra operation assumption |
| Hidden Kraus refinements or labels might fake equivalence | Compare actual maps at each visible label; hidden indices remain inaccessible | Changing access changes the operational theory |
| Single-slot equality might identify reused-memory hardware | All persistent memory is in the carrier, or auxiliaries are fresh and independent | Arbitrary multitime environment identity is not claimed |
| A context-iff theorem was initially absent from Lean | Final source adds the scalar ancillary embedding and all required iff endpoints; actual compilation/audit succeeded | Full rectangular Test/parallel/quotient/tree coherence remains paper coverage |
| Arbitrary separating functional might have unstated norm | Fix one legal input and one complete-output effect, or require an explicit dual norm | Choi-element residuals are not operational bounds |
| Whole-design minimax might be attributed to a smaller confidence set | Lower bound explicitly uses both design endpoints; smaller-set counterexample retained | No data-optimality claim for the reported interval |
| Ordered gate bases might be compared in different conventions | Root explicitly verifies the oscillator-first/probe-major permutation and all source/path quantities | Floating diagnostics are not uniform interval certificates |
| Marginal mixing might imply memory erasure | Prove sector-marginal contraction and full retained-record trace-distance preservation separately | Whole-oscillator invariant sectors prevent global uniqueness |

The two initial Lean elaboration failures remain archived under
`development-attempts/` with their actual sources and logs. The final accepted
source has SHA-256 `99fd7ecfa58322321269c7504b27923f36e5c7f36fadad6a938b640c78c14f37`.
The historical 25-check root calculation is retained under runtime `prior/`;
the current 26-check calculation adds the explicit basis bridge. These are
different execution identities.

Inspection of the first PR #457 runtime artifact found a receipt-generator
metadata defect: a hard-coded local-agent actor string persisted on GitHub
Actions. Its computations and source hashes passed, but the actor label was
inaccurate. The runner now observes local versus GitHub execution, records
workflow IDs and actual checkout HEAD, and explicitly gives consumed-file
hashes priority over a possibly dirty local HEAD. The original local receipts
and the first remote artifact retain their original bytes; the corrected
runner has a new local seven-command execution and requires its own remote
CI identity. No Lean source or mathematical statement changed in this fix.

## Evidence decisions

- Mathematical: the nine numbered increments are proofs or counterexamples
  in their stated domains. Standard prior results are acknowledged; no new
  natural law or independent selection of complex quantum theory is claimed.
- Machine: one new module, 28 explicit theorems, 43 explicitly named
  declarations, and 80 exported namespace constants actually audited.
  Foundations are only `propext`, `Classical.choice`, `Quot.sound`.
  P-OPT-02 has named equivalence bindings; P-OPT-03 has only sequential/sum
  congruence bindings. Trace class, infinite dynamics, robust proofs and
  full OPT are not promoted by a nearby build.
- Computation: seven actual runtime commands; separate exact operational,
  microscopic, independent-certificate, independent-B and root controls;
  floating diagnostics identified as such. Current inputs, outputs and logs
  are checked against the execution receipt before publication.
- Empirical: no actual device or external raw measurements were acquired.
  The 80000 calibration flags and two 4096-record holdouts are explicitly
  synthetic. The correlated-shot control fails iid coverage as intended.
  The record testers do not measure arbitrary terminal quantum states.
- Publication: both existing books have chapter 67 added, nine stable IDs
  appended, all 173 old result objects and 96 old ledger claims preserved.
  Actual PDF source/build/log/visual identities are separate from scientific
  evidence. Unchanged historical heavy suites were not rerun locally.
- Remote: only the observed integration receipt may claim branch, PR, CI or
  main acceptance. Local PASS alone does not confer remote verification.

## Independent inputs and next acceptances

Complex Hilbert structure, Born statistics, CP instruments, tensor
composition, excitation operator, effective JC controls, auxiliary
initialization/readout, exact common-source gate identity and a spectral
filter are explicit physical/model inputs. Finite energy, finite protocol
height, finite untouched reference and iid fixed-parameter calibration are
explicit domain/statistical premises. This increment does not reduce the
independent complex-sector selection responsibility.

The next microscopic acceptance is a complete-record bound from explicit
nonconserving leakage or a finite Gaussian-bath approximation under the same
intervention slots, with prefix-mass-weighted defect/energy budgets.
The next operational acceptance is a complete finite Test quotient with
parallel/coherence laws and an independently justified selection principle.
The next empirical acceptance requires authorized protocol-matched raw
calibration, ordered failures/leakage, source/library gate-matching evidence,
terminal testers, fresh-reset evidence and measured full costs.

The existing ROADMAP retains memory/long-time limits, regulated fields,
complete same-order EFT observables, rank-one FCNC holdout relations,
three-/five-colour and representation countercandidates, and the restricted
Fisher/Lorentzian obstruction plus a concrete curved-background probe model.
No line is marked complete merely because the first finite shared model ran.
