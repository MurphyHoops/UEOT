# Final independent static source and native-protocol review

## Decision and exact scope

**STATIC MATHEMATICAL SOURCE REVIEW: CLEAR.** The twelve added production modules have 91 lexical public theorem/lemma candidates. The complete current source scope is 678 modules, with fingerprint:

`692626c6e91e1513843a6a6c8a37585c810d39ce2efd009e3a4aa347a022b8f5`

I independently recomputed that fingerprint in the cloud checkout. It matches the fingerprint root reported for actual `full-build-02` (exit 0, 19.151 seconds). I did not read the Mac log bytes or execute Lean myself; root's actual execution evidence and this independent mathematical/source review are separate scopes. The immutable governing predecessor is `ff71e63256c88ad2bb527fdd3004d55c77894ab7`.

**STATIC NATIVE PROTOCOL REVIEW: CLEAR**, bound to:

- `integration_native.py`: `d4708782bbb14360002f119715ba51f96c05e2e632694ba64c56c3d38ce8a924`.
- `full_build.py`: `132b1c96d38a4462ef407ee31ed94378c2025996b2a7b603e297fd9d35cf86de`.

This is not a native execution PASS. Root is retaining the actual earlier native attempt and running the final protocol in a new output directory. Final actual exports, fixed-verifier equality, axiom/type results and live registration remain separately reviewable when returned.

Machine-readable bindings:

- `FINAL_SOURCE_STATIC_REVIEW.json`: twelve source hashes, all public names, complete fingerprint and driver hashes.
- `CHAIN_REFACTOR_STATIC_REVIEW.json`: exact permitted transformation from the eight immutable archived sources.
- `FINAL_CLONE_STATIC_REVIEW.json`: unchanged scanner algorithm on all 678 current sources, exactly reproducing the immutable 68 rows.
- `NATIVE_PROTOCOL_STATIC_REVIEW.json`: protocol checks and the actual optimized-Python rejection check.

## 1. Same-source chain refactor

All original 56 public mathematical endpoints are retained. One generic public helper is added, yielding 57 chain candidates. `SameSourceConditionedTerminal.pmf_map_injective_atom` now owns the single original proof; `SameSourceQSDBinding` imports and uses it, deleting its identical private proof. This is a real use by the QSD proof, not an extra theorem alias created merely for naming. The helper's statement and proof body are the original injective-PMF-atom calculation.

I compared the old Git-object code with the current sources after nested-comment removal and separate handling of imports/`#print`. For the two changed modules, the comparison applies exactly the declared helper visibility/name change and deletion/reuse transformation. Every remaining mathematical token matches. The other six modules still have identical mathematical declarations and proofs to their archived inputs. The promotion manifest's production hashes match every current file.

The essential assumptions and meanings from the earlier source audit remain unchanged: original unnormalized initial safe mass, actual finite path experiment, time 0 and initial failure, actual conditioned terminal under positive survival, same killed Q in QSD, first-exit indexing, full state-prefix transport to the same infinite path measure, and decreasing-event continuity to never-hit mass. No positive infinite-survival conclusion, arbitrary-history stationary reduction, or finite-window Doob equivalence was introduced.

The previous eight-line private-helper clone is gone. A later redundant pure-PMF support argument in `InfiniteSupportViability` was genuinely replaced by `PMF.support_pure`. The final independent complete-scope diagnostic returns the same 68 records as `CLONE_CANDIDATES_68.json`, in the same order and with the same fields; no delta file or historical rewrite is needed for the frozen current source set.

## 2. Infinite policy: proof review

Source hash: `57bd13aae378429d71bb3c6f9094d0f837378d7127924b51a15e7e8b65e71757`.

The terminal equivalence is a genuine quantifier strengthening with fixed inputs:

\[
\bigl(\forall T\;\exists\pi_T\;\forall n<T:\ U_n(\pi_T)=0\bigr)
\quad\Longleftrightarrow\quad
\bigl(\exists\pi_\infty\;\forall n:\ U_n(\pi_\infty)=0\bigr).
\]

`p₀`, `q`, the whole time-dependent transition sequence `P`, and the whole time-dependent certification predicate are explicit parameters outside both sides. `InfiniteViable` contains only all finite-horizon viability predicates; it contains neither a policy nor the desired all-time occupancy conclusion.

The local selection argument is correct. For each fixed time and support, an action is in `Dₖ` when it certifies the support and leaves all nonempty observation successors viable for k further steps. `viableWith_horizon_pred` gives nesting. If every one of finitely many actions failed at some depth, the maximum of those depths would make one `Dₖ` empty, contradicting all finite-horizon viability. The chosen action consequently preserves all-horizon viability for every nonempty successor.

The total causal policy uses that one chosen pure action on viable histories and the supplied complete `πbase` elsewhere. The supported-history induction is performed on this constructed policy's own `coarseLaw`, using the old exact support characterizations. The existing `zero_uncovered_iff_support_certified` is then instantiated with that same policy and original source. No limit of unrelated finite policies, foreign deployment law, or hidden reference-path equivalence is used. The reverse direction simply reuses the single infinite policy at each finite horizon.

Finite X and A and the existing singleton measurability assumptions are retained at the actual occupancy endpoint. Y has no added finiteness or measurability assumption. The first viable step supplies an action; the total fallback is explicit. The source may be nonautonomous.

This module does not yet construct the finite-support greatest fixed point, prove the finite-memory cardinality/stabilization theorem, or connect the alternating two-state memory example to Lean. It also does not identify the new policy with a previous finite `viablePolicy`, compress reference-Q checks on source-null histories, or derive physical safety without its extra conditions. These limits are stated in its source documentation and must remain visible in release claims.

## 3. Rowwise SISC: proof review

| Module | SHA256 | Public candidates |
|---|---|---:|
| RowwiseProbeSampling | `24f389bd6fe31c8c62758edf38e1badc3e3148851bac0b9d23d3ee54bd002c26` | 4 |
| SISCRowwiseProbeCalibration | `794aa7051f2457ba4c14fad0b2568563e8471aca0489267c223fcac10c64d1e8` | 7 |
| SISCRowwiseProbeWitness | `4524aad99685a7e50364ccea61468d96f55071d1060cb32b07a07e5a2773a5b0` | 16 |

### Sampling and common event

Every row count `N j` is fixed outside the probability experiment and positive. The general theorem requires rowwise independence and correct individual sample marginals under the same μ, not independence across rows. It applies the existing scalar two-sided Hoeffding theorem to each [0,1] outcome and then a finite probe union bound. It correctly obtains

\[
\mu(G^c)\le\min\left(1,\sum_j2e^{-2N_j u^2}\right),\qquad u\ge0.
\]

`coordinateGood_measurable` proves the common event measurable. The explicit sigma-indexed product experiment supplies the required marginal/independence hypotheses and additionally has cross-row independence. Empty probe registration is allowed only at the generic calibration level and is explicitly separated from N3's nonempty field. This is scalar mean calibration; it does not substitute the older total-variation budget or justify adaptive counts/stopping.

### N3 matching, intervals and identification

`RowwiseCoordinateLawMatchesKernel` asserts the independently required coordinate-level population-mean match with the same original `kernel/source/action/read`. `rowwise_population_risk_eq_registered` derives the full L1 candidate-risk identity from that premise. It does not assume its final target equation as a field. The predictions are exactly the old protocol table.

The constructed interval changes only its estimate and radius. Its estimate is the sum of coordinate absolute mismatches; statistical radius is `|J|u`, drift radius is zero. Kernel, source, action, predictions, registration, causal predicate, tolerance and `observed_nonempty` persist by record update. Neither the interval constructor nor the resolver receives the unknown true candidate.

On the same Good, the deterministic finite L1 Lipschitz bound controls every candidate. No candidate-count union is introduced. The existing uniqueness theorem consumes the actual new interval with the required inside and outside margins, including the factor `2|J|u`. The failure bound follows from containment in Good's complement. The registered candidate type need not itself be finite at the general calibration endpoint.

### N6 audit and source identity

The separate N6 constructor preserves registration, reference response and authenticated-transfer predicates while constructing the observed coordinate averages. The correctness theorem explicitly consumes the proposed parent's registration, its authenticated transfer to the considered child, actual mean/reference-response matching, and `LocalResponseGap` against every other parent in the full type. None of these external scientific obligations is manufactured by concentration.

The constructor totalizes observed responses for all children with the supplied record; its comment correctly restricts scientific interpretation to the child whose experiment is used in the theorem. The theorem does not infer that other children share that experiment. Its true parent appears only in correctness premises/conclusion.

### Genuine finite product witness and negative control

The witness has two nonempty probes and fixed sample counts 128 and 256. Every coordinate belongs to a separate product-experiment unit. Its actual row is `PMF.pure false`; the positive protocol uses the same point-mass kernel. Matching is proved, not assumed. The two candidate risks are 0 and 2; the scalar budget is exactly `2 exp(-4) + 2 exp(-8)`, with a proved conservative upper bound `28/45 < 1`.

Both N3 identification and N6 audited-source recovery consume that product law and actual sample hypotheses. The example is a formal finite experiment, not an empirical dataset or a nondegenerate stochastic-data demonstration. Authentication is explicit toy input, not learned from fit.

The negative control changes the declared kernel to the opposite point mass and leaves the actual data law fixed. It proves the mean-matching obligation false and gives an exactly accurate data record that fails calibration of the wrong kernel. This addresses a concrete failed conclusion rather than only reporting an absent hypothesis.

## 4. Native and full-build protocol review

The final driver resolves an immutable predecessor SHA, executes that predecessor's exact reuse-consumer Git object, and retains its code hash. It uses that baseline consumer at both preparation and final prior-graph reconstruction, so registering the ninth overlay does not make reproduction incorrectly treat the new layer as prior. It checks the parser, fingerprint tool, exporter template and build-identity helper against immutable base bytes. Prior source hashes and public names are independently reconciled with the actual base corpus; the eight prior overlays remain hash-pinned.

The full-build driver runs the actual pinned `lake build UEOT` subprocess into a fresh external directory. It preserves stdout/stderr, exit code, duration, log hash, driver/helper hashes and the complete initial identity. It requires exit 0, the real success marker and unchanged final identity before marking PASS. It uses explicit exceptions throughout and contains no Python `assert`.

The integration driver now also checks the received full-build schema, exact base, explicit full command, fixed log name/hash and success marker, then rechecks complete build identity. It refuses optimized Python at module entry. I executed the narrowly targeted negative check `python3 -B -O integration_native.py --help`; it returned exit 1 with `OPTIMIZED_PYTHON_DISABLES_REQUIRED_ASSERTIONS`, before any native subprocess.

The reused Lean exporter imports UEOT and verifies every candidate module is present. Its census enumerates every actual `.thmInfo` owned by every new module, including private/generated theorem constants; each receives `Lean.collectAxioms` and rejection of any nonstandard axiom. It records owners, privacy, stored universe parameters/types and complete direct proof constants. Public candidate names are separately checked for actual theorem kind, owning source module and nonprivate status.

All cross and internal type comparisons use the established raw stored types with a fresh `liftTermElabM` for each `Meta.isDefEq`. At the current 91-candidate scope, required actual counts are 377,377 cross comparisons and 4,095 internal comparisons. These are expected obligations, not yet an observed result in this review.

The first actual native subprocess supplies the observed proof-edge lists. Only then is a fixed verifier written. The fixed verifier repeats the complete census, type comparisons and proof-edge extraction and checks the observed fixed edge sets. The second actual subprocess must exit 0, pass validation and emit a complete JSON object equal to the first. Only after those checks is a candidate PASS overlay emitted. Failed subprocess logs are retained. No synthetic JSON is used as an execution result, and no expected edge total is prefilled as an observed total.

The full build-input identity helper covers every production source file, the three pinned environment files, exact clean checkouts of all nine dependencies, actual Lean/Lake executables and versions, and import-environment settings; identity is rechecked before and after native runs. Root's current full build and all-source root reachability provide the production import gate. Static protocol correctness does not certify an unseen actual native result or resulting main.

## 5. Remaining claims and handoff

The source review found no unresolved mathematical blocker in the twelve-file increment. The two actual protocol-hardening findings were resolved in the hash-bound final driver. Original and intermediate source/compile/failure receipts must remain historical, with final acceptance tied to the final source fingerprint and final driver.

Still separate: final actual native output/certificate review, additive ninth-layer registry and live freshness checks, immutable-base PR preflight, all required governance/FKRG regressions, PR review/merge and resulting-main identity. The current count of 91 is lexical public scope until actual compiler/native confirmation.

The scientific work remains uncounted post-Core research. It does not change the frozen 106 P-ID classification, the four counted generators or the global `NOT_ESTABLISHED` scientific closure status. Infinite consistency has advanced to an actual Lean endpoint; finite-memory realization, the remaining conditioned-path/Doob work, and original C1–C7 responsibilities are not all completed by this increment.
