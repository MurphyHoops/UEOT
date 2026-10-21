# Registered-interfaces native repair protocol

**Prepared and structurally checked; Lean/native execution has not been performed by this agent.** These tools are isolated copies of `native-tools`. The originals, production sources, historical CSV files and frozen `fkrg.py` are unchanged. Root owns execution and registration.

## Why this correction is needed

The actual base has 4,095 public lexical theorems, while the registered graph has 4,094. The unique omission is `UEOT.V3.FreeInformationValue.integrable_finset_sup'`. The old source regex terminates identifiers with `\b`; after the trailing apostrophe it can backtrack and report the truncated name. The historical declaration CSV stores that truncated name as `UNRESOLVED`. The exact public theorem already exists in unchanged source. Its file SHA256 is `e4375851def0e735d54c7d3f56ba48517040e064073fdc1283a006f1d33c1a87`.

This protocol confirms the exact declaration by actual native ownership, visibility, type and axiom closure. It does not claim that the frozen parser has been repaired. It does not describe this historical registration repair as a new mathematical proof.

## Separate scopes

| Scope | Expected count | Meaning |
|---|---:|---|
| Previous registered public graph | 4,094 | Immutable base plus seven existing overlays |
| New public source declarations | 52 | The seven new Lean modules |
| Historical public repair | 1 | The exact omitted existing theorem |
| New overlay registrations | 53 | 52 new declarations plus 1 repair |
| Added source modules | 7 | `added_modules`; the existing file is not added again |
| Full production source identity | 666 | All `UEOT.lean` and recursive `UEOT/**/*.lean` |
| Native audit modules | 8 | Seven new modules plus `UEOT.V3.FreeInformationValue` |
| New declarations × registered graph | 212,888 | `52 × 4094` |
| Historical repair × registered graph | 4,094 | `1 × 4094` |
| Total cross comparisons | 216,982 | `53 × 4094` |
| New × new internal comparisons | 1,326 | `52 choose 2` |
| New × historical repair comparisons | 52 | The previously missing comparison supplement |
| Total internal comparisons | 1,378 | `53 choose 2` |

These are required counts, not observed successes. The generated Lean program increments the actual partition counters inside its comparison loops. All comparisons retain the existing protocol: raw stored compiled types and fresh `liftTermElabM` for each `Meta.isDefEq` call.

The native census exports every owned theorem constant in all eight audit modules, including private and generated declarations. It retains types, universe parameters, direct constants, direct theorem constants, owners and transitive axiom closure. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. The existing public theorem `p_ref_03` belongs to this native census but is not registered again.

## Exact additive proof-edge repair

The first native run scans each of the 4,094 existing registered theorem proof values for the exact omitted name. Every positive caller is exported, including its complete direct constants and actual registered-edge list. The result is not prefilled with one expected caller. Source inspection shows the known `p_ref_03` use; the protocol fails if that known call is not observed and accepts any additional callers actually found.

The fixed-certificate preparation reads each positive caller's prior registered dependency list from the unchanged historical graph and overlays. It requires:

1. The caller already belongs to the previous graph, with the same source owner.
2. The observed new direct dependencies are exactly historical repair targets and are absent from the prior list.
3. The actual complete registered dependency list equals the prior list union the observed delta, with no deletion or unrelated addition.
4. The full native row agrees with the narrow-scan row whenever the caller is in the eight-module census.

The generated fixed Lean verifier repeats the whole 4,094-proof narrow scan and checks the exact observed caller set, each delta and each prior-plus-delta edge set. The runner compares the two complete native JSON objects, not just counts. The finalizer regenerates both source/exporter and fixed-certificate preparations and requires exact agreement with the observed files.

The overlay keeps new-node edges in `proof_dependency_certification`. Existing-node additions are separate in `existing_proof_dependency_repairs` and `existing_proof_dependency_repair_certification`. No historical CSV row is rewritten.

## Build identity and failure handling

`build_identity.py` is byte-identical to the original. The runner still validates the complete 666-module fingerprint and path/SHA list, three pinned environment files, all nine exact clean dependency checkouts, actual Lean/Lake executable identities and versions, the focused/full build receipt, and both real build-log hashes. These checks run before and after native execution and at finalization. The smaller eight-file focused-build manifest is supplemental, not the complete proof-input identity.

A failed comparison leaves the original process log untouched. If the failed Lean run printed a complete native JSON object, the runner also saves that actual object as `observed_failed_native_export.json` or `observed_failed_fixed_verifier.json`. A historical repair collision is not suppressed or converted to a success. Full-build success, native success and canonical authorization remain distinct gates.

## Checks actually performed in this preparation

`STRUCTURAL_CHECKS.json` records Python AST checks, source-name/scope structure, unchanged original files and identity helper, unique template insertion points, and in-memory dependency-delta checks. The synthetic structural fixture deliberately contains an additional old caller, and rejection fixtures cover count drift, duplicate callers, a deleted prior edge, an invented edge, a missing known call and the wrong owner. Synthetic fixtures are never written as native data.

`UNEXECUTED_NATIVE_EXPORT_PREVIEW.lean` contains concrete real names and is only an unexecuted source preview. No `prepare`, Lean, native export, project test or build command was run by this child agent.

## Root execution commands after the actual build is PASS

The last read of attempt 8 was `RUNNING`; these commands are not a report of execution. The runner fails closed until the actual receipt is PASS. Use fresh empty output directories. It must run before the eighth overlay is registered, because its predecessor guard is the real 4,094-node graph.

```bash
python -B /workspace/scratch/9a8d58b21e30/tmp/registered-interfaces-20261021/native-repair-tools/run_native_registered_interfaces_pipeline.py \
  --repo /workspace/scratch/9a8d58b21e30/ueot-integration \
  --output /workspace/scratch/9a8d58b21e30/tmp/registered-interfaces-20261021/linux-native-repair-observed-1 \
  --lake /workspace/scratch/9a8d58b21e30/tmp/registered-interfaces-20261021/linux-runtime/lean-4.33.1-linux/bin/lake \
  --build-status /workspace/scratch/9a8d58b21e30/tmp/registered-interfaces-20261021/linux-build-attempt-8/STATUS.json \
  --build-manifest /workspace/scratch/9a8d58b21e30/tmp/registered-interfaces-20261021/linux-build-attempt-8/SOURCE_MANIFEST.json \
  --build-log-dir /workspace/scratch/9a8d58b21e30/tmp/registered-interfaces-20261021/linux-build-attempt-8 \
  --focused-label new_modules --full-label full_ueot \
  --base-ref 65db00a12d20be41cd6c8befacb9ba2e74a2a8a9
```

```bash
python -B /workspace/scratch/9a8d58b21e30/tmp/registered-interfaces-20261021/native-repair-tools/finalize_observed_registered_interfaces_overlay.py \
  --repo /workspace/scratch/9a8d58b21e30/ueot-integration \
  --observed /workspace/scratch/9a8d58b21e30/tmp/registered-interfaces-20261021/linux-native-repair-observed-1 \
  --output /workspace/scratch/9a8d58b21e30/tmp/registered-interfaces-20261021/linux-native-repair-final-1 \
  --build-status /workspace/scratch/9a8d58b21e30/tmp/registered-interfaces-20261021/linux-build-attempt-8/STATUS.json \
  --build-manifest /workspace/scratch/9a8d58b21e30/tmp/registered-interfaces-20261021/linux-build-attempt-8/SOURCE_MANIFEST.json \
  --build-log-dir /workspace/scratch/9a8d58b21e30/tmp/registered-interfaces-20261021/linux-build-attempt-8 \
  --focused-label new_modules --full-label full_ueot \
  --base-ref 65db00a12d20be41cd6c8befacb9ba2e74a2a8a9
```

The `base-ref` above is the observed build predecessor. It does not grant canonical policy authorization and does not replace a later actual-base Git-object preflight. Root controls sequence/output names and the final canonical gates.
