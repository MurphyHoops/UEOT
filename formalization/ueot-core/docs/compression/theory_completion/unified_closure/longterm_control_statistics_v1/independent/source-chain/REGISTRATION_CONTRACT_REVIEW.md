# Native candidate to registered overlay: independent consumer-contract review

## Decision

The proposed separate registration step is sound. Preserve the raw native-produced candidate overlay byte-for-byte; construct the registered overlay by adding exactly two top-level metadata keys, `lexical_pr_preflight` and `registration_provenance`. The fixed Lean verifier and native JSON must be copied byte-for-byte. The registered overlay receives its own new SHA256. The raw candidate's SHA remains a separate provenance fact, not the registry digest for the augmented object.

No production theorem, raw proof dependency, native axiom record, type-comparison count or PASS state may be rewritten by registration. The registration step must not convert a failed or incomplete actual native run into a successful one.

## Exact current consumer requirement

`knowledge/reuse/fkrg_reuse.py:556` directly indexes:

```python
overlay["lexical_pr_preflight"]["new_theorems_with_lexical_reuse_candidates"]
```

This is the only lexical metadata field the current `status()` requires directly. Omitting the lexical object causes a `KeyError`; the native result itself is not defective for having produced an execution-only candidate before registration. `load_overlays()` additionally retains its existing schema, predecessor-chain, base module count, zero-defeq and exact proof-edge count checks. `_parse_data()` and freshness checks still require the exact added-module rows, source overrides, theorem rows and immutable prior evidence.

The other lexical fields below follow the established overlays' honest reporting convention; they are not a substitute for the mandatory later Git-object PR preflight.

## Recommended metadata

Use values derived from the actual `SOURCE_PREFLIGHT.json` and verified source scope:

| Field | Current value |
|---|---|
| `baseline_ref` | `ff71e63256c88ad2bb527fdd3004d55c77894ab7` |
| `candidate_ref` | `null` until the separate immutable candidate commit is checked |
| `candidate_scope` | Frozen worktree source; actual Git-object PR preflight remains separate |
| `base_lean_module_count` | 666 |
| `candidate_lean_module_count` | 678 |
| `base_public_lexical_theorem_count` | 4147 |
| `candidate_public_lexical_theorem_count` | 4237 |
| `new_public_source_theorem_count` | 90 |
| `historical_public_repair_count` | 0 |
| `overlay_public_registration_count` | 90 |
| `new_theorems_with_lexical_reuse_candidates` | `sum(bool(row['reuse_candidates']) for row in hints)`; independently recomputed current value 27 |
| `candidate_source_tree_sha256` | `60cd5f8ab161c5b51394463c466947a4c6a6c1742ecdcd9c2bbfc41c0c06bd31` |
| `registered_prior_public_source_theorem_count` | 4147 |
| `candidate_registered_public_source_theorem_count` | 4237 |
| `note` | Lexical hints and raw stored-type equality do not replace semantic review; the commit preflight is separate |

The independent recomputation used the exact Git-base parser code with SHA256 `6d9ee21b7c832aa238c7fd2b42cd5aa9085bc3af616df16819aa100d82f9213c`, the unchanged `candidate_hints` algorithm, the actual immutable-base corpus and current source bytes. All 90 hint rows and the 27 nonempty groups are retained in `REGISTRATION_LEXICAL_RECOMPUTATION.json`. Do not replace a computation by the expected number 27; compare the actual preparation rows with this independent result.

## Registration checks

1. Require the actual final native status to be exactly `PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION`, with both subprocess result codes zero. A substring containing `PASS` is insufficient.
2. Verify the raw candidate, fixed verifier and native JSON hashes against actual `STATUS.json.summary` and the candidate's own evidence fields. Verify source/base/public/module scope against `SOURCE_PREFLIGHT.json`. Preparation's `PENDING_ACTUAL_NATIVE_EXECUTION` label is historical and should not be rewritten; actual execution status lives separately.
3. Recheck the complete first and fixed native JSON objects are equal. Candidate theorem names must match preparation and native public names exactly, with no duplicates; ownership/path/line data must remain tied to the same prepared sources. Check current counts as derived facts, not replacement evidence.
4. Verify the preparation's source fingerprint equals the candidate checkpoint and current frozen full source fingerprint. All twelve module hashes and the root hash override must agree. Its actual base is ff71, prior modules are 666, prior public names 4147 and prior overlays eight.
5. Check every lexical hint row is unique and corresponds exactly to a prepared public candidate (`symbol` ↔ `name`, path and line). Compute H from the real lists and compare to the independent recomputation. For repeatability, preserve the actual preparation file and its SHA.
6. Refuse input raw candidates already containing either new metadata key. Add both keys to a deep copy. Require `set(registered) - set(raw)` to be exactly those two keys, no key loss, and `registered` with those two keys removed to equal the parsed raw object in every field. This preserves list order and values, while permitting only JSON key-layout differences from serialization.
7. Archive raw candidate bytes and the preparation/status bytes with hashes. Copy verifier and native JSON without reformatting, then compare actual destination bytes and SHA to their source files. The native JSON must still match the SHA embedded in the unchanged raw candidate evidence field.
8. Record `registration_provenance` as a metadata-only augmentation: raw candidate path/hash, preparation/status path/hash, verifier/native path/hash, registration tool hash and the two allowed keys. The native execution driver/hash remains an input provenance fact, not an invented registration execution claim.
9. Existing archive/destination paths are idempotent only if their bytes already equal the expected bytes. Conflicting bytes cause failure; do not overwrite historical evidence. The registration step should compute and validate all intended contents before publishing its final receipt.
10. Pin the augmented overlay's SHA, unchanged verifier SHA and native JSON SHA in the authorized registry flow. Afterwards run live freshness, exact counts and existing tests. The source/native/static review and mandatory base-authorized Git-object parser retain separate receipts.

The finalizer and registered eighth overlay demonstrate this metadata convention at `registered_interfaces/native_protocol/finalize_observed_registered_interfaces_overlay.py:126–152` and `REGISTERED_INTERFACES_REUSE_OVERLAY_V1.json:1214`. Their historical repair-specific values must not be copied into the present zero-repair layer.

## Scope limit

This review validates the proposed metadata transformation and actual consumer contract. It has not inspected the unseen final native execution artifacts or executed official registration. The implementation owner is `/root/infinite_policy`; the reviewer has not edited any live consumer or Mac file.
