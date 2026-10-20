# UEOT-QM v31.6 integration source review

**Reviewer:** `/root/q316_quantum_doob`. **Disposition:** PASS for the recorded source coverage and integration design. This is a read-only source review; it does not substitute for the combined Lean build or actual audit and witness receipts.

## Main package coverage

An independent scanner erased nested Lean comments and strings, tracked namespace/section scopes, and enumerated the actual module commands. All 22 module files are exported exactly once by `UEOTQM.lean`. Relative to v31.5, the four added exports are ClassicalSector, CorePurificationBoundary, RealLocalTomography and QuantumDoob; no prior export was removed.

The scanner found **459 explicit theorem declarations**, and all 459 names appear exactly once in the public audit request list. The current public list has **573 distinct targets**, with no duplicate target and no removed baseline target. The retained baseline contributes 392 audit targets; the four new modules add **181 targets**: 125 theorems and 56 other named constructions, type declarations, instances and explicitly audited structure constructors.

| New module | theorem | def | abbrev | structure | named instance | `.mk` constructor | audit targets |
|---|---:|---:|---:|---:|---:|---:|---:|
| ClassicalSector | 24 | 10 | 1 | 1 | 0 | 1 | 37 |
| CorePurificationBoundary | 32 | 13 | 3 | 0 | 3 | 0 | 51 |
| RealLocalTomography | 37 | 11 | 2 | 0 | 0 | 0 | 50 |
| QuantumDoob | 32 | 9 | 0 | 1 | 0 | 1 | 43 |
| **Total** | **125** | **43** | **6** | **2** | **3** | **2** | **181** |

All new explicit theorems, definitions, abbreviations, structures and named instances are covered. Both new structure constructors are also covered: `UEOTQM.Classical.Effect.mk` and `UEOTQM.QuantumDoob.InvertibleFilter.mk`. The independent name/kind inventory matches `/tmp/qm316_declaration_inventory.json`; its audit list agrees exactly and in order with the actual `AxiomAudit.lean` list. No additional new audit target remains unexplained.

### Resolved finding: public typeclass instances

The first source read found three explicit named global instances omitted from the initial 570-target list: `terminalFintype`, `terminalMeasurableSpace` and `restrictedTerminalFintype`, all in `UEOTQM.CorePurificationBoundary`. Agent A confirmed that their public availability is intentional: imported users need the quotient carriers' finite-type and discrete-measurable interfaces. Root retained them and added three audit requests. The corrected totals are **573 overall**, **181 new**, and **51 CorePurificationBoundary targets**. Re-reading the actual patch confirmed that all three occur exactly once. No count-preserving renaming or removal was performed.

These figures count explicit named source declarations and the specified constructors. They do not claim to count every compiler-generated projection, recursor, equation theorem or anonymous instance, nor every definition in the old baseline. The 573 total is an audit target count, not a theorem count.

## Four concrete witness scripts

All four files' explicit theorem/definition names were independently enumerated. Their `#print axioms` lists match those names exactly once and in source order, with no overlap with the main package audit targets.

| Concrete witness | theorem | def | audit targets |
|---|---:|---:|---:|
| MixtureExamples | 5 | 4 | 9 |
| SurvivalTwoState | 24 | 6 | 30 |
| RealTomographyTwoRebit | 5 | 0 | 5 |
| QuantumDoobExamples | 28 | 12 | 40 |
| **Total** | **62** | **22** | **84** |

The four scripts are correctly kept separate from the package's 459 theorem and 573 audit-target totals. Their declarations describe retained concrete witnesses; the count is not added to the general package theorem count.

## Axiom parser

`check_axioms.py` rejects duplicate requested names and duplicate actual Lean reports before constructing the result dictionary, so dictionary insertion cannot silently discard repeated entries. Requested and reported name sets must be identical. Each report's axiom set must be a subset of `propext`, `Classical.choice`, and `Quot.sound`. The report regular expression admits line breaks within an axiom list. This review did not execute the script or write `proof-axioms.json`; the actual runtime receipt belongs to root's acceptance run.

## Finite-witness verifier

`verify_finite_witnesses.py` includes exactly the four files above and runs them sequentially. Its default timeout is **600 seconds per Lean invocation**, including the toolchain-version invocation; this is not an overall four-file time budget. A witness passes only when Lean exits zero, every expected declaration has one allowed-axiom report, and the bound inputs remain unchanged.

The verifier checks the actual Lean version against the pinned toolchain. It binds witness bytes, its own source, toolchain/configuration files, and the recursive repository-local QM/Core source-and-olean import closure before and after each actual invocation; it also checks the invoked Lake binary identity at completion. Missing build prerequisites fail the gate. These identity checks do not claim to rebuild an olean from a digest: the ordinary package build is correctly retained as a separate prerequisite. The verifier's receipt explicitly excludes witness counts from main theorem/audit totals.

## CI integration

The Lean job runs the ordinary package build and main axiom audit before the witness gate. The witness step is named **Verify retained finite and quantum Lean witnesses** and calls `scripts/verify_finite_witnesses.py` without overriding its 600-second default. The final always-run artifact step archives the witness evidence directory together with the source manifest, build log, main axiom log and main axiom receipt. Workflow permissions are limited to `contents: read`, and checkout does not persist credentials.

## Binding and acceptance limits

The machine-readable report records SHA-256 and byte size for all reviewed integration files, 22 modules, four witness sources and the supplied inventory. All scanned inputs remained unchanged during the enumeration. CorePurificationBoundary has now been re-read and bound to its author-frozen SHA-256 `53d957159fa6cf743c4e146e7d146385af81b7ec9c5a12204f90e488d870bce4`; its author reports official focused Lake PASS. The independent declaration scan was repeated on this final source and retained the exact 459/573 and 62/22/84 coverage results. Other frozen source hashes remain intact.

Actual combined build acceptance, actual **573/573** main axiom reports and the combined **84/84** four-witness receipt must still be established by the root run. No Lean compilation, source mutation or receipt substitution was performed by this reviewer.
