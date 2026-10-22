# Public PMF reuse refactor

This record preserves a proof-maintenance decision made after the initial
focused Lean passes. It does not replace the original draft contract or any
failed/executed source snapshot.

## Observed issue

The first finite-window implementation included a private generic
filter/map/real-atom calculation because the corresponding existing helper in
`SameSourceConditionedTerminal.lean` is private. That copied helper was
explicitly disclosed in `SOURCE_CONTRACT_V1.md`.

The limited new-source clone diagnostic identified 21 equal normalized
nonblank lines between those private proofs. It did not identify a
mathematical defect. The accepted old source and the existing 68-row clone
ledger were not edited.

## Substantive replacement

The new source no longer re-proves the mapped atom by expanding
`PMF.map_apply`, summing individual source atoms, and splitting both the
filter and image-equality conditions. It now uses the public Mathlib chain

1. `PMF.toOuterMeasure_apply_singleton` identifies the mapped atom with its
   singleton outer measure.
2. `PMF.toOuterMeasure_map_apply` supplies the complete pushforward/preimage
   identity.
3. A small local filter-event lemma uses `PMF.filter_apply`,
   `PMF.toOuterMeasure_apply_fintype`, `Set.indicator_mul_const`,
   `Set.indicator_indicator` and finite-sum scalar multiplication.
4. The actual source consumer performs its own `toMeasure`/`toReal`
   conversion using `PMF.toMeasure_apply_eq_toOuterMeasure` and
   `ENNReal.toReal_div`.

Thus the generic `filter_map_atom_real` helper is removed. Its replacement
stops at outer-measure event identity; the source-specific real-measure
conversion belongs to `actual_conditioned_prefix_mass`. Public theorem
statements, the original experiment and all positivity conditions are
unchanged.

The relevant upstream APIs were checked in the public Mathlib documentation:

- [PMF basic outer-measure and measure identities](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ProbabilityMassFunction/Basic.html)
- [PMF map and filter constructions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ProbabilityMassFunction/Constructions.html)
- [Indicator multiplication](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupWithZero/Indicator.html)
- [Indicator composition](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Notation/Indicator.html)

Actual compilation against this repository's pinned environment remains the
authority on availability and correct use of these APIs.

## Immutable earlier execution identities

| Source snapshot | Observed result |
| --- | --- |
| Window `eba9136fde3cafdcfd6dc23f1fcba9ff8921665d6ed991171f3f80710d8c78d6` | Compile-05 PASS, 4.72129975 seconds, empty compiler log. This snapshot precedes the reuse refactor. |
| Doob `5175fed66f44c17f58d965a21c06a60542a22a5edd9dfc22ac146e22cdb61367` | Compile-06 PASS, 3.9796065 seconds; two unreachable-`ring` warnings were subsequently removed. Compiler log SHA256 `08bb20905d8b865c2876b68a622f69b83401bbee809fe5da375b287a7caffce3`. |

Earlier failed attempts remain in the coordinating execution records. They
are not relabeled as passes by this refactor.

The intermediate Window source
`84fe6a873871282642f13070b309c73b7cfdb942ba6a6a5210b040934ad583d1`
used the outer-measure route while retaining the generic real-valued helper
shell. Its status is UNEXECUTED. It was superseded by the final consumer-level
conversion before submission to the next focused compiler invocation. A
temporary oral reference associating diagnostic-02 with this intermediate
hash was corrected: diagnostic-02's actual JSON binds the final source below.

## Final refactor candidate and limited diagnostic

- Window SHA256:
  `4ce233c0138c17faeb458580c34c7d99985fd3cb0ba9fc3b09884a4d7f655691`.
- Doob SHA256:
  `1bcf2d6baaa55e4ea648d19a78dc490a86b525eaaa109464654184d447544081`.

`NEW_SOURCE_CLONE_DIAGNOSTIC_03.json` was produced with before/after source
identity checks over the 691 observed source modules. It found zero
new-module-related matches under the existing eight-normalized-line rule.
Its SHA256 is
`4028fcab0d15ab1a90565f3adc4bf6573b470e166e6ba014f62a900d1609c85a`.
Diagnostics 01 and 02 retain their original bytes.

That limited result does not stand in for the final full-current clone gate,
and this record does not assign an execution result to the new candidate.
The new candidate receives its own focused compiler receipt.

## Compile-08 result and syntax-only repair

Compile-08 actually failed for Window
`4ce233c0138c17faeb458580c34c7d99985fd3cb0ba9fc3b09884a4d7f655691`:
the newly written function annotation used `ℝ≥0∞` without enabling its
notation scope. Its compiler log SHA256 is
`aa35fbf82e679ffe95d9f7dfe0418a1aca1e65d50f23f9818d29342adc453d23`.
That parser failure prevented acceptance of the new private event proof.

The annotation was changed to the explicit type name `ENNReal`. This is the
only source change in candidate
`61feecf09bd38d2b5497a7be33d073b1c04cd20a3e45a6840af19dd1670af363`.
All theorem statements, assumptions, proof steps and constructions otherwise
remain identical to the preceding refactor candidate.

Compile-08 separately compiled Doob `1bcf2d6...` and the actual witness
`e37d32...` successfully with empty logs. Those downstream compilations used
the previously accepted cached Window `.olean`, so the entire batch remained
FAIL. They do not establish final closure of the refactored dependency chain.
The coordinating root scheduled the repaired Window, Doob and witness for a
new sequential compile-09 pass. Its outcome belongs to its own receipt.

## Compile-09 accepted refactor chain

The coordinating root subsequently executed all three final modules in
dependency order and reported `FINAL_STATE=PASS`, each with an empty log:
Window `61feecf09bd38d2b5497a7be33d073b1c04cd20a3e45a6840af19dd1670af363`
in 4.276018667 seconds; Doob
`1bcf2d6baaa55e4ea648d19a78dc490a86b525eaaa109464654184d447544081`
in 3.986290084 seconds; witness
`e37d32b9f5da631392706e60c68d21fcb26491fea1c67614be57afbf6d4b0455`
in 4.082827625 seconds.

`FOCUSED_CHAIN_PASS.md` records that exact source chain and the pending raw
aggregate-copy status at documentation time. The public outer-measure reuse
proof is now part of this actual focused pass. The earlier attempted-source
identities and failure records above remain unchanged.
