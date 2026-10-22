# Focused finite-window / Doob chain: compile-09 PASS

Status: FOCUSED_CHAIN_PASS. The coordinating root executed the three modules
sequentially in the actual pinned Mac Lean environment and reported
`FINAL_STATE=PASS`. Each compiler log was empty. The root is retaining and
aggregating the original tool receipts with the batch evidence.

The exact accepted source identities and measured execution times are:

| Module in `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure` | SHA256 | Exit | Seconds |
| --- | --- | --- | --- |
| `SameSourceFiniteWindow` | `61feecf09bd38d2b5497a7be33d073b1c04cd20a3e45a6840af19dd1670af363` | 0 | 4.276018667 |
| `FiniteWindowDoob` | `1bcf2d6baaa55e4ea648d19a78dc490a86b525eaaa109464654184d447544081` | 0 | 3.986290084 |
| `FiniteWindowDoobWitness` | `e37d32b9f5da631392706e60c68d21fcb26491fea1c67614be57afbf6d4b0455` | 0 | 4.082827625 |

The compilation order was the order in the table. This binds the final public
outer-measure reuse proof to both its Doob consumer and the actual
three-state TV witness. The source and declarations were frozen by the
coordinating root after this pass.

## Mathematical content checked in this chain

The source module derives the actual fixed-prefix/final-survival joint mass
from the original causal PMF, then obtains its conditioned initial law,
complete safe-path atoms, safe support and positive-parent transition ratios.
The normalized finite-window row PMF retains its positive-denominator
premise.

The Doob module constructs genuine initial and transition PMFs from the
existing positive right eigenstructure, derives their complete finite path
atoms, and compares those atoms with the same original survival-conditioned
source. The actual three-state witness consumes these source identities and
proves pair-law TV `1/4` despite a genuine left QSD.

The final private filter-event proof uses the public Mathlib outer-measure
pushforward and indicator identities described in
`PUBLIC_REUSE_REFACTOR.md`. It supplies no source identity as an assumption
and introduces no additional public hypothesis.

## Evidence boundaries

The initial draft contract, failed compiler attempts, unexecuted intermediate
candidate and earlier passes remain records of their original source bytes.
Compile-08's batch failure and cached-predecessor limitation remain preserved;
compile-09 is the successful sequential check of the final source chain.

The raw compile-09 tool output was still being copied into the shared
aggregate when this module-level record was written. The exact times and
source identities above come from the coordinating root's actual execution
report. The aggregate retains the original raw receipt and its digest rather
than reconstructing compiler output from this table.

This record certifies the focused three-module execution. Full production
imports, native build, complete-source audits, axiom/export checks and
publication acceptance are recorded by the coordinating root in their own
integration receipts.
