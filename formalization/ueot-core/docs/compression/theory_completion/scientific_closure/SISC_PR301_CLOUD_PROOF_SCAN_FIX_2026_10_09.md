# SISC PR #301 — Compression Guard comment-token regression

Date: 2026-10-09. Scope: **comment-only**, no Lean theorem statement or
proof term changed. Original cloud head: `efac5f5aad5612250cb5a822c1b68b408244c706`.

After pushing the first immutable-base-policy-authorized PR candidate,
GitHub Compression Guard passed authorization, classification and governance,
but the proof-escape scan failed because its exact `grep -RInE` pattern
matches the English word `admit` **inside Lean prose comments**. Three new
SISC files included that ordinary word; all actual Lean source declarations
and proofs had previously compiled successfully and selected axiom surfaces
had no nonstandard assumptions.

The only three Lean changes substitute equivalent prose:
- `SISCStochasticDescent.lean`: "need not admit a Markov" → "need not support a Markov";
- `SISCLinearPredictiveLift.lean`: "need not admit any" → "need not support any";
- `SISCInterventionTransferExamples.lean`: "admit BOTH parents" → "allow BOTH parents".

The V12 local gate now checks the **same cloud Compression Guard textual
predicate** over every first-party Compression Lean source in addition to
the previous proof checks. It protects every archived V1–V9 source inventory
unchanged, records the current source state in V10, and verifies that each
of the three comment-only files is **exactly** the corresponding source
from the first pushed PR head with only its single named prose substitution.

This is a strict regression improvement, not a weakening of the source
escape policy. It makes no scientific/experimental status promotion. The
independent external evidence gates remain **OPEN/HOLD**.
