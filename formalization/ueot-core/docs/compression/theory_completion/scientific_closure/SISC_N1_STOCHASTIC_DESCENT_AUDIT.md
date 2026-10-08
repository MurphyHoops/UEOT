# N1.1 — controlled stochastic quotient exists iff strong lumpability

Baseline `c4dddacdcf1638b6a2772eb7795372f5e707c17e`.
The source `UEOT/V3/FiniteStablePartition.lean` already defines `Stable`
and exact finite `blockMass`; `FiniteStablePartitionQuotientLaw.lean` already
constructs `quotientTransition` from a stable partition. `PAlg01.lean`
already provides a coarsest stable refinement preserving output/reward and
finite-horizon output-word laws. Repeating these as a new UEOT generator
would be double-counting existing formalization.

`SISCStochasticDescent.lean` makes the **reverse implication** explicit:
an exact controlled Markov transition on a *given arbitrary* quotient
reproducing all true block probabilities forces `Stable`. Together with
the old quotient construction it yields a **necessary-and-sufficient**
statement and **uniqueness** of the Markov quotient matrix:

`Stable M S ↔ ∃! Q, ∀ a x z, Q a ⟦x⟧ ⟦z⟧ = blockMass M S a x z`.

Its forward proof explicitly reuses the existing construction; its reverse
proof uses equality of quotient representatives. No extra axiom about the
physical meaning of `S` is inserted. The result is exact and finite,
not a universal measurable-kernel theorem.

**Scientific limit:** equality of present observable labels, or even
equality of all declared response statistics, does not automatically imply
`Stable`. The next task is to identify a genuinely observable sufficient
condition, without assuming block-mass equality in different language.

Status: **LEAN LOCAL PASS (upon root rebuild)**, no changes to 106/106 Core,
Compression counted generator inventory, real-world verification or remote.
