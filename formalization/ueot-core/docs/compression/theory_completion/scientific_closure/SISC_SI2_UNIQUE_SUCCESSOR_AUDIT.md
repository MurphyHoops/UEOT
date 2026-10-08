# SISC SI-2 — Non-Circular Unique Operational Successor

Status: **LOCAL LEAN-CHECKED; PUBLIC BUILD PENDING AT AUDIT CREATION**.
Core and C4 scientific status unchanged; no real-world identity established.

## Quantified result

`SISCUniqueSuccessor.lean` introduces an *independent* causal edge predicate
`edge source target`, a registered response prediction and measured candidate
response, and a tolerance `eps`. `AdmissibleSuccessor` is their conjunction.

Under a **pairwise response separation** condition for distinct target
candidates, `dist (observed a) (observed b) > 2 eps`, two admissible target
matches must coincide. Given one independently obtained admissible witness,
`certified_unique_successor_of_witness` gives the existential plus all-target
unique continuation certificate. It never presupposes token equality or
`SameObject`. A finite positive Bool/real response witness compiles.

The *noisy* version uses candidate-wise certified observation error `eta`
and requires true candidate responses to be separated by strictly more than
`2 (eps + eta)`. It correctly accounts for measurement uncertainty; the
corresponding good event is an external estimator/statistical obligation.

## Genuinely excluded and unresolved claims

- Existence is an explicit independently measured edge+response witness; SI-2
  **does not derive it** from lower dynamics. SI-3 will tackle that gap.
- Pairwise separation of *all registered* candidates is not proof that an
  unknown, unregistered candidate does not exist. It needs a coverage audit.
- The conclusion is a **unique registered operational successor**, not
  metaphysical or physical token identity. Mapping this certificate to a
  domain-specific `SameObject` predicate requires a separate noncircular bridge.
- Clone/split, merge/fusion, measurement error above budget, or failure of
  candidate coverage can produce `UNRESOLVED` or `LINEAGE_ONLY`, not a forced
  positive certificate.
- A fixed finite positive witness is a method test, not independent evidence
  from a natural system.

Acceptance requires exact-head focused compile and `lake build UEOT`, public
import reachability, no `sorry`/`axiom`/frozen ledger edits, and a standalone
local stage commit distinct from SI-0/SI-1.
