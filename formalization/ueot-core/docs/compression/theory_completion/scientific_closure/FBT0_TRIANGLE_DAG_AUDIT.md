# FBT0 — Formation / Binding / Transport Theorem-DAG Audit

Status: **LOCAL COMPLETE / SYNTHESIS HYPOTHESIS VALIDATED AS NONTRIVIAL**

## 1. Formation (F)

| Surface | Classification | Meaning |
|---|---|---|
| `responseFormedCandidateFamily` | EXACT DEFINITION | parent candidate family is generated from exact physical carriers + minimal child coverage |
| `responseFormedCandidateFamily_nonempty_of_zeroDefectSeed` | THEOREM | one zero-defect physical seed + child coverage generates a nonempty family |
| `responseFormedCandidateFamily_empty_of_no_exactCarrier` | NO-GO | no exact carrier ⇒ formation cannot invent a parent |
| `responseFormedCandidateFamily_recovery_on_good_event` | CONDITIONAL THEOREM | simultaneous response accuracy + known separation/gap recovers the true finite formed family |
| `formedCandidate_interactionIsolation_pos_iff` | THEOREM | positive interaction-isolation iff distinct formed candidates are probe-separated |

The main open F-side problem is operational recovery under correlated data,
unknown gap, drift and protocol choice, plus scalable carrier search.  This maps
naturally to C2/C3.

## 2. Parent completion and binding (B)

| Surface | Classification | Meaning |
|---|---|---|
| `pb0_valid_completions_have_different_dynamics` | NO-GO | valid child evidence may admit distinct richer parent dynamics |
| `pb0_pcompValidity_does_not_control_parent_semantics` | NO-GO | P-COMP validity alone does not bound parent semantics |
| `ParentBindingLipschitz` | ASSUMED DOMAIN BRIDGE | realization metric controls row-TV dynamics with constant `L` |
| `parentRowDefect_of_binding` | CONDITIONAL THEOREM | fibre diameter + binding regularity ⇒ dynamics defect bound |
| `parentSemanticDiameter_of_binding` | CONDITIONAL THEOREM | assembly diameter + binding + residual isolation ⇒ semantic diameter ≤ `L*delta/kappaMin` |
| `parentSemanticDiameter_zero_of_exact_binding` | CONDITIONAL THEOREM | zero assembly diameter collapses semantic diameter |

The scientific residual is the origin/calibration of the assembly geometry and
`L_bind`.  Generic UEOT should expose this as a typed certificate and no-go, not
pretend to derive one universal physical metric.

## 3. Transport (T)

| Surface | Classification | Meaning |
|---|---|---|
| `TransportCertificate.twoStage_*`, `chain_bound`, `weighted_chain_bound` | THEOREM / M-TC | generic exact/approx finite transport calculus |
| `assemblyDist_le_bindingTransportEnvelope` | THEOREM | M-TC transports assembly-state defect |
| `parentSemanticTracking_via_MTC*` | CONDITIONAL THEOREM | transported assembly defect + binding + isolation ⇒ semantic tracking |
| `ObjectScaleTransport` / composition | TYPED TRANSPORT | fine→coarse object mapping; identity preservation is separate |
| `OwnHistory.advance_preserves_parent` | PRESERVATION BY TYPE | preserves a supplied parent token; does not infer structural identity |
| `homeostaticMarginals_preserve_lifecycleParent` | CONDITIONAL PRESERVATION | supplied carrier-level same-parent bridge propagates through finite-time P5 marginals |

The open T-side problem is structural identity when the parent-forming
architecture itself changes.

## 4. Non-circularity audit

The desired structural-continuation theorem is **not already proved**:

- current same-parent theorems preserve an identity token or consume an explicit
  same-parent bridge;
- `ObjectScaleTransport` does not assert identity preservation;
- `ParentBindingLipschitz` does not contain long-run semantic equality, but its
  metric and constant are external domain data;
- formation produces a set/fibre of candidates and explicitly permits
  nonuniqueness.

Therefore an FBT theorem is not a trivial re-export if it makes continuation an
**output** of independently checkable formation/binding/transport coherence.

## 5. Missing arrows

`MISSING-1` Formation transport/naturality:

`T_P[F_t(x)] ≈ F_{t+1}[T_X(x)]`.

`MISSING-2` Binding transport/naturality:

`B_{t+1}(T_P p) ≈ T_D(B_t p)`.

`MISSING-3` Structural continuation:

formation coherence + binding coherence + directed transport + predictive/
causal margins ⇒ certified same-object continuation, with `SameObject` not a
premise.

## 6. Required no-go controls

1. same lower evidence / distinct parent completions;
2. formation compatibility while binding compatibility fails;
3. small dynamics distance with causal-response mismatch;
4. semantic similarity without directed historical continuation.

## 7. Generator interpretation

M-QD, M-TC and M-OI are plausible reusable ingredients for quotient/formation,
transport and invariant semantics, but FBT is **not** counted as a new generator
and this audit does not establish `FBT = M-QD + M-TC + M-OI`.  Compression-level
promotion may be considered only after exact theorem reuse, cross-domain
instances and deletion/nonredundancy evidence.
