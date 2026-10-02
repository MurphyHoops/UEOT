# Endogenous Formation × Constitutive Persistence — Final Local Synthesis

Status: **LOCAL CONDITIONAL CLOSURE**

Exact implementation:

`e58ab6c8ac06b4ba7ea62be1bf2665483d8ec189`.

Remote predecessor integration:

PR #228 merged into `main` as

`ba6da44fbf87b0f2f31313ae4479d70253c99b4c`.

## 1. Candidate formation result

The previous interaction-identifiability theory began from an external finite
candidate space `A`.

The new construction replaces that free input, for the finite
response/carrier/child-region setting, by

`response law`

-> `zero-defect seed`

-> `minimal exact physical carrier`

-> `minimal sufficient child coalition`

-> `FormedCandidate`.

A single finite zero-defect seed covered by the declared children is enough to
prove that this generated candidate family is nonempty.

The frozen statistical recovery theorem also lifts to exact recovery of the
formed candidate family on its good event.

## 2. Formation-to-identification result

Generated candidates carry the Hamming metric on child-membership signatures.

An interaction response family restricted to these candidates therefore has a
canonical interaction conorm `beta_E`.

Lean proves on this generated type:

`beta_E > 0`

iff

the selected probes distinguish every distinct generated coalition pair.

Thus the earlier chain

`candidate A -> interaction identification`

has become, conditionally,

`response/child structure -> generated A -> interaction identification`.

## 3. Constitutive persistence result

For finite controlled dynamics `P : X -> A -> PMF X`, the P-PER viability
machinery stabilizes at a fixed kernel `K` and produces a stationary preserving
selector `pi`.

The local construction forms reflexive state

`Z = X × (X -> A)`

and stores `pi` in `Z`.

The lifted dynamics reads `pi(x)` internally and has only `Unit` as external
action.

Machine-checked consequences:

- external action is irrelevant;
- the physical marginal equals the original policy-induced transition;
- the controller coordinate is exactly preserved;
- the constitutive domain `K × {pi}` is a fixed viability set;
- from any finite viability problem such a constitutive fixed set exists;
- starting in that domain, the true path law remains there for all times with
  probability one.

This is a genuine runtime-autonomy upgrade over merely displaying `pi` as an
external theorem witness.

## 4. Why this is not yet full Objecthood

The preserving controller is synthesized from the finite viability problem and
then embedded.  The lift does not regenerate it if corrupted.

Indeed Lean proves that a wrong controller stays wrong under the current lift.

Therefore the supported terminology is:

**endogenous/constitutive runtime persistence**,

not

**self-repairing Omega-loop Objecthood**.

The remaining Omega-loop target is now concrete:

`controller/integrity failure`

-> `internally detectable defect`

-> `repair/reconstruction action`

-> `return to constitutive domain`

with the repair mechanism itself represented inside the object state/dynamics.

## 5. Operational synthesis certificate

The final local layer now packages the preceding branches into

`OperationalFormedPersistentParent`.

The certificate simultaneously records:

- membership of the selected parent in the response-generated coalition
  family;
- family-wide interaction separation on a nonempty probe set;
- a nonvacuous constitutive persistence certificate containing an actual seed
  state, fixed viability kernel, internal controller, and probability-one
  all-times persistence witness.

`exists_operationalFormedPersistentParent_of_responseSeed` constructs such a
certificate from:

1. nonempty lower-level response-history and response-probe axes;
2. one zero-defect lower-level response carrier seed;
3. child-region coverage of that seed;
4. a nonempty finite interaction-probe family that separates all generated
   candidates;
5. nonempty P-PER winning sets for the generated parents.

The first condition is a post-review hardening: it rules out vacuous
`responseDefect = 0` caused solely by an empty response axis.

This is the first local theorem in the current chain that places generated
formation, identifiability, and nonvacuous autonomous persistence in one typed
object.  It is still deliberately named **operational formed-persistent
parent**, not UEOT Object, because controller repair/reconstruction is absent.

The formation side also has an exact negative boundary:

`no exact physical carrier -> no response-formed parent candidate`.

## 6. Updated UEOT object-construction stack

The strongest justified finite architecture is now

`lower-level response structure`

-> `formed candidate coalitions`

-> `interaction identification beta_E`

-> `P-MET parent realization`

-> `Track-S semantic isolation kappa_sem`

-> `stable parent semantics`

plus, on the persistence side,

`P-PER viability kernel`

-> `preserving selector`

-> `selector internalization into reflexive state`

-> `autonomous probability-one constitutive persistence`.

These branches now meet in

`OperationalFormedPersistentParent`,

subject to explicit interaction-separation and nonempty-winning-set
conditions.

The two branches are now structurally much closer to a later object synthesis,
but they have not yet been identified with one another.

## 7. What is closed locally

1. response-generated finite candidate-family definition;
2. zero-defect seed -> exact minimal carrier existence;
3. zero-defect covered seed -> nonempty formed candidate family;
4. P-COMP-06 exact child-coalition construction;
5. empirical carrier recovery -> formed-candidate recovery;
6. generated candidate subtype and coalition-Hamming metric;
7. generated formation -> interaction-identification bridge;
8. internal constitutive controller representation;
9. proof that external `Unit` action is irrelevant;
10. exact physical/controller projection theorems;
11. fixed constitutive viability domain;
12. finite existence of constitutive closure;
13. path-level probability-one constitutive persistence;
14. explicit no-self-repair boundary for corrupted controllers.
15. no-carrier -> no-formed-candidate boundary;
16. nonvacuous constitutive persistence certificate with an actual seed;
17. operational formation + identification + persistence synthesis certificate.

## 8. What remains open

The local closure does not prove:

- every physical domain has a zero-defect seed;
- a universal parent constructor independent of readout/region semantics;
- infinite candidate formation;
- optimal noisy estimator/sample complexity beyond existing recovery premises;
- uniqueness of the formed parent coalition;
- that formation, identification, semantic stability, and persistence select the
  same unique parent in every domain;
- self-construction of the preserving controller;
- autonomous repair/reconstruction after controller corruption;
- energetic/material closure;
- full P-OMG-integrated self-repair;
- a final Omega-loop Objecthood equivalence;
- a fifth counted generator.

## 9. Validation

On exact implementation `e58ab6c...`:

- focused new modules: **PASS**;
- public CrossTrack build: **PASS**;
- full `lake build UEOT`: **PASS (9101 jobs)**;
- research governance relative to merged `origin/main`: **PASS, 8 paths**;
- research-governance regressions: **PASS**;
- frozen compression validator: **PASS**;
- compression validator regressions: **PASS**;
- source/final accounting: **106/106**;
- counted generators: **4**;
- unresolved: **0**;
- proof-escape scan: **PASS**;
- exact diff-check: **PASS**;
- selected public theorem axiom audit: only
  `propext / Classical.choice / Quot.sound`.

## 10. Local verdict

**Conditional closure of the two previous high-level residuals.**

Candidate formation is no longer an arbitrary type input in the finite
response/carrier/coalition model, and preserving control is no longer an
informative external runtime action in the constitutive persistence model.

Moreover, those two results are now joined by an explicit nonvacuous
operational parent certificate rather than merely coexisting in parallel
modules.

The next dominant mathematical target is correspondingly sharper:

**self-repairing constitutive closure** rather than generic persistence.
