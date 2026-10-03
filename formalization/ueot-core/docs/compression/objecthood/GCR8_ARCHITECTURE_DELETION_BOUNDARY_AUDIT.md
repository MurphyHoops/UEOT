# GCR8 — Architecture / Deletion / Residual-Boundary Audit

Status: **FINAL LOCAL PASS**
Tracker: #243
Planning parent: #242
Governance base: `main@a2fd6f431e6ef891bc5b233d87a4cc884bcf9129`
Prior local stages: GCR0 `4c87558`, GCR1 `83d28d6`, GCR2 `611706c`,
GCR3 `9c75f5c`, GCR4 `2aec086`, GCR5 `a1cb1ec`,
GCR6 `6be0695`, GCR7 `a6d13bc`
Counted-core impact: **NONE**

## 1. Exact scientific verdict

Within the exact finite controlled-PMF semantics authorized by #243, the AR6
G3 boundary `GeneralCausalToStationaryCompleteness` is **CLOSED**.

The machine-checked chain is:

1. GCR0 identifies deterministic stationary physical path laws with the exact
   AR6 complete-history causal path-law semantics.
2. GCR1 proves target absorption preserves first-hitting semantics and builds
   the finite normalized discounted repair model / greedy certificate.
3. GCR2 identifies nested discounted value with exact Ionescu--Tulcea
   normalized target occupation.
4. GCR3 proves arbitrary-causal discounted domination and the Abelian
   almost-sure-hitting direction.
5. GCR4 uses finiteness of `X -> A` to extract one fixed deterministic
   stationary almost-sure-hitting witness.
6. GCR5 proves finite homogeneous stationary almost-sure hitting implies finite
   canonical expected hitting time.
7. GCR6 proves `GeneralCausalToStationaryCompleteness P K` and the exact
   set-level equivalence between general-causal almost-sure repairability and
   deterministic-stationary finite-expected repairability.
8. GCR7 identifies that set with the unchanged AR3 maximal certificate basin
   and resynthesizes the existing Objecthood repair conclusions on the proved
   general-causal semantics.

Accordingly there is **no residual G3 boundary inside the authorized #243
finite-PMF target**.

This verdict does not assert an extension to infinite state/action spaces,
arbitrary non-PMF controlled kernels, or other semantics outside the frozen
GCR contract.  Such extensions are outside this mission, not unresolved
subgoals of the theorem proved here.

## 2. Architecture classification

| Stage | Principal role | Classification |
| --- | --- | --- |
| GCR0 | stationary / complete-history physical path-law equivalence | G1 semantic bridge |
| GCR1 | absorbed first-hitting invariance + normalized Bellman adapter | G1 bridge / G2 derived adapter |
| GCR2 | exact nested-value / physical path-law occupation identity | G1 semantic bridge |
| GCR3 | all-causal discounted domination + Abelian limit | G1 quantitative bridge |
| GCR4 | finite-policy pigeonhole extraction of one fixed stationary witness | G2 derived witness synthesis |
| GCR5 | stationary a.s.-hitting -> finite expected hitting | G1 quantitative bridge |
| GCR6 | closure of the named general-causal completeness boundary | G1/G2 closure; prior G3 discharged |
| GCR7 | maximal-certificate / general-causal Objecthood resynthesis | G2 end-to-end synthesis |
| GCR8 | architecture/deletion/boundary audit | audit only; no G0 promotion |

No GCR stage establishes a new primitive generator.  None has architecture
role G0 for counted-core purposes.

## 3. Frozen counted-core audit

The live compression ledger remains unchanged from the authorized main base and
continues to record:

- source P-IDs: **106**;
- source proved: **106**;
- final dispositions: **106**;
- unresolved P-IDs: **0**;
- counted generators: **4**;
- minimal-core state: **frozen**;
- exact counted generator IDs:
  `M-QD-01`, `M-TC-01`, `M-PE-01`, `M-OI-01`.

The live FINAL validator with GitHub reference verification passes and reports
`source_index=106`, `unique=106`, `counted_generators=4`,
`final_dispositions=106`, `unresolved=0`, and
`minimal_core_state=frozen`.

The validator also prints `generators=5`, which is the number of generator
records in the ledger, **not** the counted minimal-core cardinality.  The
authoritative counted field and `minimal_core.generator_ids` remain exactly
the four IDs above.

The following frozen/protected files are byte-identical to `origin/main` in
the cumulative GCR branch:

- `formalization/ueot-core/docs/V3_COVERAGE_STATUS.md`;
- `formalization/ueot-core/docs/PID_STATUS.yaml`;
- `formalization/ueot-core/docs/CORE_COMPRESSION_THEOREM_INDEX.csv`;
- `formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml`;
- `formalization/ueot-core/docs/compression/COMPRESSION_RESEARCH_TRACKS.json`;
- `formalization/ueot-core/docs/compression/POST_FINAL_RESEARCH_GOVERNANCE.md`.

No counted theorem source, ledger, coverage record, theorem index, or promotion
state is mutated by GCR.

## 4. Source-track isolation audit

The cumulative `origin/main..HEAD` diff through GCR7 contains only:

- the public Objecthood root import surface;
- nine new GCR Objecthood Lean modules;
- the GCR0--GCR7 audit documents.

There are no changes under the Track-S topology/stability source surfaces, no
changes under `Compression/Hierarchy/` or the Track-H root, and no changes to
Track-X source surfaces.

Thus GCR consumes frozen/merged interfaces only and does not reopen S, H, or X.

## 5. Deletion / nonredundancy audit

GCR closes a semantic comparison boundary; it does not make the pre-existing
repair architecture redundant.

- `GeneralCausalRepairBoundary.lean` remains useful as the stable definition
  layer for the broad comparison class and named completeness proposition.
  GCR6 proves that proposition in a separate closure module rather than
  rewriting the historical AR6 artifact.
- GCR0 is indispensable for the stationary -> general-causal direction and for
  exact physical path-law identity.
- GCR1--GCR3 are the semantic and Abelian bridges that prevent discounted
  optimality from being relabelled as undiscounted reachability.
- GCR4 is the finite-policy memoryless-determinacy extraction step; it is not
  implied by the fixed-beta verifier alone.
- GCR5 is the finite-state homogeneous tail argument needed to upgrade
  stationary a.s.-hitting to finite expectation.
- The AR3 maximal repair policy/certificate is retained unchanged.  GCR6/GCR7
  prove that its old deterministic-stationary basin already equals the broader
  general-causal class; they do not replace the certificate.
- The original deterministic-stationary AR7 wrapper theorems remain useful
  narrower APIs and are directly reused by GCR7.  Deleting them would reduce
  modularity without removing any primitive.
- `StrongRepairable`, `repairRank`, and the endogenous descending
  certificate remain nonredundant constructive substructure: they provide a
  finite-step/rank guarantee strictly stronger than mere membership in the
  maximal stochastic/general-causal basin.
- Route B (qualitative nested safe-progress attractor) was retained only as a
  read-only fallback/cross-check and was never promoted into repository source;
  Route A closed the target theorem, so no duplicate Route-B implementation is
  required.

No source deletion is justified by this cycle.

## 6. Objecthood meaning after GCR

The strongest proved repair statement now has the following exact semantics:

> For finite controlled PMF dynamics, every state that can reach the repair
> target almost surely under any admissible randomized complete-history causal
> policy belongs to the basin of the one AR3 maximal deterministic stationary
> repair certificate; conversely every state in that basin is repairable in
> the broad general-causal sense.

Through the unchanged AR7/O7/ER0 architecture, this general-causal repairability
is sufficient for failure repair and eventual permanent return to the
legitimate constitutive domain.

This is a stronger semantic closure than AR7 had before GCR, but it is still
repair/recovery of an already specified object.  It is **not** recurrent
homeostasis under continuing faults, repair-law self-reconstruction,
energetic/resource closure, ontogenetic construction, or full autopoiesis.

## 7. Hard boundary after local GCR closure

GCR8 ends this research cycle.  The next scientific stage, only after the full
remote closeout required by #243, is RH recurrent homeostasis.  RH must use an
explicit repair kernel `Q`, fault kernel `F`, fault hazard `epsilon`, and
AR repair potential `W` to study long-run occupation/homeostatic bounds.

RLSR remains after RH and must separate immutable ambient/trusted substrate
from the mutable object-level repair program.  EC, OC, and an explicit
`AutopoieticObject` contract remain later still.

Nothing in GCR authorizes any of those stages now.

## 8. Local validation

GCR8 is a documentation/audit stage.  Its terminal and cumulative gates pass:

- focused Lean compile of `GeneralCausalRepairSynthesis.lean`: **PASS**;
- Objecthood build: **PASS**;
- Compression build: **PASS** (`9111/9111` jobs);
- cumulative proof-escape scan over all nine GCR Lean modules:
  **CLEAR**;
- representative cross-stage `#print axioms` for the GCR0 path-law bridge,
  GCR1 absorption invariance, GCR2 exact occupation bridge, GCR3 Abelian
  direction, GCR4 stationary witness, GCR5 finite-expectation bridge, GCR6
  completeness theorem, and GCR7 maximal-basin identification: only
  `propext`, `Classical.choice`, `Quot.sound`;
- counted FINAL governance validator with live GitHub reference verification:
  **PASS** — `source_index=106`, `unique=106`,
  `counted_generators=4`, `final_dispositions=106`, `unresolved=0`,
  `minimal_core_state=frozen`;
- research-governance regression suite: **PASS**;
- cumulative protected-file/source-track diff audit: **PASS**;
- full second-pass `lake build UEOT`: **PASS** (`9130/9130` jobs);
- exact-candidate Track-O validation for the final staged GCR8 tree and for the
  cumulative `origin/main -> GCR0--GCR8` candidate: run immediately before
  the atomic local commit;
- final `git diff --check`: **PASS**.

After those exact-candidate checks, the GCR8 commit is the final local mission
commit.  Only then may the research branch be pushed for the first time.
