# Theory Completion P7 — Ontogenetic Self-Construction Audit

Status: **LOCAL COMPLETE / TRACK O / UNCOUNTED**

Base: `main@695119a883b2469a7319bfc16710bd940f31bbe1`

## Scientific question

P7 asks for a construction step that is genuinely distinct from repair:

`seed/components -> formed organization -> maintenance regime`.

The finite benchmark must not relabel an already formed self-maintaining object as a
seed, and must not hide construction success inside a certificate field.

## Formal construction

The P7 seed contains only:

- a physical component;
- a repair-program source.

It does **not** contain a controller or encoded mutable repair-program
representation. `assembleRepairOrganization` creates those coordinates by the
already-declared trusted interpreter and codec:

`(x,r) -> (x, T.execute r, codec.encode r)`.

`OntogeneticState` separates pre-formation `.seed` from post-formation `.formed`.
`constructionKernel` performs the deterministic one-step assembly benchmark and
leaves formed states absorbing for the construction-only dynamics. P5/P6 then
supply the separate maintenance/resource dynamics.

## Main proved results

- `assembleRepairOrganization_mem_jointLegitimate` — admissible physical seed
  components assemble into P5 exact joint legitimacy for their own program.
- `assembled_controller_implements_source` — the newly installed controller is
  behaviorally bound to the seed's program source.
- `constructionKernel_seed_staysIn_formedTarget` — a seed enters every declared
  formed target satisfied by its assembled organization with probability one.
- `seed_constructs_finiteMaintenanceCarrier` — under the existing P5 finite
  assumptions and program validity, construction lands in the finite repair
  carrier from which recurrent homeostasis is certified.
- `pure_assembled_stays_finiteMaintenanceCarrier` — the freshly formed
  organization is an admissible pure initial law for P5 maintenance.
- `p7_terminal_ontogenetic_selfConstruction` — one theorem packages the actual
  pre-formation transition, installed controller, exact joint legitimacy and
  entry into the P5 finite maintenance carrier.

## Boundary / no-go content

`encode_injective` follows from trusted `decode_encode`; therefore distinct
program sources have distinct trusted encodings. The theorem
`distinct_program_sources_assemble_distinct_program_state` shows that the
assembler does not create missing program information from the physical
component alone. `seed_ne_formed` / `construction_state_not_formed_state` keeps
construction and repair separated at the state type.

## Claim class

P7 is a **CONDITIONAL THEOREM + ADAPTER** result.

It proves a finite ontogenetic transition under an explicit trusted assembler,
program source, physical target membership and the already established P5
repair assumptions. It does not prove construction ex nihilo.

## Nonclaims

P7 does not prove:

- origin of the repair-program source from raw matter;
- reconstruction of the trusted interpreter or codec;
- autonomous synthesis of the ambient physical dynamics/object specification;
- thermodynamic construction cost;
- reproduction or lineage — P8;
- general-state ontogeny;
- full autopoiesis.

P6 resource theorems may be applied to the post-construction maintenance law only
when their explicit reserve/replenishment/realized-cost premises are separately
supplied.

## Architecture deletion audit

Removing the seed/program-source type collapses construction back into repair of
an already formed organization. Removing the distinct pre/post constructors
loses the formal separation between ontogeny and maintenance. Removing the
maintenance-entry theorem leaves no bridge from construction to canonical P5.
The boundary theorem is needed to prevent an ex-nihilo interpretation.

No counted Core theorem, compression ledger, generator or frozen source is
modified.
