# Theory Completion P7 — Ontogenetic Self-Construction Audit

Status: **LOCAL COMPLETE / REVIEW-TIGHTENED / TRACK O / UNCOUNTED**

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
`ontogeneticConstructionKernel` is not an arbitrary `Seed → Org` adapter: its
source is fixed to `OntogeneticSeed X Program`, its target is fixed to
`RepairOrganizationState X A Representation`, and its constructor is exactly
`assembleRepairOrganization T codec`. This excludes the degenerate
`Seed := Org; assemble := id` witness that would merely relabel a formed object.

## Main proved results

- `assembleRepairOrganization_mem_jointLegitimate` — admissible physical seed
  components assemble into P5 exact joint legitimacy for their own program.
- `assembled_controller_implements_source` — the newly installed controller is
  behaviorally bound to the seed's program source.
- `ontogeneticConstructionKernel_seed_staysIn_formedTarget` — a seed enters every declared
  formed target satisfied by its assembled organization with probability one.
- `seed_constructs_finiteMaintenanceCarrier` — under the existing P5 finite
  assumptions and program validity, construction lands in the finite repair
  carrier from which recurrent homeostasis is certified.
- `pure_assembled_stays_finiteMaintenanceCarrier` — the freshly formed
  organization is an admissible pure law on the finite carrier; this theorem by
  itself makes **no** claim that a P5 recurrent-homeostasis system has been
  instantiated.
- `pure_assembled_stays_p5MaintenanceSystem` — after threading P5's actual
  viability fixed point, repair-policy dynamics bridge, finite representation,
  fault envelope and hazard premises, the same pure law lies in the carrier of
  the instantiated `finiteJointRecurrentHomeostasisSystem`.
- `p7_terminal_ontogenetic_assembly` — packages the typed pre-formation
  transition, installed controller, exact P5 legitimacy and entry into the
  actual P5 recurrent-maintenance system.

## Boundary / no-go content

`encode_injective` follows from trusted `decode_encode`; therefore distinct
program sources have distinct trusted encodings. The theorem
`distinct_program_sources_assemble_distinct_program_state` shows that the
assembler does not create missing program information from the physical
component alone. `seed_ne_formed` / `construction_state_not_formed_state` keeps
construction and repair separated at the state type.

## Claim class

P7 is a **CONDITIONAL THEOREM + TRUSTED ASSEMBLY ADAPTER** result.

It proves a finite ontogenetic assembly transition under an explicit trusted
interpreter/codec, a supplied program source, physical target membership and the
full already-established P5 recurrent-maintenance premises. It does not prove
construction ex nihilo, nor does the type-level pre/post distinction alone count
as evidence of autonomous self-construction.

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
