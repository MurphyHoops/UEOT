# RH4 — Cesaro / Invariant Occupation Bridge Audit

Status: **FINAL LOCAL CANDIDATE**
Tracker: #248
Planning parent: #246
Authorization base: main@c6bb5a82f51dfaf18a354ee4a11687bff40a315f
Prior local stages: RH0 faebae1, RH1 f23fbce, RH2 a3156e5, RH3 4961e3f
Counted-core impact: **NONE**

## Scope

RH4 bridges the exact RH3 finite-PMF marginal process to the already merged
finite row-stochastic / Cesaro / occupation-limit interfaces. It does not
duplicate or modify FiniteCesaroInvariant.lean,
Compression/OccupationLimitInvariance.lean, or Track-S source files.

## PMF to matrix adapter

pmfKernelMatrix maps H(x,y) to its real probability entry and
pmfKernelMatrix_rowStochastic proves row-stochasticity.

pmfSimplex_bind_vecMul proves PMF bind is exactly matrix row evolution.
pmfSimplex_homeostaticMarginal_eq_orbit identifies every RH3 marginal with
the existing FiniteCesaroInvariant.orbit.

cesaroRow_eq_average_homeostaticMarginal identifies the existing Cesaro row
with the finite average of exact RH3 marginals.

## Occupation observable

simplexDamagedMass and simplexLegitimateMass are complementary finite simplex
observables. Their masses sum to one.

simplexDamagedMass_pmfSimplex identifies damaged simplex mass exactly with
finite PMF mass on L-complement.

simplexDamagedMass_cesaroRow_eq_realDamageAverage identifies the Cesaro
observable exactly with RH3 realDamageAverage.

The damaged-mass observable is continuous, so finite-average bounds pass to
convergent Cesaro subsequences.

## M-OI / P-GOA reuse

RecurrentHomeostasisSystem.invariant_cesaro_limit_damage_bound takes an
arbitrary convergent Cesaro subsequence and proves:

- its limit is invariant, using
  OccupationLimitInvariance.finite_invariant_of_cesaro_tendsto;
- damaged invariant mass is at most the certified load ratio lambda/kappa;
- legitimate invariant mass is at least 1-lambda/kappa.

Thus the RH3 occupation estimate passes to every convergent Cesaro subsequence
supplied to this theorem.

exists_invariant_cesaro_limit_with_damage_bound obtains existence only by
calling the already merged
OccupationLimitInvariance.p_goa_01_via_occupationLimit compactness adapter and
then invokes the universal theorem above.

No invariant-law uniqueness, full Cesaro convergence, irreducibility,
aperiodicity, or mixing claim is introduced.

## Boundary discipline

RH4 does not claim pathwise recurrent legitimacy, a sharp phase transition,
semantic identity during damaged periods, repair-law self-reconstruction, or a
new generator.

## Local validation

- focused Lean compile of CesaroHomeostasis.lean: **PASS**;
- lake build UEOT.V3.Compression.Objecthood: **PASS**;
- lake build UEOT.V3.Compression: **PASS**;
- proof-escape scan: **PASS**;
- representative #print axioms: **PASS**;
- research-governance regression: **PASS**;
- exact-candidate Track-O validation: **PASS**;
- final git diff --check: **PASS**.

No RH research branch is pushed in RH4.
