# UEOT Core Compression — Second-Order Synthesis

Status: **INTEGRATED LOCAL PASS / FOUR-GENERATOR CORE UNCHANGED / BRIDGE NETWORK VALIDATED**

Baseline: `ba793fa` plus the independently developed second-order feasibility
lanes integrated on one local synthesis branch.

The canonical counted minimal core remains

\[
\boxed{
\{M\text{-QD-01},\;M\text{-TC-01},\;M\text{-PE-01},\;M\text{-OI-01}\}
}
\]

This document records what the second-order program actually established and,
equally importantly, what it did **not** establish.

## 1. Integrated validation state

All second-order modules listed below have been loaded simultaneously through
`UEOT/V3/Compression.lean` and pass one common dependency graph.

Integrated local validation:

- `lake build UEOT.V3.Compression`: PASS;
- `lake build UEOT`: PASS, 9025 jobs;
- compression governance validator: PASS;
- proof-escape scan: PASS;
- `git diff --check`: PASS.

No counted generator, ledger mapping, source P-ID, or frozen theorem statement
was modified by this synthesis.

## 2. Result matrix

| Lane | Main relation | Result | Counted impact |
|---|---|---|---|
| Structural defect closure | M-TC -> M-QD / M-OI / exact quotient | Generative bridge | none |
| Control-limit assembly | approximate P-CORE/P-QUO -> exact P-QUO | Out-of-sample bridge | none |
| Positive-eigen invariant limit | M-PE -> M-OI after moving Doob normalization | Valid bridge | none |
| Recursive sufficient state | history/input update -> reachable-state descent | **reduces to M-QD** | rejects new generator |
| Teleological equivalence | exact equality -> positive affine -> order -> maximizers | Typed bridge hierarchy | none |
| Contractive fixed-point | Bellman + Dobrushin stability certificates | Generative cross-domain bridge | none |
| Value alignment | P-ALI-02 robustness + P-ALI-03 threshold | Generative bridge calculus | none |

The second-order program therefore produces a **network of typed bridges**, not
a fifth counted generator and not a collapse of the four-generator basis.

## 3. Structural-defect lane

The structural-defect hypothesis connected M-TC, M-QD, and M-OI through the
pattern

\[
\text{quantitative defect}
\to
\text{vanishing defect}
\to
\text{exact limiting structure}.
\]

Two conclusions survived formal testing.

### 3.1 Real generativity

`StructuralDefectControlLimit.lean` proves that a sequence of certified
approximate control quotients with vanishing source defect and convergent macro
models closes to an exact quotient, after which the existing P-QUO-01 theorem
supplies exact value and policy lifting.

This is a genuine assembly transfer not used to infer the original candidate.

### 3.2 No 4 -> 3 deletion

The deletion audit failed constructively:

- M-QD still owns exact universal descent / quotient uniqueness;
- M-TC still owns finite quantitative accumulation and transport bounds;
- M-OI still owns topological/observable limit closure.

The shared defect language is useful, but it does not replace those distinct
obligations.

## 4. M-PE -> M-OI normalization bridge

`PositiveEigenInvariantLimit.lean` proves a moving-kernel theorem.

For each `n`, M-PE generates a Doob kernel `P_n` and paired exact stationary
weight `q_n`.  If

\[
P_n\to P_*,\qquad q_n\to q_*,
\]

then the moving exact identities

\[
q_nP_n=q_n
\]

produce a vanishing residual against the fixed limiting kernel, and M-OI closes
the limit to

\[
q_*P_*=q_*.
\]

This is not the cosmetic constant-sequence use of an already invariant law.

However M-PE cannot be deleted: Doob normalization, paired eigenweights,
survival/QSD algebra, eigen-readout, and martingale structure remain outside
M-OI.

## 5. Recursive sufficient state is an M-QD derived interface

`RecursiveSufficientState.lean` resolves the earlier M-BU/M-RS question.

Given a history representation

\[
C:H\to S
\]

and an input-parametrized next response

\[
R:H\to E\to T,
\]

the recursive-sufficiency condition

\[
C(h)=C(h')\Rightarrow R(h,e)=R(h',e)
\]

for every `e` is precisely M-QD fibre compatibility after currying

\[
R:H\to(E\to T).
\]

Because `C` need not cover all of `S`, the correct universal property lives on
the reachable image `range C`.  M-QD then gives the unique update on reachable
states.

Consequences:

- no independent M-RS generator is justified;
- the Bayes ratio and measurable ambient extension in P-PRED-03 remain domain
  adapters;
- P-REF-02 retains posterior/disintegration and explicit model-conflict
  semantics;
- history augmentation is not confused with sufficient-state compression.

This is one of the strongest negative compression results of the current
program because it explains *why* the earlier M-BU candidate was useful but
non-independent.

## 6. Teleological equivalence is stratified, not absolute

`TeleologicalEquivalence.lean` formalizes the hierarchy

\[
\text{ValueEqual}
\Rightarrow
\text{PositiveAffineEquivalent}
\Rightarrow
\text{OrderEquivalent}
\Rightarrow
\text{MaximizerEquivalent}.
\]

This clarifies two different frozen results:

- P-DDH-01 gives literal equality of the combined objective under the
  \(\Pi/\Phi\) gauge transformation;
- P-TEL-01 gives a positive-affine relation between infinite-horizon policy
  values after the nontrivial telescoping/convergence analysis.

They therefore inhabit the same **equivalence hierarchy**, but are not the same
physical or mathematical transformation.

In particular, no theorem presently identifies an arbitrary DDH objective with
the policy-value functional used by TEL.  Such an evaluation bridge would need
to be stated and proved separately.

This supports the stricter UEOT interpretation

\[
\Pi/\Phi\text{ representation}
\to
\text{teleological/value equivalence class}
\to
\text{control},
\]

rather than treating the numerical decomposition into \(\Pi\) and \(\Phi\) as
uniquely identifiable from behavior.

## 7. Contractive fixed-point bridge between Control and GOA

`ContractiveFixedPoint.lean` introduces a weak `DistanceLike` contraction
certificate that requires only:

- nonnegativity;
- separation at zero;
- triangle inequality;
- strict one-step contraction.

From this it derives:

\[
\text{fixed-point uniqueness},
\]

\[
d(F^n x,F^n y)\le\alpha^n d(x,y),
\]

\[
d(x,x^*)\le\frac{d(x,Fx)}{1-\alpha},
\]

and a two-map fixed-point perturbation certificate.

The same core serves:

- Bellman/sup-metric residual and iterate certificates;
- Dobrushin/TV invariant uniqueness and stationary perturbation.

It also generates the out-of-sample theorem

\[
D_{TV}(P^n\mu,\mu^*)
\le
\alpha(P)^nD_{TV}(\mu,\mu^*).
\]

This is a genuine Control <-> GOA stability bridge.

It remains uncounted because it does not construct either domain's evolution
operator, prove fixed-point existence, construct optimal selectors, establish
causal optimality, or prove Dobrushin contraction itself.

## 8. Value-alignment calculus and the ALI-01 boundary

`ValueAlignment.lean` identifies the common local object

\[
S_g(v)=\langle g,v\rangle.
\]

It exactly rederives the source-facing signatures of P-ALI-02 and P-ALI-03 and
proves the new robust coordination result:

if the intended coordinated target is only `g + e`, with

\[
\|e\|<\|g\|,
\]

then the P-ALI-02 robustness margin

\[
m=\|g\|(\|g\|-\|e\|)
\]

can replace the ideal \(\|g\|^2\) target in a conservative P-ALI-03 threshold.
Above that threshold the *actual imperfect target* still has positive parent
directional score.

P-ALI-01 is intentionally excluded.  It answers a prior question:

> does the local directional one-form arise from any globally consistent scalar
> value at all?

Thus the correct order is

\[
\text{integrability boundary}
\to
\text{global value, when it exists}
\to
\text{local M-VA directional coordination}.
\]

Local alignment must not be identified with GOA convergence.

## 9. What the second-order search says about the minimal core

The most important result is not that many abstractions compile.  It is that
the attempted reductions repeatedly stop at the same four kinds of obligation:

### M-QD — representation / descent

When does richer state/history information factor uniquely through an
effective representation?

### M-TC — finite quantitative transport

How do local mismatch certificates accumulate or contract through finite
composition?

### M-PE — positive spectral normalization/value

How does positive left/right eigenstructure generate normalized dynamics,
survival/value weights, and martingale/readout structure?

### M-OI — asymptotic closure

When does approximate/asymptotic invariance become exact invariance in a
limit?

The second-order candidates connect these obligations but have not removed one.

Current evidence therefore strengthens rather than weakens the claim that the
four-generator set is a useful minimal structural basis for the proved Core v3
compression target.

This remains a statement about the **current formal theorem graph**, not a proof
that no future stronger abstraction can reduce the basis further.

## 10. Emerging UEOT architecture after compression

The verified graph now supports a more precise reconstruction of the original
UEOT conceptual spine:

\[
\text{effective object/state}
\xrightarrow{M\text{-QD}}
\text{closed usable representation}
\]

with recursive update supplied as a derived M-QD interface;

\[
\text{local change / model mismatch}
\xrightarrow{M\text{-TC}}
\text{controlled finite transport},
\]

\[
\text{positive growth/survival structure}
\xrightarrow{M\text{-PE}}
\text{normalized value/invariant candidates},
\]

and

\[
\text{asymptotic residual}
\xrightarrow{M\text{-OI}}
\text{exact long-run invariant structure}.
\]

Around this minimal core sit typed bridges:

\[
\text{teleological representation}
\xrightarrow{M\text{-TE bridge}}
\text{decision-order equivalence},
\]

\[
\text{Control}
\xrightarrow{M\text{-CF stability bridge}}
\text{stable fixed/long-run structure},
\]

\[
\text{parent value}
\xrightarrow{M\text{-VA bridge}}
\text{robust local alignment}.
\]

This suggests the typed chain

\[
\boxed{
\text{state/identity}
\to
\text{value representation}
\to
\text{Control/GOD}
\to
\text{closed-loop dynamics}
\to
\text{GOA}
\to
\text{hierarchical alignment}
}
\]

but the arrows are now explicit theorem obligations rather than philosophical
identifications.

## 11. Decisive end-to-end theorem — local PASS

The strongest proposed next test was an end-to-end theorem not used to infer
the current generators:

\[
\text{recursive sufficient state}
\to
\text{control on that state}
\to
\text{optimal selector / GOD}
\to
\text{policy-induced closed-loop dynamics}
\to
\text{long-run invariant GOA under explicit stability hypotheses}.
\]

In shorthand:

\[
M\text{-QD-derived recursive state}
+
\text{Control}
+
M\text{-OI/M-CF}
\Longrightarrow
\text{Agency -> GOD -> GOA assembly}.
\]

This lane is now implemented in

`UEOT/V3/Compression/AgencyGodGoaAssembly.lean`.

The stronger theorem `agency_god_goa_from_history` does not merely place a
recursive-state theorem and an unrelated control model on the same state type.
It starts from history-level reward/transition data, requires their exact
fibre-sufficiency through one effective state map, uses M-QD-derived recursive
descent to construct the finite control model, obtains the Bellman-greedy
selector, forms the exact P-CORE policy-induced closed-loop matrix, obtains an
invariant law through the M-OI P-GOA-01 route, and under an explicit Dobrushin
margin uses M-CF to prove uniqueness and geometric attraction.

Thus the requested no-smuggling criterion is satisfied in the finite setting:
GOA existence, uniqueness, and mixing are conclusions, not assumptions.

The dedicated audit is
`docs/compression/AGENCY_GOD_GOA_ASSEMBLY_AUDIT.md`.

## 12. Final second-order disposition

At the current verified checkpoint:

- **counted generators:** unchanged at four;
- **second-order deletion:** no justified 4 -> 3 reduction;
- **new bridges:** multiple, machine-checked, and jointly buildable;
- **new generated consequences:** yes, including exact control-limit closure,
  moving positive-eigen invariant closure, Dobrushin geometric mixing, and
  robust imperfect-target alignment;
- **decisive out-of-sample assembly:** finite Agency -> GOD -> GOA **PASS**;
- **quantitative perturbative assembly:** local PASS in
  `ApproximateGoaTracking.lean`: P-QUO-02 near-optimal control + M-TC
  time-varying defect transport + M-OI reference invariant existence + M-CF
  near-GOA stability;
- **approximate history encoder:** local PASS; within-fibre reward and encoded
  transition-TV defects now construct the `ApproxControlQuotient` itself, so
  the quantitative chain starts at representation defect rather than an
  independently supplied macro approximation certificate;
- **encoder exact closure:** local PASS; vanishing fibre-defect envelopes feed
  the existing structural-defect exactification layer and produce a literal
  `ExactControlQuotient`, after which P-QUO-01 gives exact value/Q/policy
  descent;
- **quotient gauge:** local PASS; two surjective representations with identical
  source fibres are uniquely equivalent up to quotient-state relabeling, with
  the equivalence generated by M-QD descent in both directions;
- **approximate quotient gauge:** local PASS; finite representations of equal
  quotient cardinality now carry a label-invariant mismatch distance with
  attained optimal alignment, exact-zero recovery of `SameFibers`, symmetry,
  and triangle inequality;
- **occupation-weighted quotient gauge:** local PASS; under one source simplex
  law the optimal relabeling cost becomes the occupied mass of partition drift,
  with support-level zero semantics, full-support recovery of exact
  `SameFibers`, symmetry, and triangle inequality;
- **moving encoder gauge closure:** local PASS; for a finite source under one
  fixed full-support law, weighted gauge mismatch converging to zero forces
  eventual exact `SameFibers` with the reference encoder because every nonzero
  mismatch has a positive minimum-mass gap;
- **gauge-to-control semantic transfer:** local PASS; exact quotients of one
  micro model with the same source fibres have one unique M-QD-generated state
  relabeling transporting reward, transition, optimal value, optimal Q, and
  Bellman-optimal actions; weighted gauge convergence therefore yields eventual
  exact control-semantic gauge lock for moving exact quotients;
- **closed-loop / unique-GOA gauge invariance:** local PASS; the semantic state
  relabeling transports deterministic optimal selectors, conjugates the exact
  P-CORE policy-induced closed-loop matrices, transports simplex evolution, and
  carries the source M-CF-certified unique invariant GOA to the target unique
  invariant law.  A direct wrapper starts from `SameFibers + same micro`;
- **TV / Dobrushin metric gauge invariance:** local PASS; simplex PMFs and row
  PMFs commute with state relabeling, canonical event-supremum TV is exactly
  preserved, conjugate kernels have identical Dobrushin coefficients, and the
  complete M-CF geometric mixing certificate transfers with the same numerical
  rate and initial TV error;
- **next research target:** leave the now-nearly-saturated exact gauge lane and
  test approximate semantic gauge stability, explicitly requiring semantic
  reward/transition defect envelopes so representation mismatch is not falsely
  identified with model closeness.

The compression program has therefore moved beyond proof deduplication: it now
has a stable minimal core plus a growing, typed bridge architecture that can be
tested by new theorem generation.
