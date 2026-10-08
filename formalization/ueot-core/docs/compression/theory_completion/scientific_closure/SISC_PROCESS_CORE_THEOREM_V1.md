# SISC core theorem candidate — process-generated predictive quotient

Date: 2026-10-08. Branch: `research/sisc-local-20261008`.
Disposition: **LOCAL CONDITIONAL CORE CANDIDATE / SCIENTIFIC FINAL HOLD**.
Source: `SISCFutureResponseCore.lean`, `SISCFiniteFutureProbes.lean`.

## An explicit chain from process to minimal recursively evolving state

Let `X` be a set of process states, `A` the registered intervention set,
`step : X → A → X` a **deterministic** controlled transition, and
`read : X → O` a declared observable. For a finite word of interventions
`w ∈ List A`, define the future-response function

`F(x)(w) = read(runInterventions(step,x,w))`.

Define `x ≈ y ↔ F(x) = F(y)` and the **reachable response-state image**
`S = range(F)`. This is a construction from the process, not a given `q`.

**Core claim 1 (automatic dynamical closure).**

`F(x)=F(y) → F(step(x,a))=F(step(y,a))` for every `a`.

The proof evaluates the former function equality on the longer word `a::w`;
the generic `M-RS` compatibility premise is here **derived**. Consequently
there exists **exactly one** action update on the reachable canonical image
that commutes with the bottom-level step.

**Core claim 2 (universal minimality).** For any candidate summary
`q : X → Q` which (i) preserves the current observable whenever `q(x)=q(y)`
and (ii) is a congruence under every registered action, **every future
response** agrees whenever `q(x)=q(y)`. Therefore there exists a unique
map `range(q) → range(F)` recovering the canonical state from the summary.
It says `F` is a **coarsest sufficient recursive state**, not an ontic object.

**Core claim 3 (representation invariance).** If some summary `q` identifies
*exactly* the same pairs as `F`, its reachable image is related to the
canonical state by a **unique bijective relabeling** commuting with source
representation. This is a specialization of the established
`Compression.QuotientGauge` theorem, not an independent new gauge principle.

**Core claim 4 (finite protocol extraction).** If `X` is finite, then there
exists a finite set `E ⊂ List A` of at most `|X|²` finite intervention words,
such that equality of responses over `E` is equivalent to equality of the
**entire** future-response functions for *every* state pair. This is proved
by choosing one distinguishing word for each distinguishable ordered pair.
The existence proof is **noncomputable** and provides neither a polynomial
time algorithm nor an a-priori short-word length bound.

**Falsifying control.** The module constructs two `Bool×Bool` process states
with identical present observations but a permitted intervention that reveals
different futures. Present-response equivalence is not automatically a
dynamical congruence. This precisely falsifies the tempting shortcut
`observation identity ⇒ state identity`.

**Stronger negative control.** A constant-response two-token system exhibits
two distinct physical tokens with identical response signatures for *every*
allowed finite intervention history. Thus **even complete future-response
access relative to a non-separating protocol cannot certify literal physical
token identity**. The canonical predictive quotient intentionally merges
them; source-token individuation needs extra independently grounded evidence.

## Relation to existing UEOT sources

| Existing result | New leverage | What is not newly established |
|---|---|---|
| `M-QD`, `QuotientDescent` | universal descent supplies the unique factor | generic quotient mathematics not invented here |
| `M-RS`, `RecursiveSufficientState` | derives compatible update from the entire future signature | measurable or continuous extension to arbitrary ambient states |
| `QuotientGauge` | minimal representations differ only by relabeling | physical metric or gauge semantics without calibration |
| `P-PRED-01/03` | deterministic, exact process-level construction | arbitrary Bayesian regular conditional kernels and null-set issues |
| P4 Inverse Objecthood | provides an evidence-relative canonical candidate class | objecthood validity, unique physical tokens or causal provenance |
| SISC SI-1..SI-4 | gives a non-arbitrary source for a predictive state type | formation `tp`, physical identity, repair/viability, purpose/GOA |
| C3 Nested Search | proves existence of a finite distinguishing protocol in finite systems | efficient construction, experimental budget/complexity |

## Five decisive caveats

1. This result is a familiar **behavioral equivalence / Myhill–Nerode-type**
   construction in deterministic automata and predictive-state theory. It is
   a valuable formal integration for UEOT, **not proof of conceptual novelty**.
2. The response signature quantifies over *all finite action words*; it is
   epistemically justified only when these interventions are admitted and
   their response model is known. Finite probe existence via choice is not a
   physically executable experimental plan without word discovery.
3. Distinct world tokens may be behaviorally indistinguishable in all
   registered experiments. `S` then merges them by design; this does **not**
   prove they are one physical object.
4. Real physical evolution is often stochastic or continuous-time; the
   immediate theorem is **deterministic and set-level**. Kernel descent,
   measurability, causal identification, noise and intervention histories
   must be handled by separate bridge theorems.
5. Internal predictive recursion says nothing about *object individuation*:
   a boundary/delimitation, autonomous maintenance, repair, viability,
   teleological contract and typed GOD/GOA obligations remain distinct.

## Scientific implication

The most defensible candidate for UEOT's shared **mathematical architecture**
is a **process-dependent quotient carrying closed evolution**. The intuitive
principle is that distinctions which never change admissible future
responses may be discarded, but distinctions which control future evolution
must be retained. This is one common structure behind prediction, scale,
state compression and operational identity certificates.

It is NOT by itself the complete minimal foundation of the UEOT physical
ontology: constitutive persistence and external interventions may demand
independent semantic/evidence types not recoverable from the quotient alone.
No Core v3 theorem count, compression counted generator, scientific C4/7
disposition or cloud publish gate is changed.
