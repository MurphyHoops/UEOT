# UEOT Core v3 — Active Formalization Feedback

Date: 2026-09-10
Status: maintenance findings only; canonical v3.0 text/hash unchanged

This file records concrete findings produced by machine formalization.  A note
here does not alter a v3 P-ID.  It is an auditable queue for an erratum or a
future v3.1 source revision after mathematical review.

## FB-DYN-02-001 — CTMC semigroup time domain

Classification: **F2 — theorem split by model class / time domain**.

Canonical v3 P-DYN-02 is stated for a finite continuous-time Markov chain and
its semigroup.  In probabilistic CTMC semantics the semigroup is used for
`t >= 0`.  The first Lean analytic helper was naturally written with the matrix
exponential identity for every real `t`, because this makes ordinary two-sided
differentiation at zero immediate.  That helper is mathematically valid but has
a strictly stronger time-domain premise than the source-facing CTMC direction.

Maintenance recommendation for v3.1:

1. keep the algebraic all-real exponential intertwining lemma as a reusable
   strengthening, not as the P-DYN-02 source theorem;
2. state the CTMC forward hypothesis only for `t >= 0`;
3. say explicitly that the forward proof uses the right derivative at zero (or
   a derivative-within `[0, infinity)` argument);
4. retain the generator/block-sum equivalence and separately verify that the
   common block sums satisfy the CTMC generator sign and row-sum conditions.

Core idea impact: none.  This is a typing/regularity clarification that makes
the dynamics-first quotient statement more precise.

## FB-PER-01-001 — omega-limit strong invariance

Classification: **F2 pending exact source-assumption audit**.

The Lean lane distinguishes:

- forward invariance `phi_s(omega(x)) subset omega(x)`, available for an
  appropriate one-sided semiflow; and
- equality `phi_s(omega(x)) = omega(x)`, which is immediate from inverse-time
  transport for a two-sided flow but requires a separate reverse-inclusion
  argument/assumption in a genuine semiflow model.

Maintenance rule: do not replace a one-sided source theorem by a two-sided
flow theorem merely because the latter is easier.  Before v3.1, verify the
canonical hypotheses and either formalize the semiflow reverse-inclusion proof
under those hypotheses or split the theorem explicitly.

Core idea impact: none.  Persistent identity requires an invariant/recurrent
core, not artificial invertibility of every physical dynamics.

## FB-REC-02-001 — Dynkin-to-AC interface is essential

Classification: **F0/F1 boundary, currently source-aligned**.

Canonical v3 correctly does not infer recovery from a formal generator
inequality alone.  It explicitly requires generator-domain validity, Dynkin's
formula, localization limits and integrability sufficient to make
`m(t) = E W(X_t)` locally absolutely continuous.  The Lean lane has therefore
kept the scalar theorem at exactly the AC + almost-everywhere derivative level.

Next formalization obligation:

`generator drift certificate -> AC expectation trajectory -> scalar
integrating-factor/Gronwall bound -> W >= c d(.,V)^2 -> mean-square distance`.

If Mathlib lacks a process-specific Dynkin theorem at the needed generality,
the interface may be represented by an explicit standard-theorem certificate,
but the conclusion must not be assumed in disguise.

Core idea impact: positive.  It preserves the distinction between a symbolic
Lyapunov expression and an actually valid stochastic recovery certificate.

## FB-PER-03-001 — finite viability versus infinite nonexit event

Classification: **F0 proof-layer separation**.

Finite deletion recursion, stabilization, maximal controlled-invariant kernel,
and deterministic stationary one-step preservation are not by themselves the
full v3 P-PER-03 statement.  The source additionally asserts probability-one
nonexit for all discrete times and the converse characterization of states that
admit such a policy.

The clean proof architecture is:

1. finite viability recursion and stationary selector;
2. every finite-time marginal assigns probability one to the kernel;
3. path-law existence/consistency (standard process theorem);
4. countable intersection of coordinate-safe events has probability one;
5. reverse finite-horizon induction for any policy that stays safe forever.

Core idea impact: none; this strengthens the persistence/viability certificate
without adding a new objecthood axiom.

## FB-FAC-01-001 — primitive covariance must generate path covariance

Classification: **F0 source-matching obligation**.

P-FAC-01 is not proved by assuming the final path-law equality.  The primitive
transition, observation, intervention and reward transports must imply local
next-record kernel transport, and finite-horizon causal path-law covariance
must then follow by induction.  The reusable finite causal-law naturality
lemma is now machine-checked on the FAC branch; the remaining step is to wire
source primitive covariance into that local kernel hypothesis.

Core idea impact: positive.  It protects UEOT's representation-covariance claim
from becoming a circular assumption.

## FB-INFO-01-001 — discrete entropy clause is a separate standard bridge

Classification: **F0**.

The chain identity and epsilon-retention inequality do not yet prove the final
discrete clause of P-INFO-01.  The missing bridge is the standard
`I(M;Y) <= H(M)` inequality in a definition compatible with the existing
measure/KL formalization.  It should be proved/imported as ordinary information
theory, not introduced as a UEOT-specific axiom.

## Promotion rule

No item above changes the current 106-P-ID gate.  A proof branch may be green
while its P-ID remains pending.  Promotion requires exact source semantics,
o hidden stronger premise, official import, pinned build success, and proof-hole
/axiom audit.
