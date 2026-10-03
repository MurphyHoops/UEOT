# Track O / AR6 — General Causal Completeness Audit

Status: **LOCAL AR6 CLEAR — G3 BOUNDARY RETAINED**

Tracker: #238. Counted-core impact: **NONE**.

## Classification result

AR6 does **not** promote deterministic-stationary completeness against arbitrary
causal randomized policies. Instead it retains the roadmap's permitted G3
boundary, now with exact machine-level semantics.

The repository already contains an Ionescu--Tulcea construction for arbitrary
complete-history randomized causal policies. AR6 therefore builds the exact
bridge from the Objecthood PMF controlled model into that kernel interface and
defines:

- `GeneralCausalAlmostSureRepairable`: existence of an admissible arbitrary
  causal randomized policy whose exact physical path law hits `K` almost surely;
- `DeterministicStationaryFiniteExpectedRepairable`: existence of a stationary
  deterministic policy with finite canonical expected hitting time;
- `GeneralCausalToStationaryCompleteness`: the exact missing implication from
  the first class to the second.

AR3 is re-expressed as a theorem proving completeness of
`maximalStationaryRepairPolicy` **within** the deterministic-stationary
finite-expectation class. The broader `GeneralCausalToStationaryCompleteness`
proposition is deliberately defined but not assumed or asserted.

## Why G3 remains

The two sides currently use distinct but exact semantic constructions:

1. AR0--AR5 use canonical expected hitting time for a homogeneous stationary
   Markov kernel on `X`;
2. the general side uses a time-tagged complete-history carrier, arbitrary
   randomized causal action kernels, and a physical-state pushforward of its
   Ionescu--Tulcea law.

A valid closure theorem requires a memoryless-determinacy argument connecting
general almost-sure reachability to a deterministic stationary policy. That
bridge is not present in the current Objecthood theorem graph. Importantly,
almost-sure hitting and finite expected hitting are also different witness
properties for a general nonstationary policy, so silently identifying them
would be a semantic strengthening.

The scientifically correct AR6 result is therefore: **stationary completeness
is proved exactly in its established scope; general causal completeness remains
the named G3 theorem boundary.**

## Second-pass review / reflection

- the broad policy class is genuinely randomized and complete-history causal;
- its path law is the existing exact reflexive Ionescu--Tulcea construction,
  not a support-tree surrogate;
- the PMF controlled kernel is proved Markov rather than postulated;
- no converse bridge is inserted as an axiom, assumption, certificate field,
  or theorem premise;
- retaining G3 is explicitly allowed by the #238 AR6 gate and prevents a false
  overclaim while leaving a precise future theorem target.

Disposition: **CLEAR / G3 retained**.

## Validation

- focused compile and module build: **PASS**;
- Objecthood / Compression / full UEOT builds: **PASS**;
- proof-escape scan: **CLEAR**;
- selected axiom audit: only `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression and 3-path governance simulation: **PASS**;
- `git diff --check`: **PASS**.

AR6 disposition: **CLEAR / eligible for its own local commit**.
