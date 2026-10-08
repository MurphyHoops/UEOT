# Source comparison: predictive-state minimality is established prior art

Status: scoped literature cross-check for the deterministic UEOT/SISC result,
not an assertion of novelty or equivalence to the full external theories.
Date of comparison: 2026-10-08.

## Comparison targets (public published/background sources)

1. **Myhill–Nerode theorem**. Distinguishability by suffixes yields the
   canonical quotient of a deterministic automaton; its minimal automaton is
   unique up to isomorphism. This directly anticipates the deterministic
   response-over-all-future-input-words construction.
   Reference: https://planetmath.org/myhillnerodetheorem
2. **Shalizi & Crutchfield (2001), computational mechanics / causal states.**
   Future-conditional-distribution equivalence induces a minimal sufficient
   predictive state. This is stronger in stochastic predictive law content
   than the exact deterministic SISC module. Summary and theorem discussion:
   https://www.stat.cmu.edu/~cshalizi/dst/18/lectures/bonus/bonus.html
   and https://pmc.ncbi.nlm.nih.gov/articles/PMC2849313/ .
3. **Predictive State Representations (2003–2004).** Controlled system
   states can be represented using predictions about action–observation tests.
   Test discovery and prediction learning are separate problems, and the
   existence of distinguishing tests is not itself a tractable algorithm.
   See https://mlanthology.org/icml/2004/james2004icml-learning/ .

## Consequences for UEOT claims

- **No originality claim** for the abstract equivalence/quotient/minimality
  principle. It is an already-known mathematical structure.
- UEOT contribution *in this code change* is a typed, compile-checked reuse
  of its existing M-QD/M-RS/Gauge interfaces with a process-generated state
  (rather than an arbitrary compatible quotient) and a finite-state
  per-pair test existence theorem, integrated without modifying frozen Core.
- A genuinely new UEOT-specific contribution would require proving an
  independently testable bridge from this behavioral state to **formation,
  constitutive persistence, repair, causal provenance and physically anchored
  objectives**, ideally with new quantitative bounds or no-go theorems.
- Beware treating *all finite interventions* as experimentally available:
  response test selection, process learning, probability law estimates,
  intervention feasibility and source token coverage all need dedicated work.

The literature comparison reinforces the result as a useful *organizing
principle*, and simultaneously **lowers** its claim of original scientific
discovery. It does not show that UEOT has solved the physical identity or
universal truth problems.
