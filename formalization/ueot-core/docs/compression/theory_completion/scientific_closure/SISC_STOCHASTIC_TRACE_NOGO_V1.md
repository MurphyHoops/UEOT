# N1: Full predictive trace agreement does NOT imply Markov quotient closure

Status: **LEA​N-CHECKED SIX-STATE COUNTEREXAMPLE** (local post-Core research).
This distinction is known in probabilistic trace-versus-bisimulation theory;
the contribution of this source module is an explicit machine-checkable
counterexample inside UEOT's finite controlled kernel framework. No physical
identity proof or scientific-final promotion is claimed.

## Six-state controlled countermodel

States `0,1,2,3,4,5` emit a deterministic Boolean observation. All emit
`false` except state `5`, which emits `true`. The only action is `()`.

The nonzero one-step transition probabilities are:

| From | To | Probability |
|---|---|---:|
| 0 | 4 | 1 |
| 1 | 2 | 1/2 |
| 1 | 3 | 1/2 |
| 2 | 2 | 1 |
| 3 | 5 | 1 |
| 4 | 2 | 1/2 |
| 4 | 5 | 1/2 |
| 5 | 5 | 1 |

The law of an entire observed prefix `w ∈ List Bool`, given microscopic
initial state `i`, is a recursive sum over all microstate paths:

`L(i,[]) = 1`;
`L(i,b::w) = (if output(i)=b then ∑_j K(i,j) L(j,w) else 0)`.

There are two **literal all-length** identities proved in Lean:

1. `L(4,w) = (L(2,w)+L(3,w))/2` for every `w`. The predictor of a
   *single intermediate state* aliases a distributional mixture of two
   distinct other states.
2. `L(0,w) = L(1,w)` for **every finite future observation word**. One
   starting state goes certainly to state 4, the other mixes states 2 and 3.

However, `L(2,[false,false])=1`, `L(3,[false,false])=0`, and
`L(4,[false,false])=1/2`. Thus the three reachable predictive classes are
different. From equivalent initial states 0 and 1, the probability of moving
into the class of state 4 is respectively **1** versus **0**.

Consequently the partition defined by *all future output-trace laws* fails
the strong-lumpability criterion even though states 0 and 1 are perfectly
predictively trace-equivalent.

## Source-level audit chain

- `traceCounterexampleKernel` is finite and satisfies positivity and exact
  row normalization, proved via Lean rather than asserted as an axiom.
- `stochastic_trace_midpoint_alias` is a theorem for arbitrary list length.
- `stochastic_all_future_trace_equivalent` is a function equality of whole
  observation-word distributions, **not** a finite-horizon check.
- `stochastic_trace_mid_not_extreme` uses two-step witnesses to certify the
  destination classes are really distinct.
- `all_future_trace_equivalence_not_markov_lumpable` derives a literal mass
  contradiction `1=0` from hypothetical strong lumpability.
- `all_future_trace_quotient_kernel_does_not_exist` applies the formally
  proved finite-quotient iff theorem to reject even an exact real-valued
  state-to-class transition factorization, hence any exact Markov kernel.

## Scientific interpretation

The process-generated *deterministic* predictive quotient of the previous
stage was automatically action-recursive. **Stochastic predictive equivalence
is fundamentally more subtle**: distinct mixtures of predictive components
can have the same observable trace law. A state representation that retains
only the equivalence class of the current *microscopic token* does not
necessarily admit an exact Markov kernel across those classes.

This is why the scientifically safe next UEOT backbone must distinguish:

1. observational predictive equivalence (what traces can tell apart);
2. strong Markov lumpability (what class-transition law is well-defined);
3. filtering/belief state over hidden classes (what posterior information
   must be retained for recursive prediction under partial observation);
4. causal lineage and physical objecthood (additional, independent evidence).

Prior literature distinguishing probabilistic trace/testing equivalence
from bisimulation and lumpability includes Bernardo (2006–2007):
https://www.sciencedirect.com/science/article/pii/S1571066106004178
and https://www.sciencedirect.com/science/article/pii/S1567832607000057 .

### Research priority after this no-go

Prove the **precise additional sufficiency** of class-indicator spanning
tests, or construct a recursively sufficient Bayesian belief state retaining
necessary mixture coordinates. Test identifiable interventions and protocol
coverage separately. No universal predictive-quotient Markov closure is
permitted without one of these strengthening bridges.
