# N1: a closed finite-dimensional predictive linear lift after the trace no-go

**Lean-verified conditional mathematical result.** The construction does not
claim a new mathematical principle beyond predictive state representations,
observable operator models or weighted automata; it gives a typed post-Core
integration and an exact positive alternative to the local six-state no-go.

## 1. Two types of closure must not be confused

The exact six-state result in `SISCStochasticTraceNoGo.lean` proves that
all-future observation trace equivalence does **not** imply ordinary
Markov lumpability of the equivalence-class state. This does not mean the
observable process has no finite-dimensional recursive representation.

For a finite stochastic kernel K and deterministic output map `read`, define
the response to an action-observation word as

`F_x([])=1`,
`F_x((a,o)::w) = 1_{read(x)=o} ∑_y K(x,a,y) F_y(w)`.

Let `V = span_ℝ { F_x : x∈X }` inside the ambient real-valued function
space over all finite action-observation words. This is a *linear* predictive
carrier, not the set of observational equivalence classes.

For each registered event `(a,o)`, define the prefix/shift operator
`P_(a,o)(f)(w) := f((a,o)::w)`.

## 2. Machine-checked conclusions

- `prependEventLinear` is a genuine ℝ-linear operator on the full future
  response function space.
- `shifted_source_trace_in_span` proves each generating trace is mapped
  into `V`, since its prefix response is a linear mixture of the generators
  or zero for an impossible current observation.
- **`controlled_trace_span_shift_invariant`:** *every* vector in `V`
  remains in `V` under every registered action-observation shift. This is
  derived by module-span induction and does not require `StrongLumpability`.
- **`controlled_trace_span_finrank_le_card`:**
  `finrank_ℝ(V) ≤ |X|` for finite X. The full ambient word-function space can
  be infinite dimensional, but this predictive realization is finite rank.

The result is exact, for *all finite future words*, without assuming an
ordinary Markov chain on output-predictive equivalence classes. In
particular, its positive conclusion is compatible with the six-state no-go.

## 3. What has and has not been derived

**Derived:** a process-generated finite-rank invariant linear predictive
space, with exact event update linear maps and an upper bound on dimension.

**Not derived:** the minimal dimension (only ≤|X|), a numerically stable
constructive basis, probabilistic positivity of *arbitrary vectors* in V,
Bayesian normalization after observing an event of nonzero probability,
online inference from finite noisy trajectories, ontic identity, a causal
parent transport or independently grounded purpose/GOD/GOA semantics.

The linear state might contain signed function combinations which are not
physical probability states. It is therefore invalid to identify the whole
subspace V with a space of probability measures or physical objects.

## 4. Prior-art and conceptual positioning

The existence of low-dimensional linear predictive/operator realizations
is established literature. In particular:

- Singh, James and Rudary, *Predictive State Representations: A New Theory
  for Modeling Dynamical Systems*,
  https://arxiv.org/abs/1207.4167 .
- Balle, Quattoni and Carreras, *Spectral Learning Techniques for Weighted
  Automata, Transducers, and Grammars* (2014),
  https://aclanthology.org/D14-2002/ .

For UEOT the significant design decision is a separation of levels:

`process → finite linear predictive closure`

does not by itself imply

`stochastic Markov quotient → persistent object → physical identity`.

When a real stochastic quotient is required, use the independently proved
strong-lumpability and observable test-spanning gates. When only exact
predictive recurrence is required, the linear response span provides a
stronger and more generally available mathematical interface.

All results remain on the additive local SISC branch and do not alter the
governed 106/106 Core, counted compression, C7 external evidence or cloud
release status.
