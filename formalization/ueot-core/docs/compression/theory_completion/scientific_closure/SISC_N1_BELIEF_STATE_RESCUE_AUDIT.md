# N1.5 — failure of trace-predictive Markov quotient versus belief-state rescue

Status: **FORMAL FINITE MODEL BRIDGE, NOT REAL-WORLD OBJECTHOOD CLOSURE**.

The compiled `SISCStochasticTraceNoGo.lean` now gives a stronger negative
result than the immediate-output counterexample: a concrete finite stochastic
hidden-state process has states `0` and `1` with **identical laws of every
finite output word** but unequal one-step transition probabilities into a
third **predictively distinct** hidden-state class. Hence the equivalence
induced by all these finite observational trace laws is **not strongly
lumpable**. There is no exact memoryless Markov kernel on that raw quotient.

This directly falsifies an unjustified stochastic generalization of the
deterministic `SISCFutureResponseCore` construction. Finite predictivity and
one-step Markov lumpability require separate examination: stochastic state
mixtures may be behaviorally identical without sharing latent class masses.

`SISCStochasticBeliefBridge.lean` gives the conditional remedy by mapping
the **same** finite controlled kernel to the existing `FiniteBayesBelief`
model with one trivial latent parameter and deterministic emission readout.
No new Bayesian update rule is invented: P-REF-02 already proves normalized
observation laws, positive-evidence posterior updates and explicit
`modelConflict` on zero-probability evidence.

The bridge verifies in Lean that even the six-state observational-quotient
no-go still admits normalized output prediction for *every full finite
microstate belief*. This is not a contradiction: **full Bayesian beliefs are
more informative than the observational quotient**. This guarantee does not
make belief-space dimension minimal or make filtering possible without a
correct, calibrated transition/emission model.

## Refined core picture

1. **Deterministic process:** all-future response equality is an action
   congruence automatically; canonical predictive quotient is closed.
2. **Stochastic process:** equality of output-trace laws does not necessarily
   imply strong lumpability; an exact Markov quotient requires all class
   transition masses to be source-fibre invariant.
3. **Observable criterion:** a registered finite test family with a linear
   reconstruction of destination-class indicators, plus matching source
   expectations, implies strong lumpability.
4. **Robust criterion:** with class-indicator reconstruction error `δ` and
   one-step test mismatch `ε`, the deviation of class-transition masses is at
   most `2δ + ε Σ_i |c_i|`.
5. **Fallback representation:** the full latent-state belief is a valid
   (not necessarily minimal) stochastic predictive state in the supplied
   Bayesian model. It needs honest model-conflict treatment.

This structured dichotomy is a stronger research conclusion than the claim
that the same set-level minimal quotient always works. The claim remains
limited to exact finite models and conditional sensor/test calibration;
physical object identity, endogenous provenance, long-run viability and
goal emergence remain OPEN.
