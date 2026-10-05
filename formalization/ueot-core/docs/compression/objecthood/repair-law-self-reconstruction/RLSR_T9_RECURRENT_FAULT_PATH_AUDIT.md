# RLSR-T9 — recurrent organizational fault-process audit

Status: **LOCAL PASS**

## Strengthening over T2/T6

T2 proved that one damaged state in the correctable codec fibre is repaired
before its physical action.  T9 upgrades that statement to a state-dependent
stochastic fault process applied before every safe macro-step.

The fault process may arbitrarily change:

- stored controller;
- program representation;
- which replica is damaged;
- the injected bad program value;
- all of the above as functions of the current recovered state.

The only envelope conditions are:

1. the fault does not directly move physical state;
2. the damaged representation still decodes to the intended program.

## Main theorem

Under that envelope, Lean proves the complete fault-then-safe PMF is exactly the
no-fault recovered PMF for every state.  Hence the resulting Markov kernels are
equal, the recurrent-fault kernel strongly lumps to the intended physical
stationary kernel, and the entire projected Ionescu--Tulcea path law equals the
no-fault reconstructed-program path law.

The concrete triple-repetition instance allows a new arbitrary replica index,
bad program value and controller corruption at every cycle.

## Remaining boundary

This does not tolerate faults that directly perturb physical state, or program
faults that leave the decoder's correctable fibre.  Those require a separate
homeostatic/fault-burden analysis rather than exact path masking.

## Validation

- focused Lean compile/build of `RecurrentFaultPathLaw.lean`: PASS;
- new-file theorem-surface warnings removed with explicit `omit`;
- umbrella `All.lean` compile: PASS;
- `git diff --check`: PASS.
