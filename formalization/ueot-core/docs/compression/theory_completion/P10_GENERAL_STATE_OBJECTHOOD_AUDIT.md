# Theory Completion P10 — General-State Objecthood Audit

Status: **LOCAL COMPLETE / PARTIAL EXPLICIT BOUNDARY / TRACK TC / UNCOUNTED**

Immediate local dependency: rewritten P9 exact head
`463e7beb101f66ad5af3933830c2d4a387554268`.

## Reconciliation with Core v3

P10 does **not** claim that Core only had finite predictive states. Core's
P-PRED-01 formal surface already handles measurable dependent future spaces and
a countable protocol family. Core also already contains a Standard-Borel
posterior/disintegration interface.

The actual P10 increment is the reusable general-observation belief-update
surface in `GeneralStateObjecthood.lean`.

## Proved result

For Standard-Borel latent state `Z`, arbitrary measurable observation space `Y`,
a probability current belief, and Markov transition/observation kernels:

- the predictive observation law is a probability law;
- the regular posterior readout `Y -> Measure Z` is measurable;
- pushing the observation law through that readout gives a probability law on
  the measure-valued next-belief space;
- composing the posterior kernel with the observation law recovers the predicted
  latent law exactly.

`p10_terminal_generalState_belief_update` packages these facts and has no finite
or discrete observation assumption.

## Explicit remaining boundary

This is a fixed-current-belief/action theorem. It does **not** prove joint
measurability of `(belief, action, observation) -> posterior belief`, hence it
does not by itself construct a Markov kernel on the whole infinite-dimensional
belief space. It also does not solve noncompact occupation tightness, general
GOA existence, or all general-kernel object-realization questions.

Therefore P10's numbered stage contract is locally closed by a real general-state
increment plus an explicit stronger boundary; the full Core §31.2 general-state
open port remains open.

Claim class: **THEOREM + PARTIAL/EXPLICIT BOUNDARY**.
