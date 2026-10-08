# SISC N2.1 — observation-time bridge closed at one step

Status: **kernel-checked local conditional theorem**. Frozen Core v3 unchanged.

Previous work found a real semantic mismatch: `controlledOutputTrace` emits from the **current** state before a controlled transition, whereas `FiniteBayesBelief.observationLaw` emits after the action from the **next** state. A two-state flip process showed that treating those as the same time-indexed experiment yields probability 1 versus 0.

`SISCObservationOrderBridge.lean` now supplies an explicit one-step alignment:

`P_Bayes(o | δ_x,a) = ∑_y K(x,a,y) · F_y([(a_dummy,o)])`,

where the right side uses the next microscopic state y and a pre-transition trace observation. The dummy action is unused by this last first-observation event; the proof also establishes invariance under any change to that dummy action.

For the old flip counterexample, the shifted pre-trace sum is **0**, matching the post-transition Bayes probability **0**. The unshifted pre-action readout **1** remains correct for its different experiment.

This is a **typed bridge across two pre-existing verified components**. It proves neither that their full multi-step joint word laws agree without appropriate reindexing nor that the microkernel/emission model is identified from observations. These remain separate tasks.

Important modeling principle: state mapping, action mapping, observation mapping, and observation timing all need explicit compatibility checks before a purported UEOT universal diagram can be declared commuting. This is a semantic correctness condition, not a new physical conservation law.
