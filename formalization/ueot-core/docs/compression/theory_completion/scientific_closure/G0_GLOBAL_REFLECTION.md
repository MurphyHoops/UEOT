# G0 Global Reflection — after R0 / FBT0

Status: **PASS WITH SCOPE REVISION**

## Findings

1. FBT is not already a theorem under another name.  Existing same-parent
   results preserve a supplied identity; structural identity remains open.
2. Formation is set/fibre-valued.  Any new theorem that chooses one parent
   without a declared selector would erase the existing parent-completion no-go.
3. `ParentBindingLipschitz` is a real domain premise.  Generic Core may transport
   its consequences but may not claim to derive one universal `L_bind`.
4. P10 already closes fixed-belief/action general-observation posterior
   measurability.  A stronger C1 target is joint measurability across
   belief/action plus a full belief-state Markov kernel, not another fixed-action
   wrapper.  Mathlib's parameterized `Kernel.condKernel` makes this target
   constructible when the observation sigma-algebra is countably generated.
5. `ReflexiveStateSpecialCases` already proves the generic adapter
   “measurable update + Markov noise ⇒ Markov kernel”.  Recreating that adapter
   in Scientific Closure would be theorem-count inflation rather than progress.

## Scope revision

- C1 must split the port rather than treating it as all-or-nothing: prove the
  countably-generated-observation parameterized posterior/belief-kernel theorem,
  and retain arbitrary measurable observations as the stronger open boundary.
- C2 becomes the first new formal package: deterministic certification logic
  around intervals, abstention, protocol coverage and formed-family recovery.
- C4 structural continuation must return identity/continuation as a conclusion;
  terminal theorems whose main premise is `SameObject` do not close C4-06.
