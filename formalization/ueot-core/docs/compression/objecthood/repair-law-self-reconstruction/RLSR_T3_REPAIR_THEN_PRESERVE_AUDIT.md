# RLSR-T3 — repair-then-preserve policy tightening

Status: **LOCAL PASS**

## Scientific correction

The first RLSR8 theorem required a reconstructed program to equal the selected
parent's physical-repair policy on all states and separately required target
preservation.  That is stronger than first-hitting semantics needs: behavior
inside the already-hit target cannot affect the first hitting time.

## New unified contract

`repairThenPreservePolicy` uses the parent's recovery policy outside `K` and a
canonical preserving viability witness inside `K`.  Lean proves:

1. it preserves `K`;
2. its expected first-hitting time is exactly the same as the original recovery
   policy for every initial state;
3. a program need only implement this composite policy at the *physical-kernel*
   level, not by matching action labels;
4. that single dynamics-level contract implies both program validity on `K` and
   membership in the original program-specific recovery basin whenever the
   original physical repair certificate is finite there.

Thus the old pair `himpl + hvalid` can be replaced by one semantically tighter
contract.
