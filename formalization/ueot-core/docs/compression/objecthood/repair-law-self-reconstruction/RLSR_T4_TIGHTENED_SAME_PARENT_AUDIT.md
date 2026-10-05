# RLSR-T4 — tightened same-parent terminal audit

Status: **LOCAL PASS**

The strengthened endpoint replaces the original RLSR8 pair of assumptions
(global action-level implementation of the parent's repair policy plus a separate
preservation premise) with one dynamics-level program contract implementing the
canonical `repair outside / preserve inside` policy.

It also replaces the mutable-mode kernel with `safeRepairKernel` and explicitly
projects every recovered RLSR target state into the pre-existing O1
`legitimateConstitutiveDomain`.  Hence the strengthened target refines, rather
than duplicates, earlier Objecthood legitimacy.

The final theorem simultaneously gives exact one-step fault masking before the
physical action, the same selected parent's Track-X semantic bound, almost-sure
eventual-permanent physical recovery, safe-joint closure, and O1 legitimacy of
all recovered target states.
