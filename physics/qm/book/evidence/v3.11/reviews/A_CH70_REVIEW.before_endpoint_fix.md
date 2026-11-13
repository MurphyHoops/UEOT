# A: independent review of integrated Chapter 70

Review date: 2026-11-14 (Asia/Shanghai). Reviewer: native research agent A.

## Scope and current verdict

Reviewed the actual integrated files under
`/workspace/scratch/314d4fc9c52a/repo/physics/qm/book/`, not the old recovery
checkout or the intermediate combined fragments:

* `UEOT_PHYSICS.md`
* `UEOT_PHYSICS.en.md`

The scope is sections 70.1, 70.2, 70.3, 70.7, 70.8, 70.9 and 70.10, including
A's three claims and their interface with C. B's sections 70.4–70.6 have
a separately requested narrow expansion review, reported in
`A_B_EXPANSION_REVIEW.md`, and are not wholly re-certified by this text
review. B's full mathematical source and exact numerical artifacts were
separately reviewed in `work_a/A_REVIEW_OF_B.md`.

**Final verdict: PASS_INTEGRATED_TEXT_AND_DECLARED_A_C_SCOPE.** All three
requested editorial/scientific-scope corrections, both additional
clarifications, and the final tensor/unit typing clarification have been
read back in both actual book files. The final mathematical reflow was
also read back. A has not modified either book.

The read-back identities, selected-section hashes and programmatic checks
are in `A_CH70_TEXT_CHECK.json`, with the post-correction identities in
`A_CH70_COMPLETION_CHECK.json`. The final frozen-source identities are in
`A_CH70_FINAL_TEXT_CHECK.json`; this last receipt supersedes the earlier
source hashes without relabeling their earlier review identities.

## 1. A's three results survive integration without changes of scope

The initially integrated sections 70.2, 70.3 and 70.7 matched A's frozen
bilingual fragments after normalization of Markdown math delimiters and
section numbering. The final text is deliberately **not byte-identical**
to those fragments: section 70.2 now contains the explicit tensor/unit and
composite-central-block typing clarification requested during review, and
long displays use equivalent aligned/gathered reflow. These are proof
typing and presentation clarifications, not new results or new physics
executions. A's sections now contain 16 display equations, identical
between languages. The original scope limitations have been retained.

### C-QSEL-02

The complete operation library is a declared **reachable** library; its
closure is not confused with access to every state of the completed
theory. The proof preserves every finite generated circuit, including
parallel references and full labels. Its purification counterexample is
quantified over finite direct-sum matrix auxiliary systems, as stated.
The text explicitly permits the minimal reachable response quotient to
delete an unreachable sector as representation redundancy. It does not
claim a new observable sector, failure of every Core principle, or that
the selected complex model is false. Classical, real, complex and
superselected candidates remain distinguished.

The English preserves the same quantifiers and the distinction between a
reachable operational target and a global theory. The external CDP
reconstruction background is not reduced to two informal principle names.

The final clarification uses the true tensor product of the completed
elementary algebras. Its all-visible joint central block is the original
joint algebra; the direct sum of every other central block is retained as
the hidden part. The tensor unit remains C and discarding is total matrix
trace. Arbitrary multi-input/multi-output complete CP generators have an
explicit replacement extension on hidden input, including scalar input or
output. Identity and discarding may use their exact structural extensions.
Actual composition and tensor products then generate the circuits. This
does not treat the objectwise construction A -> A direct-sum C as a strong
monoidal functor, nor require every original operational equality to hold
on newly added unreachable states. The induction concerns reachable
circuits, so the clarification repairs a potential type ambiguity without
enlarging the global-selection conclusion.

### P-TOM-01

Each of the d² effects is a separate binary setting, not one incomplete
purported POVM. Input and output duals are correctly distinguished. The
weighted inequality is for the complete recorded map and every finite
untouched reference. The constants 17.660254..., 101.530377... and
333.579068... are sufficient constants, explicitly not claimed optimal.

The external d=2 fixed-protocol map is correctly separated from the large
internal bath carrier and from a process tensor allowing different
intermediate operations. Four preparations and four binary effects are a
sufficient complete external test family, not the two-parameter calibration
already executed. SPAM, gauge, leakage, physical-fit residuals, rare
acceptance and the sufficient-not-necessary shot budget are all retained.

### P-QMEM-02

All history-carrying registers count toward D, including a readable past log
and a varying accessible reference. The future operations are identical
for the two histories. The causal-break diagnostic is separately declared
and is not used to replace the frozen three-slot source. The nonzero phase
and rank-two result apply analytically to the whole lambda interval;
three numerical values are not used as proof of the universal assertion.
The text claims a necessary dimension bound, not a CP compression theorem
or a sufficient dimension for every bath history.

## 2. A/C interface and mathematical equivalence

The eight display equations in section 70.8 are identical between
languages. Together with A's sixteen equations, this gives **24 identical
display equations** in the reviewed A/C sections. The final chapter has
44 display equations, all identical between languages. All nine new stable
identifiers occur in the same order in the two chapter bodies. Equation
identity is a textual integration check, not an extension of the scientific
review to every aspect of B's sections.

The structured calibration has two explicitly declared unknowns, lambda
and shared symmetric detector visibility eta. The zero-time anchor and a
nonzero-time setting break their single-setting equivalence. Unknown
thermal occupation, readout bias and unrestricted drift remain outside
the identified model. This does not silently promote the calibration to
arbitrary instrument tomography.

The confidence set is nonempty and distinguished from its rectangular
outer enclosure. Coverage is a statistical theorem under stated sampling
assumptions, not an empirical assertion inferred from one synthetic seed.
The false-rejection allowance is the sum of calibration and held-out
failure probabilities. Non-rejection is not claimed to identify a unique
physical mechanism.

The displayed error composition was independently recomputed with exact
fractions:

\[
5.1(0.007170144244)+0.00001344+10^{-8}
=0.0365811856444<0.036581185645,
\]

\[
0.0365811856444+0.007740457121/2
=0.0404514142049<0.040451414205.
\]

The visibility contribution is correctly divided by two for a complete
binary readout distribution: the l1 change of the two signs, summed over
all subnormalized record blocks, uses total block mass one. No extra
factor equal to the number of records is required.

There is a useful conservatism to state explicitly: the certified nominal
Choi repair already has an error below 10^-8 relative to the **infinite**
source. Thus parameter stability plus that pointwise bound is already
sufficient. Retaining the uniform K20 analytic term is harmless additional
budget, not a newly required independent remainder. The displayed upper
bound is mathematically valid either way. The accounting clarification has
now been read back in both final book files, without changing the frozen
numbers or decisions.

The strong baseline is the standard persistent model under the same
data, actions and robust rule. Reset is an ablation. The conclusion
`EQUIVALENT_NO_ADDED_GAIN` is not replaced by a comparison only against
that weaker ablation. Synthetic records, author-published processed
observables and matched device evidence remain separate categories.

## 3. Review findings and correction status

| Finding | Why it matters | Read-back status |
|---|---|---|
| Both 70.10 versions contained a literal TAB followed by `imes` instead of LaTeX `\\times` | This would render the displayed correction magnitude incorrectly | Corrected by master; zero control characters in the reviewed chapter |
| English 70.9 still said `No` + newline + `failed attempt was filtered out.` while Chinese specifies no initial projection filter and complete source failure records | The broad English statement could be read as a claim about all failed computation attempts and omits the declared source-operation meaning | Corrected and read back: no initial projection filter is used, and all failure records of the source itself are retained |
| 70.10 offered only a new physical prediction or a resource improvement as a next meaningful result | This excluded the user's independent non-circular premise-reduction route, even when standard predictions are reproduced | Corrected in both languages: premise reduction and exclusion of competing theories are now retained |
| 70.1 says R remains untouched throughout, while terminal testers include XX on S/R | Standard reference language is mathematically understood during the channel, but an explicit terminal-readout exception prevents a reader from inferring a contradiction | Clarified and read back in both languages: R is untouched during evolution/instruments/feedback; the declared terminal tester may read S/R |
| K20 analytic budget and pointwise Choi certificate have overlapping truncation coverage | The numerical inequality is safe; readers should not infer an unsupported independent repair-to-Galerkin edge | Clarified and read back: the K20 term is a conservative uniform analytic allowance because the pointwise interval certificate already compares to the infinite source |
| The objectwise completion formula could obscure composite central blocks and the tensor unit | A direct-sum completion is not automatically a strong monoidal functor | Explicit true-tensor, unit-C, total-trace and arbitrary multi-input/output CP-generator extensions inserted and read back in both languages |

All six changes were actually re-read in both book files. The English
failure sentence initially did not change because `No` and `failed` occur
on separate source lines; the master was given that exact cause and then
corrected it. The final read-back has no control characters in Chapter 70.
No requested change was marked complete without reading the changed source.

The final reflow only adds aligned/gathered line breaks to the tester
constants, the all-input truncation display and the parameter enclosure.
The source equations remain algebraically unchanged and bilingual-equal.
No numerical verification, synthetic sample generation or physical test
was rerun for this final textual read-back.

## 4. Root framing and remaining proof boundaries

Sections 70.1 and 70.10 correctly distinguish source recovery from new
execution; independent physical inputs from Core; conditional mathematical
results from numerical representation and synthetic sampling; and internal
separate-role review from external peer review. The source contract hash
matches the actual integrated JSON:

`685d373bb5a70a677fd4d110cb81c6624260de95ea39cc60070a8f4bd9f19668`.

The new-result inventory is nine named claims, not new Lean proofs. The
historical objects are not described as newly executed. The unification
limits, device qualification limits and broader field/gravity/continuum
responsibilities remain explicit. Chapter count is not treated as a
fraction of physics solved.

This is a textual and mathematical integration review. The separately
completed visual check is recorded in `A_PDF_REVIEW.json`: A actually viewed
Chinese physical pages 240–244 and 255–259 and English physical pages
304–310, 17 images in total, with verdict PASS_SCOPED. That receipt binds
both PDFs, both sources and each inspected page image; it does not claim a
whole-book visual review or extend this textual review's scientific scope.

Final whole-book source SHA256 identities at this read-back:

* Chinese: `4f336843b0b0b2b0d5f2553cc7f4ce34268c9ba403e835dce7320ef36baf133a`
* English: `e8f2652e2959e05b665318675dd757373d7c442ab0bdbd576f50616d58a12b3a`
