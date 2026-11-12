# A bilingual Chapter 68 review

Review type: internal native-AI scientific/editorial review.
This is an actual reading of both complete drafts:
`recovery_reviews/root/ch68.zh.md` and `recovery_reviews/root/ch68.en.md`.
The existing Chapter 67.5 sentences in both integrated book sources were also
read. At this review's first reading, those book sentences were still unchanged;
the new draft described the intended correction. No existing code tests were rerun.

## Initial verdict

The two languages contain the same scientific chain, six result IDs, parameter
set, pulse order, record policy, radical certificate, counterexamples and evidence
limits. I found no changed-language theorem or disagreement in displayed formulas.
The core proofs match the already reviewed A/B derivations. Several local changes
are nevertheless necessary before publication to make the hypotheses and domain
boundaries explicit. They are listed below with concrete replacements.

## Required scientific/editorial corrections

### 1. State the input and normalization premises before P-OPT-04's formula

Section 68.3 currently uses `rho_N` and its error bound before explicitly fixing
`Tr(G rho_S)<=nbar<N+1`. Bounded mean alone does not ensure that a particular
cutoff has positive probability. The premise appears later in 68.4, but it should
precede the theorem where it is needed.

Add, in both languages, immediately before the displayed instrument equations:

- Chinese: “取非负整数 N，最大时槽数 L，及满足
  Tr(Gρ_S)≤n̄<N+1 的联合密度算子。于是 s_N>0，并定义有限坐标态
  ρ_N=(J_N†⊗I_R)ρ_SR(J_N⊗I_R)/s_N。嵌入 ι 在每个记录块上作用为系统的
  经 J_(N+2L) 到共同物理 Fock 空间的规范嵌入，并在记录及参考上作用为恒等。”
- English: “Fix a nonnegative integer N, a maximum slot count L, and a joint
  density satisfying Tr(G rho_S)<=nbar<N+1. Then s_N>0 and define the finite
  coordinate density rho_N=(J_N† tensor I_R)rho_SR(J_N tensor I_R)/s_N.
  The embedding iota acts blockwise through J_(N+2L) into the common physical
  Fock space, leaving the record and reference unchanged.”

The slot bound L should be defined, because the formula uses uniformly padded
`N+2j` windows. Optionally explain that these pad the smaller actual windows
`N+2 count_1(h)`; zero/failure slots need not inject excitation.
For a general untruncated input the ideal output may still have infinite tails.
Only the projected-input equality or supported numerical example has both
outputs contained in the common finite terminal carrier; the general error
comparison uses the physical Fock carrier.

Also replace the leftover Chinese phrase “任意有限 untouched 参考” with
“任意不受操作的有限正维参考”.

### 2. Handle zero-probability failure without normalized conditional objects

Section 68.4's operator formula is already correct: the failure reference is
subnormalized, so it is the zero operator when failure probability is zero.
The prose about convex combinations of two conditional means must avoid defining
the rejected mean when that outcome has zero probability.

Add an explicit sentence in both languages: if the failure probability is zero,
the failure block is zero and no normalized failure-reference state or rejected
conditional mean is defined; the energy conclusion is immediate. When both
outcomes have positive mass, the stated convex-combination proof applies.

Change “两个非零特征值” / “the two nonzero eigenvalues” to
“至多两个非零特征值” / “at most two nonzero eigenvalues”. This includes zero tail
without a false rank assertion.

The same rule applies to the broader prefix statement in 68.5: only normalize
positive-mass reachable prefixes; zero-mass prefixes contribute zero. The actual
four successful Q paths are positive, but the common complete alphabet also has
zero failure blocks.

### 3. Write the unbounded-generator estimate on its actual graph domain

Finite mean excitation guarantees a purification in `D(B)`. It need not guarantee
membership in `D(B^2)`. The displayed expression `<psi,B^2 psi>` is legitimate
only if expressly understood as a quadratic form; the draft's notation can be
read as an operator-domain expectation.

The direct replacement in both displayed formulas is

`||(exp(-i beta B)-I)psi||^2 <= beta^2 ||B psi||^2`.

The following proof can say `psi in D(B)` and identify the right side with the
quadratic form of `B^2`. This requires no stronger assumption and preserves the
proved bound. The operator identity `B^2=G+I-2P_e` can be used in that form sense.

### 4. Identify which process has success probability s_N s^2

Section 68.7's `p_actual=s_N s^2` is correct only for a complete attempt of the
filtered **original source**. The surrounding theorem concerns two compiled
implementations as well; both compiled instruments have success probability
`s_N`, because they do not reintroduce original-source failure after filtering.

Use explicit labels, for example

`p_source_attempt=s_N s^2`, `p_compiled_attempt=s_N`.

Alternatively state the distinction immediately adjacent to the formula. Do
not allow the generic `actual` label to become a denominator for compiled cost.

### 5. Qualify compiled blue-call counts

In 68.9, compiled selected and scheduled counts `s_N` and `2s_N` refer to the
matched-blue compiler. The blue-omitted compiler has zero blue calls under either
schedule. Add “matched” to those two subscripts or explicitly explain this before
the equations. Keep the final `mu/(s_N s^2)` formula limited to original-source
attempts, as the following paragraph already does.

### 6. Fix the operator realization in the simultaneous counterexample

B's final proof specifies `H_sim=sigma_x tensor X`, where X is the canonical
self-adjoint quadrature; the identity with `A+B` is on the finite Fock core.
Use that definition in both chapter drafts and write the exponential as
`exp(-i t H_sim)`. This avoids treating self-adjointness as automatic for an
unspecified sum of unbounded operators. State its direct-sum domain in the
sigma_x basis, or point explicitly to the specified canonical realization.

The Chinese “位置象限算符” is an incorrect translation of “position quadrature”.
Use “位置型正交分量算符” or “与位置成比例的振子正交分量”.

### 7. Name the two resolvent shifts

In 68.2, the inverse norm at most one is for `B+iI` and `B-iI`. Generic nonreal
shifts have a different resolvent bound. The prose should explicitly say these
two shifts in Chinese and English, matching B's full proof.

## Inherited sentence correction and evidence continuity

The current English sentence read in Chapter 67.5 was:
“A general energy-bounded input can have a larger normalized energy budget after
passing.” The corresponding Chinese sentence has the same overbroad scope.

A correct bilingual replacement distinguishes general postselection from the
specific low spectral filter. For example:

- “一般后选择可能提高归一能量预算；本例的理想低谱过滤不会提高通过后的
  平均激发，第68.4节给出证明。”
- “General postselection may increase normalized mean excitation; this ideal
  low-spectral filter does not increase it on passage, as proved in section 68.4.”

Preserve the adjoining warning about no free fresh copy of an unknown input.
Record this one localized correction explicitly in the inheritance checker;
do not claim that every old chapter's bytes stayed identical. Old result objects
and historical execution files retain their original identities.

## Items already correct

- Common output records include physical preparation failure and all seven
  source labels, including zero target failures.
- The system-only failure reset retains the correct unnormalized conditional R
  output; no operation resets R to a new fixed or unconditional marginal.
- `V1=B_beta U1` has the same red-before-blue order in both languages.
- The omission estimate uses no-blue prefixes and the deployed policy's expected
  count one; it does not use the target's `2q` or the raw source count.
- The source acceptance effect is derived as scalar, making the conditional
  target CPTP; omission of a generic posterior denominator is justified here.
- The exact radical bound and the much smaller remaining device-error margin
  are matched between languages. Failure of the older loose bound is correctly
  distinguished from physical impossibility.
- Flag-only non-identifiability deliberately violates the independent small-beta
  premise and is not presented as a counterexample within that premise.
- Paper, finite computation, inherited Lean, synthetic data and absent device
  evidence remain separately described.

## Follow-up

Read back only the localized changes above before final acceptance. No full code
rerun is needed for these prose/notation fixes. PDF visual review is a separate
pending step until rendered pages are assigned.

## Actual narrow readback after the first revision

A actually reread the revised versions and checked the affected paragraphs in
both languages. The following findings are resolved: the finite-coordinate input
and positive projection premise; slot-count L; zero failure reference block and
zero-prefix contribution; at-most-two eigenvalues; the graph-domain norm estimate;
the specified self-adjoint simultaneous generator; the exact `B±iI` shifts;
original-source versus compiler success probabilities; and matched-blue versus
omitted-blue pulse costs. The nonzero-tail finite witness now also explicitly
states its separate input/output cutoffs, avoiding confusion with analytic N=4095.

The actual delimiter count is **nine display-math blocks in each language**,
with eighteen `$$` delimiter lines per file. This corrects any earlier informal
expectation of ten blocks. The nine displayed mathematical contents agree.

One sentence remains to make the output carrier completely explicit. In 68.3,
immediately after the finite-coordinate `rho_N` definition and before the original
flag construction, replace the current generic description of iota by:

- Chinese: “`iota_(N+2L)` 在每个 CQ 标签块上以 `J_(N+2L) tensor I_R` 共轭，
  嵌入共同物理 Fock 空间并保留标签。一般未截断输入的理想输出仍可能有无限尾；
  这里的共同有限载体计算限于投影输入或已知支持算例。”
- English: “On each CQ label block, `iota_(N+2L)` conjugates by
  `J_(N+2L) tensor I_R` into the common physical Fock space and preserves the label.
  The exact output of a general untruncated input can still have an infinite tail;
  the common finite-carrier calculations here concern projected inputs or
  known-support examples.”

All other scientific scope corrections have passed this readback. This is a
prose/typing clarification of the already correct displayed map into H_S; it
requires no change to the reviewed model or rerun of the numerical tests.

## Final prose readback

A subsequently read back the final iota paragraph in both languages. Both now
explicitly use conjugation by `J_(N+2L) tensor I_R` into the common physical Fock
space, retain the label, and distinguish a general untruncated ideal output's
possible infinite tail from finite-carrier calculations on supported inputs.
The last required clarification is therefore resolved.

**Final scientific/editorial verdict: PASS_SCOPED.** All seven requested groups
of corrections and the explicit carrier sentence have been read back. The two
languages each contain nine identical display-math blocks. No code was rerun
for this editorial review, and no new machine-proof or empirical status is
asserted. Rendered-page visual acceptance remains a separate task.
