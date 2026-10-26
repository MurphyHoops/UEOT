# R1: executable support-controller synthesis

This is the next mathematical increment after R0/PR #371. It removes the
noncomputable winning-action selection and PMF-support initialization from the
runtime interface. The finite relation checker and greatest-fixed-point theory
are reused; their implementation and earlier proofs remain unchanged.

The source base is `c54f1a96b25e57a3484da46d38c1c9f668d53a34`, with 694 modules
and 4,357 registered public source theorems. This increment adds
`ExecutableSupportController.lean` and `ExecutableSupportControllerWitness.lean`.
The complete 696-module source fingerprint is
`f95a19e8c0ad5f7295f8166d5a5fc212af5a8af40e2e2740673aaaf425b6e09d`.
Frozen 106/106, four counted generators and 11/89/6 are unchanged.

## 1. The computational input and actual returned object

Inputs are finite enumerations of $X,A$, computable $q:X\to Y$, decidable
equality on $X,Y,A$, decidable relation $R(x,a,z)$ and certificate $C(x,a)$,
an explicit initial finite set $I$, a finite ordered action list and a fallback
action. The ambient observation type $Y$ need not be finite.

The runtime returns `Option (Program X Y A)`. A `Program` contains exactly:

- `initialMemory : Y → Finset X`;
- `action : Finset X → A`;
- `update : Finset X → A → Y → Finset X`.

These functions are executable. `synthesize` checks that $I$ is nonempty, every
action appears in the list, and the existing `finiteMemoryCheck` accepts $I$.
Failure returns `none`; success returns the actual three-function program.
Duplicate list entries are allowed. No no-repeat or optimal-query-count claim
is made for a list containing duplicates.

The probability interpretation `Program.toController` uses `PMF.pure` and is
noncomputable. Actual execution uses the deterministic fields above and never
calls that probability interpretation or asks for the support of an arbitrary
PMF. This distinction is part of the API, not a claim that all Lean proofs avoid
classical logic.

## 2. The algorithm

Initialization and update are

$$
I_y=\{x\in I:q(x)=y\},\qquad
\operatorname{Next}(S,a,y)=
\{z:q(z)=y,\ \exists x\in S, R(x,a,z)\}.
$$

The update directly reuses `finiteRelationSuccessor`. Let
$B=2^{|X|}-1$. The Boolean action test is true exactly when

$$
S\ne\varnothing,\qquad
\forall x\in S, C(x,a),\qquad
\forall z\in X,
\operatorname{Next}(S,a,q(z))\ne\varnothing
\Rightarrow
\operatorname{Check}_B(\operatorname{Next}(S,a,q(z)))=\mathrm{true}.
$$

`List.find?` chooses the first successful action in the supplied list. If none
is found, including at empty memory, the program uses its fixed fallback.
Every nonempty observed successor has an element $z$, so its observation is
$q(z)$: finite enumeration of $X$ covers every relevant observation without an
enumeration of $Y$.

The code reuses the recursive finite checker. It terminates, but may repeatedly
solve the same subproblem and have exponential cost. It is not the separately
proposed memoized table algorithm and does not inherit that algorithm's
$M^2|A|$ action-check bound. The total memory type has $2^{|X|}$ values; no
global minimal-memory claim is made.

## 3. Why the computed action is valid

First, `relationCheck_iff_viableWith` proves the finite Boolean recursion's
pure relation semantics, without assuming a probability model exists. On the
nonempty single-observation arena, existing finite stabilization gives

$$
\operatorname{Check}_B(S)=\mathrm{true}
\iff S\in W_*,
$$

where $W_*$ is the already proved greatest winning support family.
`stepCheck_iff` therefore identifies the computed action test with certification
and preservation of $W_*$ for every nonempty successor. Existing
`supportWinning_step` provides existence of a qualifying action for $S\in W_*$;
list coverage guarantees that `find?` encounters one.

`findAction_eq_some_iff` characterizes the first successful list entry.
`selectedAction_step` proves the returned action itself is certified and keeps
all nonempty successors winning. Existence of a winning action is used only
in this proof; the program executes the list search and receives no unknown
winning selector as input.

## 4. The new program's own actual process

Let $p_0$ and $P_n(x,a,\cdot)$ be an actual controlled PMF source. The required
representation conditions are explicit:

$$
x\in I\iff x\in\operatorname{supp}(p_0),
$$

$$
z\in\operatorname{supp}(P_n(x,a))\iff R(x,a,z),\qquad
\operatorname{Certified}_n(x,a)\iff C(x,a).
$$

Transition probabilities may vary with $n$; their support and certification
must have the declared fixed representations. These equations are not inferred
from finite observations by the synthesizer.

`memory_eq_traceSupport` and `program_memory_eq_traceSupport` identify the new
program's replayed finite set with the existing original-source trace support,
for every complete record, including null records. Then
`supported_histories_winning` proves the winning invariant on the new
controller's own supported history law. Recorded positive-mass actions equal
the action actually computed by this program.

Applying the existing deployment-support characterization gives

$$
\forall n,\qquad
U_n=\Pr_{\rm this\ program}
  (\neg\operatorname{Certified}_n(X_n,A_n))=0.
$$

The public endpoint `synthesize_some_zero_uncovered` starts from the actual
equation `synthesize ... = some program`; it extracts list coverage, viability
and program identity from that computation. It does not identify the new
program with the earlier `Classical.choose` policy.

## 5. Physical safety and the numerical closure back to R0

For a physical safe set $K$, retain

$$
\operatorname{supp}(p_0)\subseteq K,
\qquad
x\in K\land C(x,a)\land R(x,a,z)\Rightarrow z\in K.
$$

`synthesize_some_all_times_physical_safe` consumes the computed program and
the source representation, derives its own zero occupancy, and invokes the
existing generic physical-safety theorem. It proves

$$
\Pr_{\rm actual\ returned\ program}(\forall n,X_n\in K)=1.
$$

For one fixed numerical `Model`, the same returned program has the actual
augmented kernel

$$
\bar P((x,m),(z,m'))=
P(x,a(m),z)\mathbf1\{m'=\operatorname{Next}(m,a(m),q(z))\}.
$$

Let $\bar Q$ be its killed matrix on $K\times\mathrm{Finset}(X)$ and
$\bar\eta$ its original unnormalized safe initial row. The new endpoint
`synthesize_some_killed_mass_one` connects the computed zero occupancy and
finite physical safety to R0's actual-source killed-mass identity:

$$
\forall n,\qquad \bar\eta\bar Q^n\mathbf1=1.
$$

Thus this finite synthesis slice supplies a positive, actually realized
survival conclusion. It retains initial safety and certified transition
closure rather than placing the final safety conclusion in an input record.
The general R0 identity, which also permits zero survival, remains unchanged.

## 6. One nonvacuous instance and actual execution

The witness extends the previous hidden Boolean flip with an absorbing failure
state. Let $X=\{\mathrm{some}(0),\mathrm{some}(1),\mathrm{none}\}$, with
constant observation and actions $0,1$. A matching action flips the safe phase;
any mismatched action goes to `none`, which is absorbing:

$$
f(\mathrm{some}(b),a)=
\begin{cases}\mathrm{some}(1-b),&a=b,\\\mathrm{none},&a\ne b,\end{cases}
\qquad f(\mathrm{none},a)=\mathrm{none}.
$$

The relation is $R(x,a,z)\iff z=f(x,a)$, certification is $x=\mathrm{some}(a)$,
initial support is $\{\mathrm{some}(0)\}$ and the proper nonempty safe set is
$K=\{\mathrm{some}(0),\mathrm{some}(1)\}$. The PMF source is exactly
$\delta_{f(x,a)}$, and the numerical model is proved to give that same PMF.

The witness proves actual synthesis success, executable phase updates, proper
physical safety for the returned program, and unit killed mass for this same
numerical model at every horizon. For the alternate initial law with both safe
phases present, synthesis rejects and no complete causal policy can have zero
uncertified occupancy at every time. This is a certification-policy no-go; it
is not presented as a separately proved minimal-memory or universal physical
safety impossibility theorem.

`EXECUTE_CONTROLLER.lean` actually runs the returned deterministic program for
12 transitions. Every step checks state membership, certification, exclusion
of failure and the exact next support. The observed actions are
`false,true,false,true,false,true,false,true,false,true,false,true`.
The run also checks rejection of ambiguous, incomplete and empty inputs, an
empty-memory fallback different from the first list action, and effective
forward/reverse order when both actions qualify.

Run from `formalization/ueot-core/`:

```bash
lake env lean --run docs/compression/theory_completion/unified_closure/executable_support_v1/EXECUTE_CONTROLLER.lean
```

These runtime assertions test the executable fields. The infinite-horizon
guarantees come from the Lean proofs and their explicit source premises.

## 7. Evidence and remaining boundary

`RELEASE_ACCEPTANCE.json` records actual local build/runtime/native/replay,
source identity, ownership, tests and review outcomes. The sealed protocol
adapter executes the unchanged predecessor drivers with explicit scope/schema
substitutions and a larger export recursion limit. The first native export
failed at Lean's default recursion depth; its actual error and frozen inputs
are retained in `actual-execution/failed-native-01/`. The production Lean
source did not change to resolve this audit-harness limit.
The next actual export found a closed-Boolean fallback regression definitionally
equal to two old Boolean equalities. That regression is now private, remains in
the full compiler census, and retains its independent runtime assertion. The
failed comparisons are preserved in `actual-execution/failed-native-02/`;
the public increment contains 33 theorems rather than counting that duplicate.
Full build, compiler ownership, displayed types, private proof
dependencies, transitive axioms, raw stored-type comparisons and fixed replay
remain real execution gates. A source freeze is only a pending input record.

Actual local results for the final source fingerprint above:

| Check | Actual outcome |
|---|---|
| Full `lake build UEOT` | Exit 0; 696 source modules; 9,402 jobs including cache; 79.232 seconds |
| Executable controller | Exit 0; all 12 steps and rejection/fallback/order assertions passed |
| Native export and fixed replay | Both exit 0; 480.086 / 475.909 seconds; complete JSON equal |
| New public type comparison | 33 source theorems; 143,781 prior-registry and 528 internal comparisons; zero collisions |
| Complete new-module census | 73 theorem constants, including 4 private and 36 other generated public constants; standard axioms only; 60 registered proof edges |
| Complete UMC census | 97 modules; 1,557 owned theorem constants; standard axioms only |
| Focused regressions | Reuse 62, parser 89, FKRG 30, 12 mission negative controls; actual 68-row clone rescan unchanged |
| Independent semantic reuse | 17 hinted groups / 37 pairs reviewed with actual compiler types and dependencies |

The immutable Git-object preflight, candidate-path ownership, exact-head review,
and resulting-main regression are separate publication gates, recorded at their
actual candidate/main identities rather than inferred from this worktree receipt.

Core cloud CI remains disabled by explicit user request; no cloud PASS is
claimed. All previous overlays, raw receipts, 106 P-IDs and counted generators
retain their original identities. Strong global mathematical closure remains
**NOT_ESTABLISHED**, and external scientific evidence remains **UNVERIFIED**.

The concrete next task is R2: exact support cannot be certified from merely
unseen transitions in finite samples. Use a proved support over-approximation,
an independently justified positive-mass gap or a quantitative risk budget,
and preserve three-valued uncertain oracle results. The present runtime
algorithm supplies neither an arbitrary-PMF support oracle nor that empirical
source certification.
