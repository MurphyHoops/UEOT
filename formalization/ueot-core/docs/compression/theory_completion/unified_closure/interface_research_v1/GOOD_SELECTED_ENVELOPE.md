# Good 上受选事件包络：命题、证明与边界

以下数学论证摘自构建前独立审查；已发布 Core 的源代码未改。实际研究原型编译结果见同目录 README 与构建收据。

## 4. Exact Good-only envelope theorem

In `RegisteredDeploymentRisk.lean`, theorem
`RegisteredGoodJointCheck.registered_selected_joint_failure_of_cap_on_good`, the
current all-candidate envelope is used only once, inside the `intro ω hω` Good
branch that establishes conditional deployment risk. This makes the following
strict weakening valid without any new probability penalty:

```lean
(henvelope : ∀ ω,
  RegisteredCalibrationGood hN P certified T sample rho ω →
  E ⊆
    (riskHistoryMap (q (select ω))
      (fun ax : A × X => (ax.1, q (select ω) ax.2)) T) ⁻¹'
      F (select ω))
```

All other hypotheses, data and quantifiers can remain unchanged. In the existing
proof replace the single application `henvelope (select ω)` by
`henvelope ω hω`. Calibration still comes from the same registered sampling
experiment. The empirical fit, actual occupancy cap, envelope, and numerical
check now all concern the same selected candidate and same Good training record.
The joint is still constructed from that selection and its same causal policy.

The exact conclusion remains:

\[
J\{(\omega,h):h\in E\}\le
\min\{1,\alpha+(1-\alpha)\beta\},
\qquad\alpha=\texttt{registeredConfidenceBudget}.
\]

The proof is the already established decomposition, with no assumption inserted
for the desired conclusion:

1. On Good, calibration plus fit bounds the same-source reference discrepancy.
2. The Good-only selected envelope maps the fixed microscopic failure event into
   the selected reference event.
3. The same-policy occupancy cap and checked reference budget give risk ≤ β.
4. On Bad, any conditional failure event has probability at most 1.
5. Integrate over the actual constructed joint and use β∈[0,1].

The corresponding viable-policy endpoint keeps exactly
`viableFamilyPolicy initial q P certified T fallback`. Its Good-only initial
viability yields zero uncertified occupancy for that policy itself; it may call
the new envelope terminal with κ=0. This is an API extension/bridge, not a new
independent generator or new proof of scientific completeness. The published C files remain unchanged; the present implementation is an independently checked research prototype outside the production import graph.

## 5. When weakening is valid, and when it is not

### Strictness example

Take training Ω={g,b}, μ(g)=3/4 and μ(b)=1/4, selection s=id, deployment histories
H={0,1}, and fixed failure E={1}. Let K_g=δ₀ and K_b=δ₁. Use identity observation
and exact reference laws. Define F_g={1} and F_b=∅. Set G={g}.

The selected envelope holds on G and fails on b. On G the reference and actual
risk are both zero; β=0 and α=1/4 yield the sharp joint risk J(E)=1/4. Thus the
all-candidate envelope is strictly stronger than needed. This is an exact finite
joint example, not an assertion that the current registered calibration API has
already formalized this example.

### Deleting the envelope entirely is unsound

Take a one-record training law, G=Ω, actual and reference deployment δ₁, E={1},
F=∅, identity observation and zero model error. The reference check gives β=0,
and α=0; actual failure is 1. The only missing hypothesis is E⊆F. Hence the
package cannot omit its Good-selected envelope or substitute an unrelated event.

### A second high-probability event costs its own joint failure mass

If envelope validity is available only on a different H, use G∩H and prove an
upper bound on μ((G∩H)ᶜ). With μ(Gᶜ)≤α and μ(Hᶜ)≤δ one may use α+δ (or a tighter
actual union bound) once in the final mixture. Reusing α without charging H can
be false: let G=Ω, H={g}, the strictness construction above, and α=0. It would
claim risk 0 despite actual risk 1/4. Independence of G and H is not required for
the union bound and should not be invented.

### Almost-everywhere versus every Good record

Mathematically it is sufficient for the Good-selected envelope and all conditional
checks to hold μ-almost everywhere on G. In the current finite setting this means
only Good records with positive training mass need the premise. To formalize that
extra weakening, either prove a support-restricted version of the finite joint
sum theorem or replace G by G∩support(μ) and prove zero mass is removed. Do not
silently delete zero-probability hypotheses in the current API.

Likewise setwise envelope inclusion can be weakened to K_{s(ω)}-almost-sure
inclusion on Good, because K(E\map⁻¹F)=0 suffices. That requires a new
measure-monotonicity/null-set bridge at the conditional risk layer; the existing
set-inclusion theorem alone does not directly expose it.

### Data-dependent events require clear event identity

The base `selectedTrainingDeployment_failure_le` already supports E:Ω→Set H.
Therefore record-dependent microscopic events can be bounded, but the resulting
joint event must be written `{(ω,h) | h∈E(ω)}`. One cannot call this a bound on a
different fixed physical failure event without an additional containment proof.
Record-dependent reference envelopes are also mathematically legitimate if the
same ω is used by envelope, reference budget and selected deployment. Data
dependence itself is not the obstruction; mismatching those identities is.

### β and experiment identity remain material

β≤1 is used when replacing true bad mass by α, because the coefficient 1−β must
be nonnegative. Do not remove its interval bound while keeping the same formula.
The current nonnegative β bound is also part of the stated API. The proof does
not assume independence between training data and deployed paths: their joint
mass is constructed as μ(ω)K_{s(ω)}(h). A cap or risk certificate for another
policy cannot replace the actual selected policy's cap.

## 6. Scope of this result

The identified Good-only endpoint has an explicit proof adaptation and strictness
examples. It has not yet been added to the production Lean API. The subsequent prototype compilation is recorded separately. The current books' API-scope warning therefore remains
accurate until an actual subsequent source change passes its proof and integration
gates. No claim about physical survival, infinite-horizon survival, consciousness,
ethics or empirical unification follows from this interface extension.

## 7. Improved implementation draft: reuse by event completion

After the proof-route review, an additive draft was prepared at
`GoodSelectedEnvelope.lean` in this directory. It began as an uncompiled draft; subsequent exact-source compilation and axiom checks are recorded in the build evidence.

The preferred implementation avoids repeating either probabilistic proof. Set

\[
\widetilde F(c)=
\begin{cases}
F(c),&\exists\omega\in G:\operatorname{select}(\omega)=c,\\
\text{all reference histories},&\text{otherwise}.
\end{cases}
\]

Two elementary set-theoretic bridges show (a) this completed family has an
envelope for every candidate, and (b) it equals F for every Good-selected
candidate. Apply the already published registered-risk terminal to this family
and simplify its Good-only checked budget by (b). Do the same with the already
published viable-family terminal; its internal same-policy zero-occupancy proof
remains entirely reused. No deployment law, policy, initial distribution,
calibration event or final budget is changed. No conclusion is hidden in the
completion's hypotheses. Bad candidates receive a vacuous reference event, but
no bad-record reference budget was needed by the existing theorem.

This gives two new endpoints and two reusable set-theoretic helper theorems in
one additive module. The prototype has been compiled and axiom-checked. It has not been added to the public root or registered in the production source DAG. The production interface remains unchanged.
