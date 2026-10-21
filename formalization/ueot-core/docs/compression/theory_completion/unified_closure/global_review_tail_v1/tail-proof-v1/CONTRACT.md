# Same-source survival tail — contract v1

Status at contract creation: mathematical/API route checked; this new endpoint has not yet been compiled. Subsequent execution and independent review will be recorded separately. This task owns only this private directory and does not edit the frozen Stage1–7 packages or production imports.

## One endpoint and its exact source

Fix the same data used by the passed `SameSourceSafePrefix` adapter:

- `X Y A : Type u`, `[Fintype X]`, `[Fintype A]`, `[Nonempty A]`;
- measurable structures and measurable singleton classes on `X` and `A`;
- the actual controlled model `M : Model X (fun _ => A)`;
- the actual observation map `q : X → Y` and time-homogeneous current-observation randomized policy `sigma : Y → PMF A`;
- any actual original initial law `p0 : PMF X` and any safe set `K : Set X`.

There is no finiteness or measurability assumption on `Y`. The same `M`, `q`, `sigma`, and `p0` occur on both sides. In the following explanatory notation,

\[
\pi=\operatorname{liftedStationaryPolicy}(q,\sigma),\quad
Q=\operatorname{killedMatrix}(M,\pi,K),\quad
\eta_0(v)=p_0(v).\operatorname{toReal},\ v:K,
\]

\[
R=\operatorname{pmfRowKernel}(\operatorname{policyTransitionPMF}(M,\pi)),\qquad
\mu_\infty=\operatorname{homTrajMeasure}(p_0.\operatorname{toMeasure},R),
\]

\[
s_n=\sum_{v:K}(\eta_0Q^n)(v),\qquad
S_n=\operatorname{survivalSet}(K^c,n),\qquad
S_\infty=\operatorname{neverHitSet}(K^c).
\]

The sole new public endpoint is

\[
\boxed{\displaystyle s_n\longrightarrow\mu_\infty.\operatorname{real}(S_\infty)}.
\]

Planned Lean name: `SameSourceSurvivalTailCheck.killed_survival_mass_tendsto_homogeneous_neverHit_real`. Its full mathematical statement is:

```lean
theorem killed_survival_mass_tendsto_homogeneous_neverHit_real
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
    (p0 : PMF X) (K : Set X) :
    Tendsto
      (fun n : ℕ => ∑ v : K, rowApply (safeInitialRow p0 K)
        ((killedMatrix M (liftedStationaryPolicy q sigma) K) ^ n) v)
      atTop
      (nhds ((homTrajMeasure p0.toMeasure
        (pmfRowKernel
          (policyTransitionPMF M (liftedStationaryPolicy q sigma)))).real
            (neverHitSet Kᶜ)))
```

No event identity, source equality, convergence statement, nonnegativity, or probability-finiteness premise is supplied as a hypothesis. The previously passed finite-source identity is reused as a proved theorem.

## Proof route, with actual API signatures

1. `DynamicsKernel.isProbabilityMeasure_homTrajMeasure` gives `IsProbabilityMeasure mu` from the actual PMF initial measure and the already proved `pmfRowKernel_isMarkov` instance. No initial-law replacement is made.
2. `hKc : MeasurableSet Kᶜ` follows from finite `X` and measurable singletons: `(Set.toFinite Kᶜ).measurableSet`. For each `n`, `RecoveryHittingNonnegative.measurableSet_survivalSet hKc n` gives a measurable, hence `mu`-null-measurable, event.
3. Reuse `Objecthood.antitone_survivalSet Kᶜ`. Apply Mathlib's exact endpoint

   ```lean
   tendsto_measure_iInter_atTop
     (hs : ∀ i, NullMeasurableSet (s i) μ)
     (hm : Antitone s) (hf : ∃ i, μ (s i) ≠ ∞) :
     Tendsto (μ ∘ s) atTop (𝓝 (μ (⋂ n, s n)))
   ```

   with `mu`, `survivalSet Kᶜ`, and `hf := ⟨0, measure_ne_top _ _⟩`.
4. Rewrite the intersection using the proved `Objecthood.neverHitSet_eq_iInter_survivalSet Kᶜ`. This yields the ENNReal event-mass limit internally; no extra public wrapper is needed.
5. Compose `ENNReal.tendsto_toReal (measure_ne_top _ _)`, whose only requirement is that the limiting measure is not infinite. All such event masses are finite because `mu` is a probability measure.
6. Rewrite the real sequence pointwise using the passed S3 endpoint `SameSourceSafePrefixCheck.homogeneous_survival_real_eq_killed_pow_sum M q sigma p0 K n`. This gives exactly the stated killed-matrix sequence and the real mass of the same infinite event.

The current production `Objecthood.survivalProb_tendsto_neverHitProb` already uses steps 2–4 for Dirac initial laws. This new result reuses the generic continuity theorem directly on the original `p0` and uses S3 to supply the actual source-facing finite quantity. It neither reconstructs the infinite measure nor performs a Dirac/finite-mixture detour. Using S3 rather than reversing `ofReal` also avoids adding a redundant nonnegativity proof.

## Boundaries retained

- `S_n` includes every time from `0` through `n`. Thus `s_0 = p0(K)`, not necessarily `1`; initial failure mass remains excluded from every safety event.
- `K = ∅` is permitted. Both the finite safe-mass sequence and infinite safe-event mass are zero. No `Nonempty K` premise is added.
- No `s_n > 0` premise is added. The theorem remains valid if survival is zero at some or all finite times; there is no conditional distribution or normalization here.
- Positive survival at every finite time does not imply positive infinite survival. For a safe state with one-step survival probability `1/2`, `s_n = (1/2)^n` tends to zero.
- The observation policy is the actual fixed current-observation randomized `sigma`. The result does not identify arbitrary causal policies or `viableFamilyPolicy` with it.
- No QSD/Perron data, irreducibility, support-closed class, Doob transform, maximal fixed point, positive-survival characterization, or new all-times viable-policy existence theorem is included.

## Input and execution discipline

`API_INPUTS.json` binds the actual finite-source theorem, its archived identical source, the four private source/olean pairs (safe-prefix plus its three private dependencies), the prior independent CLEAR, the production event/trajectory endpoints, and the Mathlib continuity/toReal APIs. The whole production source tree, toolchain/manifest files, runtime binaries, and import-environment defaults are rechecked against the completed Linux build before cache reuse.

Execution uses one focused Lean process, the absolute Lean 4.33.1/Lake runtime, `LEAN_NUM_THREADS=1`, separate attempt snapshots/logs/output, and a 180-second limit per attempt. No `lake build`, native export, production mutation, book edit, Git or remote operation is part of this task. Original contract/draft and any failed execution remain unchanged; later PASS and independent review are separate records. A focused PASS is not production integration.
