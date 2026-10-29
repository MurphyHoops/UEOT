import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveHistoryControl

/-!
Original commitment: complete open-loop responses determine the same source's adaptive observed futures.
Existing result: literal P/O/latent execution transports to response dynamics under the SAME full-history policy.
Premise reduced: derive a measurable adaptive future kernel and actual path equality from response equality.
Model: fixed registered initial controller memory h0, registered latent belief, same measurable history controller and allowed actions.
Consumer: actual finite/countable observed-history laws; different initial control memories are never identified by response alone.

The initial pair (b,h0) is registered together. The theorem samples the initial
latent once from b and retains h0 literally; it does not assert that an arbitrary
h0 was previously produced under b. Empty h0 represents a fresh program. A
nonempty h0 is also permitted, but comparing different control memories is not.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveAdaptiveCanonical
open MeasureTheory ProbabilityTheory
open UEOT.V3.DynamicsKernel
open MeasurablePredictiveResponseRecursion MeasurablePredictiveHistoryControl
open scoped ENNReal
noncomputable section

variable {Z A W : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace W]
local instance : MeasurableSpace (History A W) := historySpace A W

/-- The existing Ionescu--Tulcea trajectory kernel, seeded at the supplied state. -/
private def pathKernel {S : Type*} [MeasurableSpace S]
    (Q : Kernel S S) [IsMarkovKernel Q] : Kernel S (ℕ → S) :=
  letI : ∀ n, IsMarkovKernel (homHistoryKernel Q n) := fun n => isMarkovKernel_homHistoryKernel Q n
  (Kernel.traj (homHistoryKernel Q) 0).comap
    (fun s => fun _ : Finset.Iic 0 => s) (measurable_pi_lambda _ (fun _ => measurable_id))

private instance pathKernel_isMarkov {S : Type*} [MeasurableSpace S]
    (Q : Kernel S S) [IsMarkovKernel Q] : IsMarkovKernel (pathKernel Q) := by
  unfold pathKernel
  infer_instance

private theorem pathKernel_apply {S : Type*} [MeasurableSpace S]
    (Q : Kernel S S) [IsMarkovKernel Q] (s : S) :
    pathKernel Q s = homTrajMeasure (Measure.dirac s) Q := by
  let : ∀ n, IsMarkovKernel (homHistoryKernel Q n) := fun n => isMarkovKernel_homHistoryKernel Q n
  let η : Kernel ((i : Finset.Iic (0 : ℕ)) → S) (ℕ → S) := Kernel.traj (X:=fun _ : ℕ => S) (homHistoryKernel Q) 0
  change η (fun _ => s) = η ∘ₘ (Measure.dirac s).map
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => S)).symm
  rw [Measure.map_dirac' (by fun_prop)]
  exact (Measure.dirac_bind η.measurable _).symm

variable [StandardBorelSpace Z] [Nonempty Z] [StandardBorelSpace W]
variable [Countable A] [MeasurableSingletonClass A]
variable (P : Kernel (Z × A) Z) [IsMarkovKernel P]
variable (O : Kernel (Z × A) W) [IsMarkovKernel O]
variable (π : HistoryPolicy A W) [IsMarkovKernel π]

/-- Explicit measurable adaptive predictor on ALL ambient probability response
arrays. It preserves the supplied controller memory and invokes the SAME π. -/
def adaptiveFutureKernel (h0 : History A W) : Kernel (ResponseState A W) (ℕ → History A W) :=
  ((pathKernel (responseHistoryKernel P O π)).comap
    (fun c => (c,h0)) (measurable_id.prodMk measurable_const)).map
      (mapPath Prod.snd)

instance adaptiveFutureKernel_isMarkov (h0 : History A W) :
    IsMarkovKernel (adaptiveFutureKernel P O π h0) := by
  unfold adaptiveFutureKernel
  apply Kernel.IsMarkovKernel.map
  exact measurable_mapPath Prod.snd measurable_snd

/-- Literal physical experiment: sample the latent once from b, then advance it
through P/O while π observes only the retained action-observation history. -/
def actualAdaptiveLaw (b : ProbabilityMeasure Z) (h0 : History A W) : Measure (ℕ → History A W) :=
  (homTrajMeasure (historyLatentLift (b,h0)) (physicalHistoryKernel P O π)).map
    (mapPath (fun q => q.1.2))

instance actualAdaptiveLaw_isProbability (b : ProbabilityMeasure Z) (h0 : History A W) :
    IsProbabilityMeasure (actualAdaptiveLaw P O π b h0) :=
  Measure.isProbabilityMeasure_map (measurable_mapPath _ (by fun_prop)).aemeasurable

/-- Source-derived C1 adaptive sufficiency: the actual experiment's entire
observed-history law factors measurably through the complete word response.
The equality is valid for a fixed arbitrary registered h0, not only empty memory. -/
theorem actual_adaptive_factorization (b : ProbabilityMeasure Z) (h0 : History A W) :
    actualAdaptiveLaw P O π b h0 = adaptiveFutureKernel P O π h0 (response P O b) := by
  have h := congrArg (fun μ : Measure (ℕ → ResponseHistory A W) => μ.map (mapPath Prod.snd))
    (actual_physical_response_history_path P O π (b,h0))
  have hm : Measurable (fun q : BeliefHistory Z A W × Z => projectResponse P O q.1) :=
    (measurable_projectResponse P O).comp measurable_fst
  rw [Measure.map_map (measurable_mapPath Prod.snd measurable_snd) (measurable_mapPath _ hm)] at h
  change actualAdaptiveLaw P O π b h0 = _ at h
  rw [adaptiveFutureKernel,Kernel.map_apply _ (measurable_mapPath Prod.snd measurable_snd)]
  change _ = (pathKernel (responseHistoryKernel P O π) (response P O b,h0)).map (mapPath Prod.snd)
  rw [pathKernel_apply]
  exact h

/-- Actual complete adaptive histories agree whenever all finite open-loop
responses agree, for the SAME policy and SAME registered initial control memory. -/
theorem same_response_actual_history_path (b c : ProbabilityMeasure Z) (h0 : History A W)
    (hbc : response P O b = response P O c) :
    actualAdaptiveLaw P O π b h0 = actualAdaptiveLaw P O π c h0 := by
  rw [actual_adaptive_factorization,actual_adaptive_factorization,hbc]

/-- Every finite actual history prefix is preserved by that same response
comparison; no different-memory or independent-program equality is asserted. -/
theorem same_response_actual_finite_history (b c : ProbabilityMeasure Z) (h0 : History A W)
    (hbc : response P O b = response P O c) (n : ℕ) :
    (actualAdaptiveLaw P O π b h0).map (Preorder.frestrictLe n) =
      (actualAdaptiveLaw P O π c h0).map (Preorder.frestrictLe n) :=
  congrArg (fun μ : Measure (ℕ → History A W) => μ.map (Preorder.frestrictLe n))
    (same_response_actual_history_path P O π b c h0 hbc)

/-- Event-law form of the measurable factorization, on the actual full physical
experiment rather than a separately postulated predictive kernel. -/
theorem actual_adaptive_event (b : ProbabilityMeasure Z) (h0 : History A W)
    (E : Set (ℕ → History A W)) :
    actualAdaptiveLaw P O π b h0 E = adaptiveFutureKernel P O π h0 (response P O b) E := by
  rw [actual_adaptive_factorization]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveAdaptiveCanonical
