import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralCrossVariation

/-!
Original commitment: actual weighted QV needs original caller-grid cross variation with the actual approximating input g_m.
Existing result: exact same-input arbitrary partition QV, actual grid-uniform L1 input stability and native cross polarization.
Premise reduced: derive actual varying-input QV/cross variation from actual original input L2 convergence.
Model/witness: SAME original fullPredictableL2 T/sourceLaw, exact caller mono0/T clocks with computed mesh→0, no L4.
Consumer: actual left-weighted QV for g_m=sampledH*f; no varying-input or weighted-QV conclusion is supplied as a field.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVaryingInputQV
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianPredictableInputs BrownianIntegralGridL1 BrownianIntegralEnergyL1
open BrownianQuadraticVariation BrownianPartitionQV BrownianIntegralCrossVariation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Same actual caller clocks, actual varying original inputs. L2 input
convergence is consumed through the proved grid-uniform L1 bound. -/
theorem partition_QV_of_input_tendsto (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0))
    (g : ℕ → fullPredictableL2 T) (f : fullPredictableL2 T) (hg : Tendsto g atTop (𝓝 f)) :
    Tendsto (fun m => gridSquares T (τ m) (g m)) atTop (𝓝 (energyClass T T f)) := by
  have hB : Tendsto (fun m => ‖g m-f‖*(‖g m‖+‖f‖)) atTop (𝓝 0) := by
    have hd : Tendsto (fun m => ‖g m-f‖) atTop (𝓝 0) := by
      simpa only [sub_self,norm_zero] using (hg.sub (tendsto_const_nhds (x := f))).norm
    simpa only [zero_mul] using hd.mul (hg.norm.add (tendsto_const_nhds (x := ‖f‖)))
  have hE : Tendsto (fun m => gridSquares T (τ m) (g m)-gridSquares T (τ m) f) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun m => gridSquares_sub_norm_le T (τ m) (hmono m) (hzero m) (hend m) (g m) f) hB
  simpa only [sub_add_cancel,zero_add] using hE.add (fullInput_partition_QV T N τ hmono hzero hend hmesh f)

/-- Actual varying-input cross variation in original L1 scale; this feeds
sampled coefficient products without any new source/QV assumption. -/
theorem partition_crossVariation_of_input_tendsto (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0))
    (f : fullPredictableL2 T) (g : ℕ → fullPredictableL2 T) (h : fullPredictableL2 T)
    (hg : Tendsto g atTop (𝓝 h)) :
    Tendsto (fun m => gridCross T (τ m) f (g m)) atTop (𝓝 (crossEnergyClass T T f h)) := by
  simp_rw [gridCross_polarization,crossEnergyClass_polarization]
  exact ((partition_QV_of_input_tendsto T N τ hmono hzero hend hmesh (fun m => f+g m) (f+h)
    ((tendsto_const_nhds (x := f)).add hg)).sub
    (partition_QV_of_input_tendsto T N τ hmono hzero hend hmesh (fun m => f-g m) (f-h)
      ((tendsto_const_nhds (x := f)).sub hg))).const_smul (1/4 : ℝ)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVaryingInputQV
