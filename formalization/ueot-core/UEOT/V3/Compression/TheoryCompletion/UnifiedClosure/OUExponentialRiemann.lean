import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianScalarTaylorRemainder

/-!
Original commitment: the physical Volterra path must equal the actual Brownian exponential integral, not merely share a marginal law.
Existing result: original literal uniform-clock left tables converge in source L2; the physical centered-B state satisfies its actual restoring equation.
Premise reduced: prove deterministic exponential integration by parts along the actual caller partitions, by FTC and continuous-path compact uniform continuity.
Model/witness: any continuous real path, finite nondecreasing clock from0 toT with computed mesh → 0; k ≥ 0 including k0/T0 and repeatedcells.
Consumer/boundary: SAME pathwise left sums identify physical Volterra with actual native Gaussian integral; conditional noise/kernel still requires a separate source proof.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUExponentialRiemann
open MeasureTheory Set Filter
open BrownianQuadraticVariation BrownianScalarTaylorRemainder
open scoped NNReal Topology
noncomputable section

private theorem sum_differences {n : ℕ} (F : Fin (n+1) → ℝ) :
    (∑ i : Fin n, (F i.succ - F i.castSucc))=F (Fin.last n)-F 0 := by
  rw [Finset.sum_sub_distrib]
  have h0 := Fin.sum_univ_succ F
  have hN := Fin.sum_univ_castSucc F
  linarith

private theorem exp_deriv (k s : ℝ) : HasDerivAt (fun u : ℝ =>  Real.exp (k*u)) (k*Real.exp (k*s)) s := by
  simpa only [id_eq,mul_one,one_mul,mul_comm] using (((hasDerivAt_id s).const_mul k).exp)

private theorem exp_integral (k a b : ℝ) :
    (∫ s in a..b,k*Real.exp (k*s))=Real.exp (k*b)-Real.exp (k*a) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ =>  exp_deriv k s)
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable a b)

/-- Pure finite telescoping, retaining the actual left endpoint in the Brownian-style sum. -/
theorem finite_product_telescope {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (k : ℝ) (b : ℝ → ℝ) :
    (∑ i : Fin n,Real.exp (k*τ i.castSucc)*(b (τ i.succ)-b (τ i.castSucc)))+
      (∑ i : Fin n,b (τ i.succ)*(Real.exp (k*τ i.succ)-Real.exp (k*τ i.castSucc)))=
      Real.exp (k*τ (Fin.last n))*b (τ (Fin.last n))-Real.exp (k*τ 0)*b (τ 0) := by
  rw [←Finset.sum_add_distrib,←sum_differences (fun i =>  Real.exp (k*τ i)*b (τ i))]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem integral_telescope {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (f : ℝ → ℝ) (hf : Continuous f) :
    (∑ i : Fin n,∫ s in (τ i.castSucc : ℝ)..(τ i.succ : ℝ),f s)=
      ∫ s in (τ 0 : ℝ)..(τ (Fin.last n) : ℝ),f s := by
  have hi (i : Fin n) : (∫ s in (τ i.castSucc : ℝ)..(τ i.succ : ℝ),f s)=
      (∫ s in 0..(τ i.succ : ℝ),f s)-(∫ s in 0..(τ i.castSucc : ℝ),f s) := by
    exact (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm
  simp_rw [hi]
  rw [sum_differences (fun i => ∫ s in (0 : ℝ)..(τ i : ℝ),f s)]
  exact intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

/-- The weighted right sum is exactly a sum of ordinary cell errors. -/
theorem right_error_identity {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (k : ℝ) (b : ℝ → ℝ) (hb : Continuous b) :
    (∑ i : Fin n,b (τ i.succ)*(Real.exp (k*τ i.succ)-Real.exp (k*τ i.castSucc)))-
      (∫ s in (τ 0 : ℝ)..(τ (Fin.last n) : ℝ),k*Real.exp (k*s)*b s)=
      ∑ i : Fin n,∫ s in (τ i.castSucc : ℝ)..(τ i.succ : ℝ),
        k*Real.exp (k*s)*(b (τ i.succ)-b s) := by
  have hc : Continuous (fun s : ℝ => k*Real.exp (k*s)*b s) := by fun_prop
  rw [←integral_telescope τ _ hc,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (fun s =>  k*Real.exp (k*s)*(b (τ i.succ)-b s))=
      (fun s =>  b (τ i.succ)*(k*Real.exp (k*s))-k*Real.exp (k*s)*b s) from by funext s; ring]
  have hc1 : Continuous (fun s : ℝ => b (τ i.succ)*(k*Real.exp (k*s))) := by fun_prop
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,exp_integral]

/-- Compact path uniform continuity controls every interior point of every actual small-mesh cell. -/
theorem cell_modulus_eventually (T : ℝ≥0) (N : ℕ → ℕ) (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0)
    (hmono : ∀ m, Monotone (τ m)) (hT : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m =>  (mesh (τ m) : ℝ)) atTop (𝓝 0))
    (b : ℝ → ℝ) (hb : Continuous b) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m in atTop,∀ i : Fin (N m),∀ s ∈Icc (τ m i.castSucc : ℝ) (τ m i.succ : ℝ),
      ‖b (τ m i.succ)-b s‖ < ε := by
  have huc : UniformContinuousOn b (Icc (0 : ℝ) T) := isCompact_Icc.uniformContinuousOn_of_continuous hb.continuousOn
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  filter_upwards [hmesh.eventually (gt_mem_nhds hδ)] with m hm
  intro i s hs
  have hend : (τ m i.succ : ℝ) ≤ T := by exact_mod_cast (hmono m (Fin.le_last _)).trans_eq (hT m)
  have ha : 0 ≤ (τ m i.castSucc : ℝ) := (τ m i.castSucc).coe_nonneg
  have hgap := clockIncrement_dist_le_mesh (τ m) (hmono m) i
  rw [NNReal.dist_eq,abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmono m (show i.castSucc ≤ i.succ by exact_mod_cast Nat.le_succ (i : ℕ))))] at hgap
  have hdist : dist (τ m i.succ : ℝ) s < δ := by
    rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hs.2)]
    linarith [hs.1]
  simpa only [Real.dist_eq, ←Real.norm_eq_abs] using hd _ ⟨(τ m i.succ).coe_nonneg,hend⟩ _ ⟨ha.trans hs.1,hs.2.trans hend⟩ hdist

/-- Exact left exponential-increment sums converge to the physical integration-by-parts functional. -/
theorem left_sums_tendsto (T : ℝ≥0) (N : ℕ → ℕ) (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0)
    (hmono : ∀ m, Monotone (τ m)) (h0 : ∀ m, τ m 0=0) (hT : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m =>  (mesh (τ m) : ℝ)) atTop (𝓝 0))
    (k : ℝ) (hk : 0 ≤ k) (b : ℝ → ℝ) (hb : Continuous b) :
    Tendsto (fun m =>  ∑ i : Fin (N m),Real.exp (k*τ m i.castSucc)*(b (τ m i.succ)-b (τ m i.castSucc)))
      atTop (𝓝 (Real.exp (k*T)*b T-b 0-k*(∫ s in 0..(T : ℝ),Real.exp (k*s)*b s))) := by
  let R (m : ℕ) := ∑ i : Fin (N m),b (τ m i.succ)*(Real.exp (k*τ m i.succ)-Real.exp (k*τ m i.castSucc))
  let V := ∫ s in 0..(T : ℝ),k*Real.exp (k*s)*b s
  have hv : V=k*(∫ s in 0..(T : ℝ),Real.exp (k*s)*b s) := by
    dsimp [V]
    simp_rw [mul_assoc]
    exact intervalIntegral.integral_const_mul _ _
  have hr : Tendsto R atTop (𝓝 V) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let C := k*Real.exp (k*T)
    have hC : 0 ≤ C := mul_nonneg hk (Real.exp_pos _).le
    let η := ε/(C*(T : ℝ)+1)
    have hη : 0 < η := div_pos hε (by positivity)
    filter_upwards [cell_modulus_eventually T N τ hmono hT hmesh b hb η hη] with m hm
    have he := right_error_identity (τ m) k b hb
    rw [h0,hT,NNReal.coe_zero] at he
    rw [Real.dist_eq,←Real.norm_eq_abs]
    change ‖R m-V‖ < ε
    rw [show R m-V=∑ i : Fin (N m),∫ s in (τ m i.castSucc : ℝ)..(τ m i.succ : ℝ),k*Real.exp (k*s)*(b (τ m i.succ)-b s) from he]
    calc
      _  ≤  ∑ i : Fin (N m),‖∫ s in (τ m i.castSucc : ℝ)..(τ m i.succ : ℝ),k*Real.exp (k*s)*(b (τ m i.succ)-b s)‖ := norm_sum_le _ _
      _  ≤  ∑ i : Fin (N m),(C*η)*((τ m i.succ : ℝ)-(τ m i.castSucc : ℝ)) := by
        apply Finset.sum_le_sum
        intro i _
        have ho : (τ m i.castSucc : ℝ) ≤ (τ m i.succ : ℝ) := by exact_mod_cast hmono m (show i.castSucc ≤ i.succ by exact_mod_cast Nat.le_succ (i : ℕ))
        have hbound : ∀ s ∈uIoc (τ m i.castSucc : ℝ) (τ m i.succ : ℝ),‖k*Real.exp (k*s)*(b (τ m i.succ)-b s)‖ ≤ C*η := by
          intro s hs
          rw [uIoc_of_le ho] at hs
          have hsT : s ≤ T := hs.2.trans (by exact_mod_cast (hmono m (Fin.le_last _)).trans_eq (hT m))
          have hg : ‖k*Real.exp (k*s)‖ ≤ C := by
            rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hk (Real.exp_pos _).le)]
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT hk)) hk
          rw [norm_mul]
          exact mul_le_mul hg (hm i s ⟨hs.1.le,hs.2⟩).le (norm_nonneg _) hC
        simpa only [abs_of_nonneg (sub_nonneg.mpr ho)] using intervalIntegral.norm_integral_le_of_norm_le_const hbound
      _ = C*η*(T : ℝ) := by
        rw [←Finset.mul_sum,sum_differences (fun i =>  (τ m i : ℝ)),h0,hT,NNReal.coe_zero,sub_zero]
      _  <  ε := by
        dsimp [η]
        have hd : 0 < C*(T : ℝ)+1 := by positivity
        calc
          C*(ε/(C*(T : ℝ)+1))*(T : ℝ) = (ε*(C*(T : ℝ)))/(C*(T : ℝ)+1) := by ring
          _ < ε := (div_lt_iff₀ hd).mpr (by nlinarith)
  have hp : Tendsto (fun m => Real.exp (k*T)*b T-b 0-R m) atTop (𝓝 (Real.exp (k*T)*b T-b 0-V)) := tendsto_const_nhds.sub hr
  have he (m : ℕ) : (∑ i : Fin (N m),Real.exp (k*τ m i.castSucc)*(b (τ m i.succ)-b (τ m i.castSucc)))=
      Real.exp (k*T)*b T-b 0-R m := by
    have h:=finite_product_telescope (τ m) k b
    rw[h0,hT,NNReal.coe_zero,mul_zero,Real.exp_zero,one_mul] at h
    dsimp[R]
    linarith
  rw [←hv]
  exact (tendsto_congr' (Eventually.of_forall he)).mpr hp

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUExponentialRiemann
