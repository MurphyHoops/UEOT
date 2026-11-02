import UEOT
import «ueot-compact-killed-bool-common-consumer»
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal
noncomputable section
namespace CompactKilledBoolOperatorBinding
local instance : MeasurableSpace Bool := ⊤

/-- The same registered killed transition table realizes the WHOLE L²
operator, not merely the chosen initial density's orbit. -/
theorem same_actual_operator (t:NNReal) (v : Lp ℝ 2 CompactKilledBoolAuthor.m) (y:Bool) :
    CompactKilledBoolAuthor.S t v y =
      CompactKilledBoolKernel.k t false y * v false+
      CompactKilledBoolKernel.k t true y * v true := by
  rw [CompactKilledBoolAuthor.S_apply]
  have ha := CompactKilledBoolAuthor.ae_iff.mp (Lp.coeFn_add
    (Real.exp (-(t:ℝ)) • (inner ℝ CompactKilledBoolAuthor.phi v • CompactKilledBoolAuthor.phi))
    (Real.exp (-2*(t:ℝ)) • (inner ℝ CompactKilledBoolAuthor.psi v • CompactKilledBoolAuthor.psi))) y
  have hp := CompactKilledBoolAuthor.ae_iff.mp (Lp.coeFn_smul (Real.exp (-(t:ℝ)))
    (inner ℝ CompactKilledBoolAuthor.phi v • CompactKilledBoolAuthor.phi)) y
  have hq := CompactKilledBoolAuthor.ae_iff.mp (Lp.coeFn_smul (Real.exp (-2*(t:ℝ)))
    (inner ℝ CompactKilledBoolAuthor.psi v • CompactKilledBoolAuthor.psi)) y
  have hphi := CompactKilledBoolAuthor.ae_iff.mp (Lp.coeFn_smul
    (inner ℝ CompactKilledBoolAuthor.phi v) CompactKilledBoolAuthor.phi) y
  have hpsi := CompactKilledBoolAuthor.ae_iff.mp (Lp.coeFn_smul
    (inner ℝ CompactKilledBoolAuthor.psi v) CompactKilledBoolAuthor.psi) y
  rw [ha]
  simp only [Pi.add_apply,hp,hq,Pi.smul_apply,hphi,hpsi,smul_eq_mul]
  cases y <;> simp [CompactKilledBoolAuthor.inner_formula,CompactKilledBoolAuthor.phi_apply,
    CompactKilledBoolAuthor.psi_apply,CompactKilledBoolKernel.k,CompactKilledBoolKernel.e,
    CompactKilledBoolKernel.f] <;> ring


/-- On every nonnegative L² density, this operator realizes the actual
kernel action on measures, not only a scalar trajectory chosen afterwards. -/
theorem same_actual_kernel_action (t:NNReal) (v : Lp ℝ 2 CompactKilledBoolAuthor.m)
    (hvn : 0 ≤ᵐ[CompactKilledBoolAuthor.m] (v : Bool→ℝ)) :
    CompactKilledBoolKernel.kernel t ∘ₘ
        (CompactKilledBoolKernel.m.withDensity (fun x => ENNReal.ofReal (v x))) =
      CompactKilledBoolKernel.m.withDensity
        (fun x => ENNReal.ofReal (CompactKilledBoolAuthor.S t v x)) := by
  have hv := CompactKilledBoolAuthor.ae_iff.mp hvn
  apply Measure.ext_of_singleton
  intro y
  rw [Measure.bind_apply (measurableSet_singleton y) (Kernel.aemeasurable _),lintegral_fintype]
  simp only [Fintype.sum_bool,CompactKilledBoolKernel.kernel_singleton,
    withDensity_apply _ (measurableSet_singleton _),lintegral_singleton,
    CompactKilledBoolKernel.m_singleton]
  rw [same_actual_operator]
  have h0 := CompactKilledBoolKernel.k_nonneg t false y
  have h1 := CompactKilledBoolKernel.k_nonneg t true y
  rw [ENNReal.ofReal_add (mul_nonneg h0 (hv false)) (mul_nonneg h1 (hv true)),
    ENNReal.ofReal_mul h0,ENNReal.ofReal_mul h1]
  ring

#print axioms same_actual_operator
#print axioms same_actual_kernel_action
end CompactKilledBoolOperatorBinding
