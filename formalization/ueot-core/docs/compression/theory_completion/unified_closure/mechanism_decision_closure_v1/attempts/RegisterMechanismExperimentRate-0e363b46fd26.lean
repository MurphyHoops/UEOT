import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismTableLaw

/-!
# Real physical mode rates for the source experiment bounds

The actual planning consumer keeps its existing rational parameter interface.
Experimental distinguishability also applies to every real normal rate in
[0,1]. Its primitive is the SAME original real modeLaw and independent fair
birth label, with no resampling of the rate or mechanism during the episode.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentRate

open scoped BigOperators
open RegisterJointDecisionSource (Noise)
open RegisterMechanismDecisionSource
open RegisterFaultControlModel
open UEOT.V3.FiniteDiscountedControl

structure PhysicalExperiment where
  goal : Bool
  normal : ℝ
  normal_bounds : 0 ≤ normal ∧ normal ≤ 1

def ofParameters (P : Parameters) : PhysicalExperiment where
  goal := P.goal
  normal := P.normal
  normal_bounds := by exact_mod_cast P.normal_bounds

noncomputable def physicalHazard (P : PhysicalExperiment) : NNReal :=
  ⟨1-P.normal, sub_nonneg.mpr P.normal_bounds.2⟩

theorem physicalHazard_le_one (P : PhysicalExperiment) : physicalHazard P ≤ 1 := by
  change 1-P.normal ≤ 1
  linarith [P.normal_bounds.1]

/-- Original primitive, not a free sensor or a replacement transition kernel. -/
noncomputable def primitiveLaw (P : PhysicalExperiment) : PMF Noise :=
  (modeLaw (physicalHazard P) (physicalHazard_le_one P)).bind fun mode =>
    (PMF.uniformOfFintype Bool).map fun label => (mode,label)

private theorem labelMap_real (mode : Bool) (z : Noise) :
    (((PMF.uniformOfFintype Bool).map fun label => (mode,label)) z).toReal =
      if z.1 = mode then (1/2:ℝ) else 0 := by
  rcases z with ⟨b,l⟩
  cases mode <;> cases b <;> cases l <;>
    norm_num [PMF.map_apply,tsum_fintype,PMF.uniformOfFintype_apply]

/-- The two real mode weights times one fair label; all four primitive atoms
are retained even at the zero/one endpoints. -/
theorem primitiveLaw_real (P : PhysicalExperiment) (z : Noise) :
    (primitiveLaw P z).toReal = (if z.1 then P.normal else 1-P.normal) / 2 := by
  rw [primitiveLaw,PMF.bind_apply,tsum_fintype,
    ENNReal.toReal_sum (fun b _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ b) (PMF.apply_ne_top _ z))]
  simp only [ENNReal.toReal_mul,labelMap_real]
  rcases z with ⟨b,l⟩
  cases b <;>
    simp [modeLaw,FiniteProbabilityRow.ofRealRow_apply_toReal,modeProbability,
      repairChance,physicalHazard] <;> ring

/-- Exact bridge back to the frozen rational computational/native consumer. -/
theorem primitiveLaw_ofParameters (P : Parameters) :
    primitiveLaw (ofParameters P) = RegisterMechanismTableLaw.noiseLaw P := by
  apply PMF.ext
  intro z
  rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top (primitiveLaw (ofParameters P)) z),
    ← ENNReal.ofReal_toReal (PMF.apply_ne_top (RegisterMechanismTableLaw.noiseLaw P) z)]
  apply congrArg ENNReal.ofReal
  rw [primitiveLaw_real,RegisterMechanismTableLaw.noiseLaw_toReal P (initialWorld P.goal .S) z]
  rcases z with ⟨mode,label⟩
  cases mode <;> simp [ofParameters,source,RegisterJointDecisionSource.primitiveWeight]

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentRate
