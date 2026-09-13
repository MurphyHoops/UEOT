import UEOT.V3.InformationDiscreteEntropy
import UEOT.V3.InformationKernelKL
import UEOT.V3.InformationStatistic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule

/-!
# P-EVO-02 — irrelevant copied labels inflate hereditary information

The frozen Core 3 statement assumes a finite label `T` independent of the
joint parent/offspring pair `(F,F')`, and then copies that same label without
error.  We encode those assumptions structurally: `ρ.prod (copyJoint τ)` is the
independent product of the true `(F,F')` law with a diagonal `(T,T)` copy law,
and `sharedRepack` only regroups coordinates into `((F,T),(F',T))`.
-/

namespace UEOT.V3.EvolutionSharedLabel

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationEntropyBound
open UEOT.V3.InformationDiscreteEntropy
open UEOT.V3.InformationStatistic
open UEOT.V3.InformationCore

universe uF uG uT

variable {F : Type uF} {G : Type uG} {T : Type uT}
variable [MeasurableSpace F] [MeasurableSpace G] [MeasurableSpace T]
variable [Fintype F] [Fintype G] [Fintype T]
variable [MeasurableSingletonClass F] [MeasurableSingletonClass G]
variable [MeasurableSingletonClass T]
variable [Nonempty F] [Nonempty G] [Nonempty T]

def sharedRepack : ((F × G) × (T × T)) → ((F × T) × (G × T)) :=
  fun z => ((z.1.1, z.2.1), (z.1.2, z.2.2))

def sharedUnpack : ((F × T) × (G × T)) → ((F × G) × (T × T)) :=
  fun z => ((z.1.1, z.2.1), (z.1.2, z.2.2))

lemma sharedUnpack_leftInverse :
    Function.LeftInverse
      (sharedUnpack (F := F) (G := G) (T := T))
      (sharedRepack (F := F) (G := G) (T := T)) := by
  rintro ⟨⟨f, g⟩, ⟨t, s⟩⟩
  rfl

lemma measurable_sharedRepack :
    Measurable (sharedRepack (F := F) (G := G) (T := T)) :=
  measurable_of_countable _

lemma measurable_sharedUnpack :
    Measurable (sharedUnpack (F := F) (G := G) (T := T)) :=
  measurable_of_countable _

noncomputable def sharedLabelJoint
    (ρ : Measure (F × G)) (τ : Measure T) :
    Measure ((F × T) × (G × T)) :=
  (ρ.prod (copyJoint τ)).map (sharedRepack (F := F) (G := G) (T := T))

private theorem copyJoint_fst_eq
    (τ : Measure T) [IsProbabilityMeasure τ] :
    (copyJoint τ).fst = τ := by
  unfold copyJoint Measure.fst
  rw [Measure.map_map measurable_fst (measurable_of_countable _)]
  change τ.map (fun t : T => t) = τ
  exact Measure.map_id'

private theorem copyJoint_snd_eq
    (τ : Measure T) [IsProbabilityMeasure τ] :
    (copyJoint τ).snd = τ := by
  unfold copyJoint Measure.snd
  rw [Measure.map_map measurable_snd (measurable_of_countable _)]
  change τ.map (fun t : T => t) = τ
  exact Measure.map_id'

private instance copyJoint_isProbability_evo
    (τ : Measure T) [IsProbabilityMeasure τ] :
    IsProbabilityMeasure (copyJoint τ) := by
  unfold copyJoint
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

instance sharedLabelJoint_isProbability
    (ρ : Measure (F × G)) [IsProbabilityMeasure ρ]
    (τ : Measure T) [IsProbabilityMeasure τ] :
    IsProbabilityMeasure (sharedLabelJoint ρ τ) := by
  unfold sharedLabelJoint
  exact Measure.isProbabilityMeasure_map measurable_sharedRepack.aemeasurable

private theorem sharedLabelJoint_fst
    (ρ : Measure (F × G)) [IsProbabilityMeasure ρ]
    (τ : Measure T) [IsProbabilityMeasure τ] :
    (sharedLabelJoint ρ τ).fst = ρ.fst.prod τ := by
  unfold sharedLabelJoint Measure.fst
  rw [Measure.map_map measurable_fst measurable_sharedRepack]
  change
    (ρ.prod (copyJoint τ)).map (Prod.map Prod.fst Prod.fst) =
      ρ.fst.prod τ
  calc
    (ρ.prod (copyJoint τ)).map (Prod.map Prod.fst Prod.fst) =
        (ρ.map Prod.fst).prod ((copyJoint τ).map Prod.fst) := by
      symm
      exact Measure.map_prod_map ρ (copyJoint τ) measurable_fst measurable_fst
    _ = ρ.fst.prod τ := by
      change ρ.fst.prod (copyJoint τ).fst = ρ.fst.prod τ
      rw [copyJoint_fst_eq τ]

private theorem sharedLabelJoint_snd
    (ρ : Measure (F × G)) [IsProbabilityMeasure ρ]
    (τ : Measure T) [IsProbabilityMeasure τ] :
    (sharedLabelJoint ρ τ).snd = ρ.snd.prod τ := by
  unfold sharedLabelJoint Measure.snd
  rw [Measure.map_map measurable_snd measurable_sharedRepack]
  change
    (ρ.prod (copyJoint τ)).map (Prod.map Prod.snd Prod.snd) =
      ρ.snd.prod τ
  calc
    (ρ.prod (copyJoint τ)).map (Prod.map Prod.snd Prod.snd) =
        (ρ.map Prod.snd).prod ((copyJoint τ).map Prod.snd) := by
      symm
      exact Measure.map_prod_map ρ (copyJoint τ) measurable_snd measurable_snd
    _ = ρ.snd.prod τ := by
      change ρ.snd.prod (copyJoint τ).snd = ρ.snd.prod τ
      rw [copyJoint_snd_eq τ]

private theorem prod_singleton
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (a : A) (b : B) :
    (μ.prod ν) ({(a, b)} : Set (A × B)) = μ {a} * ν {b} := by
  rw [show ({(a, b)} : Set (A × B)) = ({a} : Set A) ×ˢ ({b} : Set B) by
    ext z
    simp]
  exact Measure.prod_prod _ _

private theorem sharedLabelJoint_reference
    (ρ : Measure (F × G)) [IsProbabilityMeasure ρ]
    (τ : Measure T) [IsProbabilityMeasure τ] :
    (sharedLabelJoint ρ τ).fst.prod (sharedLabelJoint ρ τ).snd =
      ((ρ.fst.prod ρ.snd).prod (τ.prod τ)).map
        (sharedRepack (F := F) (G := G) (T := T)) := by
  rw [sharedLabelJoint_fst ρ τ, sharedLabelJoint_snd ρ τ]
  apply Measure.ext_of_singleton
  rintro ⟨⟨f, t⟩, ⟨g, s⟩⟩
  rw [prod_singleton, prod_singleton, prod_singleton]
  rw [Measure.map_apply measurable_sharedRepack (measurableSet_singleton _)]
  have hpre :
      (sharedRepack (F := F) (G := G) (T := T)) ⁻¹'
          ({((f, t), (g, s))} : Set ((F × T) × (G × T))) =
        ({((f, g), (t, s))} : Set ((F × G) × (T × T))) := by
    ext z
    rcases z with ⟨⟨f', g'⟩, ⟨t', s'⟩⟩
    simp [sharedRepack] <;> aesop
  rw [hpre, prod_singleton, prod_singleton, prod_singleton]
  ac_rfl

private theorem klDiv_prod_right_eq
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (κ η : Measure B) [IsProbabilityMeasure κ] [IsProbabilityMeasure η] :
    klDiv (μ.prod κ) (μ.prod η) = klDiv κ η := by
  have hswap :=
    klDiv_map_eq_of_measurable_leftInverse
      (μ.prod κ) (μ.prod η)
      Prod.swap Prod.swap measurable_swap measurable_swap
      (by intro z; cases z; rfl)
  rw [Measure.prod_swap, Measure.prod_swap] at hswap
  have hleft := InformationTheory.klDiv_compProd_left
    κ η (Kernel.const B μ)
  have hleft' : klDiv (κ.prod μ) (η.prod μ) = klDiv κ η := by
    simpa only [Measure.compProd_const] using hleft
  exact hswap.symm.trans hleft'

private theorem klDiv_prod_eq_add
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ η : Measure B) [IsProbabilityMeasure κ] [IsProbabilityMeasure η] :
    klDiv (μ.prod κ) (ν.prod η) = klDiv μ ν + klDiv κ η := by
  have hchain := InformationTheory.klDiv_compProd_eq_add
    μ ν (Kernel.const A κ) (Kernel.const A η)
  simpa only [Measure.compProd_const, klDiv_prod_right_eq μ κ η] using hchain

theorem p_evo_02
    (ρ : Measure (F × G)) [IsProbabilityMeasure ρ]
    (τ : Measure T) [IsProbabilityMeasure τ] :
    mutualInfo (sharedLabelJoint ρ τ) =
      mutualInfo ρ + discreteShannonEntropy τ := by
  have href := sharedLabelJoint_reference ρ τ
  unfold mutualInfo
  rw [href]
  unfold sharedLabelJoint
  have hmap :=
    klDiv_map_eq_of_measurable_leftInverse
      (ρ.prod (copyJoint τ))
      ((ρ.fst.prod ρ.snd).prod (τ.prod τ))
      (sharedRepack (F := F) (G := G) (T := T))
      (sharedUnpack (F := F) (G := G) (T := T))
      measurable_sharedRepack measurable_sharedUnpack
      sharedUnpack_leftInverse
  rw [hmap]
  rw [klDiv_prod_eq_add]
  rw [copy_kl_eq_discreteShannonEntropy]

end

end UEOT.V3.EvolutionSharedLabel
