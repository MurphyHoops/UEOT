import UEOTQM.Selector

/-!
# Finite-spectrum bridge to the conditional family selector

The input is a finite list of lepton/quark representation orientations, a
declared nonzero cubic-anomaly unit, explicit extra matter, and explicit
additional cubic contributions.  The selector equation is an output.

The weak coefficient uses the declared SU(2) one-loop convention: a Weyl
doublet contributes 1/3, an extra Weyl field contributes (2/3) T(R), a
complex scalar (1/3) T(R), and a real scalar (1/6) T(R).  These physical
coefficient rules and the spectrum/window interpretation are sector inputs.
The module proves their finite arithmetic consequences.  It does not derive
representation theory, anomaly cancellation in a complete QFT, the existence
of a matching window, global anomalies, a vacuum, or masses.
-/

namespace UEOTQM.Spectrum

inductive Orientation where
  | direct
  | conjugate
  deriving DecidableEq, Repr

def Orientation.sign : Orientation → ℚ
  | .direct => 1
  | .conjugate => -1

def Orientation.directCount : Orientation → ℕ
  | .direct => 1
  | .conjugate => 0

/-- One color-singlet lepton and one color-fundamental quark multiplet.
Each supplies one weak doublet per color when active in the declared window. -/
structure Family where
  lepton : Orientation
  quark : Orientation
  leptonActive : Bool := true
  quarkActive : Bool := true
  deriving DecidableEq, Repr

/-- The two actual contributions of one family to the selected cubic channel. -/
def familyCubicTerms (nc : ℕ) (a : ℚ) (f : Family) : List ℚ :=
  [a * f.lepton.sign, (nc : ℚ) * a * f.quark.sign]

def familyCubic (nc : ℕ) (a : ℚ) : List Family → ℚ
  | [] => 0
  | f :: fs => (familyCubicTerms nc a f).sum + familyCubic nc a fs

def leptonCount : List Family → ℕ
  | [] => 0
  | f :: fs => f.lepton.directCount + leptonCount fs

def quarkCount : List Family → ℕ
  | [] => 0
  | f :: fs => f.quark.directCount + quarkCount fs

/-- Direct quark orientations are counted from entries, so the count bound is derived. -/
theorem quarkCount_le_length (fs : List Family) : quarkCount fs ≤ fs.length := by
  induction fs with
  | nil => simp [quarkCount]
  | cons f fs ih =>
      cases hq : f.quark <;>
        simp [quarkCount, hq, Orientation.directCount] <;> omega

/-- The finite row sum yields the mixed-orientation cubic expression. -/
theorem familyCubic_eq_counts (nc : ℕ) (a : ℚ) (fs : List Family) :
    familyCubic nc a fs =
      a * ((2 * (leptonCount fs : ℚ) - (fs.length : ℚ)) +
        (nc : ℚ) * (2 * (quarkCount fs : ℚ) - (fs.length : ℚ))) := by
  induction fs with
  | nil => simp [familyCubic, leptonCount, quarkCount]
  | cons f fs ih =>
      cases f with
      | mk l q la qa =>
          cases l <;> cases q <;>
            simp [familyCubic, familyCubicTerms, leptonCount, quarkCount,
              Orientation.sign, Orientation.directCount, ih, Nat.cast_add] <;> ring

/-- Homogeneous lepton orientation is an explicit template restriction. -/
theorem leptonCount_eq_length_of_homogeneous
    (fs : List Family) (h : ∀ f ∈ fs, f.lepton = .direct) :
    leptonCount fs = fs.length := by
  induction fs with
  | nil => simp [leptonCount]
  | cons f fs ih =>
      have hf : f.lepton = .direct := h f (by simp)
      have ht : ∀ g ∈ fs, g.lepton = .direct := by
        intro g hg
        exact h g (by simp [hg])
      simp [leptonCount, hf, Orientation.directCount, ih ht, Nat.add_comm]

inductive MatterKind where
  | weyl
  | complexScalar
  | realScalar
  deriving DecidableEq, Repr

def MatterKind.screeningFactor : MatterKind → ℚ
  | .weyl => 2 / 3
  | .complexScalar => 1 / 3
  | .realScalar => 1 / 6

/-- Dynkin index and signed Weyl anomaly are supplied representation data.
Scalars have zero cubic contribution by construction. -/
structure ExtraMatter where
  kind : MatterKind
  copies : ℕ
  weakIndex : ℚ
  weakIndex_nonneg : 0 ≤ weakIndex
  cubicUnit : ℚ := 0
  weakActive : Bool := true

def ExtraMatter.cubic (e : ExtraMatter) : ℚ :=
  match e.kind with
  | .weyl => (e.copies : ℚ) * e.cubicUnit
  | .complexScalar => 0
  | .realScalar => 0

def ExtraMatter.screening (e : ExtraMatter) : ℚ :=
  if e.weakActive then
    (e.copies : ℚ) * e.weakIndex * e.kind.screeningFactor
  else 0

/-- Ordinary positive matter weights cannot increase the fixed-carrier coefficient. -/
theorem ExtraMatter.screening_nonneg (e : ExtraMatter) : 0 ≤ e.screening := by
  have hi := e.weakIndex_nonneg
  cases ha : e.weakActive <;> cases hk : e.kind <;>
    simp [ExtraMatter.screening, ha, hk, MatterKind.screeningFactor] <;> positivity

def extraCubic (es : List ExtraMatter) : ℚ := (es.map ExtraMatter.cubic).sum

def extraScreening (es : List ExtraMatter) : ℚ := (es.map ExtraMatter.screening).sum

theorem extraScreening_nonneg (es : List ExtraMatter) : 0 ≤ extraScreening es := by
  induction es with
  | nil => simp [extraScreening]
  | cons e es ih =>
      simpa [extraScreening] using add_nonneg e.screening_nonneg ih

/-- Additional terms can describe a separately supplied completion or inflow.
No validity theorem for that mechanism is assumed here. -/
def totalCubic (nc : ℕ) (a : ℚ) (fs : List Family)
    (es : List ExtraMatter) (additional : List ℚ) : ℚ :=
  familyCubic nc a fs + extraCubic es + additional.sum

def familyWeakTerms (nc : ℕ) (f : Family) : List ℚ :=
  [if f.leptonActive then (1 : ℚ) / 3 else 0,
   if f.quarkActive then (nc : ℚ) / 3 else 0]

def familyScreening (nc : ℕ) : List Family → ℚ
  | [] => 0
  | f :: fs => (familyWeakTerms nc f).sum + familyScreening nc fs

/-- The weak multiplicity is obtained by summing both active ordinary rows. -/
theorem familyScreening_eq_of_active
    (nc : ℕ) (fs : List Family)
    (h : ∀ f ∈ fs, f.leptonActive = true ∧ f.quarkActive = true) :
    familyScreening nc fs = (fs.length : ℚ) * ((nc : ℚ) + 1) / 3 := by
  induction fs with
  | nil => simp [familyScreening]
  | cons f fs ih =>
      obtain ⟨hl, hq⟩ := h f (by simp)
      have ht : ∀ g ∈ fs, g.leptonActive = true ∧ g.quarkActive = true := by
        intro g hg
        exact h g (by simp [hg])
      simp [familyScreening, familyWeakTerms, hl, hq, ih ht, Nat.cast_add]
      ring

/-- The fixed SU(2) one-loop coefficient in the declared active-matter window. -/
def weakCoefficient (nc : ℕ) (fs : List Family) (es : List ExtraMatter) : ℚ :=
  22 / 3 - familyScreening nc fs - extraScreening es

/-- Cancellation of actual rows gives the selector's natural-number equation. -/
theorem selector_anomaly_of_spectrum
    (nc : ℕ) (a : ℚ) (fs : List Family)
    (es : List ExtraMatter) (additional : List ℚ)
    (ha : a ≠ 0)
    (hleptons : ∀ f ∈ fs, f.lepton = .direct)
    (hextra : extraCubic es + additional.sum = 0)
    (htotal : totalCubic nc a fs es additional = 0) :
    2 * nc * quarkCount fs + fs.length = nc * fs.length := by
  have hf : familyCubic nc a fs = 0 := by
    unfold totalCubic at htotal
    linarith
  rw [familyCubic_eq_counts, leptonCount_eq_length_of_homogeneous fs hleptons] at hf
  have hfactor := (mul_eq_zero.mp hf).resolve_left ha
  have hq : 2 * (nc : ℚ) * (quarkCount fs : ℚ) + (fs.length : ℚ) =
      (nc : ℚ) * (fs.length : ℚ) := by nlinarith [hfactor]
  exact_mod_cast hq

/-- Positivity and nonnegative extra screening imply the required strict budget. -/
theorem selector_budget_of_spectrum
    (nc : ℕ) (fs : List Family) (es : List ExtraMatter)
    (hactive : ∀ f ∈ fs, f.leptonActive = true ∧ f.quarkActive = true)
    (hpositive : 0 < weakCoefficient nc fs es) :
    fs.length * (nc + 1) < 22 := by
  have he := extraScreening_nonneg es
  unfold weakCoefficient at hpositive
  rw [familyScreening_eq_of_active nc fs hactive] at hpositive
  have hq : (fs.length : ℚ) * ((nc : ℚ) + 1) < 22 := by linarith
  exact_mod_cast hq

/--
Finite row data, the homogeneous template, cancellation, and the declared weak
window compose with the existing selector.  Neither its integer equation nor
its screening budget is a premise of this theorem.
-/
theorem spectrum_selects_three
    (nc : ℕ) (a : ℚ) (fs : List Family)
    (es : List ExtraMatter) (additional : List ℚ)
    (hcolor : 3 ≤ nc) (hfamilies : 0 < fs.length)
    (ha : a ≠ 0)
    (hleptons : ∀ f ∈ fs, f.lepton = .direct)
    (hactive : ∀ f ∈ fs, f.leptonActive = true ∧ f.quarkActive = true)
    (hextra : extraCubic es + additional.sum = 0)
    (htotal : totalCubic nc a fs es additional = 0)
    (hpositive : 0 < weakCoefficient nc fs es) :
    nc = 3 ∧ fs.length = 3 ∧ quarkCount fs = 1 := by
  exact UEOTQM.Selector.selects_three_without_atomicity nc fs.length (quarkCount fs)
    hcolor hfamilies (quarkCount_le_length fs)
    (selector_anomaly_of_spectrum nc a fs es additional ha hleptons hextra htotal)
    (selector_budget_of_spectrum nc fs es hactive hpositive)

def canonicalFamilies : List Family :=
  [⟨.direct, .direct, true, true⟩,
   ⟨.direct, .conjugate, true, true⟩,
   ⟨.direct, .conjugate, true, true⟩]

def oneHiggs : ExtraMatter :=
  ⟨.complexScalar, 1, 1 / 2, by norm_num, 0, true⟩

/-- Explicit three-family rows and one complex Higgs doublet give b2 = 19/6. -/
theorem canonical_rows_and_higgs :
    totalCubic 3 1 canonicalFamilies [oneHiggs] [] = 0 ∧
    weakCoefficient 3 canonicalFamilies [oneHiggs] = 19 / 6 ∧
    quarkCount canonicalFamilies = 1 := by
  norm_num [totalCubic, familyCubic, familyCubicTerms, canonicalFamilies,
    Orientation.sign, Orientation.directCount, extraCubic, ExtraMatter.cubic,
    weakCoefficient, familyScreening, familyWeakTerms, extraScreening,
    ExtraMatter.screening, MatterKind.screeningFactor, oneHiggs, quarkCount]

def mixedFamilies : List Family :=
  [⟨.direct, .direct, true, true⟩,
   ⟨.conjugate, .conjugate, true, true⟩]

/-- The wider lepton template has actual two-family rows with positive coefficient. -/
theorem mixed_two_family_rows :
    totalCubic 3 1 mixedFamilies [] [] = 0 ∧
    weakCoefficient 3 mixedFamilies [] = 14 / 3 ∧
    mixedFamilies.length = 2 ∧ leptonCount mixedFamilies = 1 := by
  norm_num [totalCubic, familyCubic, familyCubicTerms, mixedFamilies,
    Orientation.sign, Orientation.directCount, extraCubic,
    weakCoefficient, familyScreening, familyWeakTerms, extraScreening, leptonCount]

/-- Replicating actual rows preserves this anomaly and violates the weak window. -/
theorem replicated_six_family_rows :
    totalCubic 3 1 (canonicalFamilies ++ canonicalFamilies) [] [] = 0 ∧
    weakCoefficient 3 (canonicalFamilies ++ canonicalFamilies) [] = -(2 / 3) ∧
    (canonicalFamilies ++ canonicalFamilies).length = 6 := by
  norm_num [totalCubic, familyCubic, familyCubicTerms, canonicalFamilies,
    Orientation.sign, extraCubic, weakCoefficient, familyScreening,
    familyWeakTerms, extraScreening]

def singleFamily : List Family := [⟨.direct, .conjugate, true, true⟩]

/-- An extra signed contribution can cancel a one-family residue; hextra is essential. -/
theorem compensated_one_family_rows :
    familyCubic 3 1 singleFamily = -2 ∧
    totalCubic 3 1 singleFamily [] [2] = 0 ∧
    weakCoefficient 3 singleFamily [] = 6 ∧ singleFamily.length = 1 := by
  norm_num [totalCubic, familyCubic, familyCubicTerms, singleFamily,
    Orientation.sign, extraCubic, weakCoefficient, familyScreening,
    familyWeakTerms, extraScreening]

/-- A zero anomaly unit carries no family-count information. -/
theorem zero_anomaly_unit_one_family_rows :
    totalCubic 3 0 singleFamily [] [] = 0 ∧
    weakCoefficient 3 singleFamily [] = 6 ∧ singleFamily.length = 1 := by
  norm_num [totalCubic, familyCubic, familyCubicTerms, singleFamily,
    Orientation.sign, extraCubic, weakCoefficient, familyScreening,
    familyWeakTerms, extraScreening]

def twentyHiggs : ExtraMatter :=
  ⟨.complexScalar, 20, 1 / 2, by norm_num, 0, true⟩

/-- The necessary ordinary budget alone does not establish a positive full coefficient. -/
theorem extra_screening_closes_positive_window :
    canonicalFamilies.length * (3 + 1) < 22 ∧
    weakCoefficient 3 canonicalFamilies [twentyHiggs] = 0 := by
  norm_num [canonicalFamilies, weakCoefficient, familyScreening, familyWeakTerms,
    extraScreening, ExtraMatter.screening, MatterKind.screeningFactor, twentyHiggs]

end UEOTQM.Spectrum
