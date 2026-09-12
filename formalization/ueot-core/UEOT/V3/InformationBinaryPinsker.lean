import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# P-INFO-02 foundation — binary Pinsker inequality

The frozen P-INFO-02 source theorem ultimately needs the measure-level bound

`2 * D_TV(μ,ν)^2 ≤ KL(μ || ν)`.

Pinned Mathlib provides measure-theoretic KL and its data-processing theorem,
but no directly reusable measure-level Pinsker theorem was found.  This module
proves the analytic two-point core without introducing an information-theory
axiom.  The next layer reduces arbitrary measurable events to this binary case
and then takes the event supremum.

Proof architecture: the standard convexity proof of binary Pinsker, adapted and
cross-checked against the Apache-2.0 implementation
`szl-holdings/lutar-lean/Lutar/Wave17/BinaryPinsker.lean` (Copyright © 2026
Lutar, Stephen P. / SZL Holdings).  The UEOT version is adjusted for the pinned
Lean 4.33.1 / Mathlib API and kept as a local reusable lemma rather than treated
as a UEOT-original information-theory result.
-/

namespace UEOT.V3.InformationBinaryPinsker

open Real Set

/-- Binary KL minus the Pinsker quadratic term, written without divisions. -/
noncomputable def gapBin (q p : ℝ) : ℝ :=
  p * (Real.log p - Real.log q) +
    (1 - p) * (Real.log (1 - p) - Real.log (1 - q)) -
      2 * (p - q) ^ 2

/-- First derivative of `gapBin q`. -/
noncomputable def gapBinDeriv (q p : ℝ) : ℝ :=
  Real.log p - Real.log q - Real.log (1 - p) + Real.log (1 - q) -
    4 * (p - q)

theorem hasDerivAt_gapBin (q p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (gapBin q) (gapBinDeriv q p) p := by
  unfold gapBin gapBinDeriv
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hlp : HasDerivAt (fun x => x * (Real.log x - Real.log q))
      (Real.log p - Real.log q + 1) p := by
    have h :=
      (hasDerivAt_id p).mul
        ((Real.hasDerivAt_log (ne_of_gt hp)).sub_const (Real.log q))
    convert h using 1
    field_simp
  have hrp :
      HasDerivAt
        (fun x => (1 - x) * (Real.log (1 - x) - Real.log (1 - q)))
        (-(Real.log (1 - p) - Real.log (1 - q) + 1)) p := by
    have hin : HasDerivAt (fun x : ℝ => 1 - x) (-1) p := by
      simpa using (hasDerivAt_id p).const_sub (1 : ℝ)
    have hlog :
        HasDerivAt (fun x => Real.log (1 - x) - Real.log (1 - q))
          ((1 - p)⁻¹ * (-1)) p :=
      ((Real.hasDerivAt_log (ne_of_gt h1p)).comp p hin).sub_const
        (Real.log (1 - q))
    have h := hin.mul hlog
    convert h using 1
    field_simp
    ring
  have hquad :
      HasDerivAt (fun x => 2 * (x - q) ^ 2) (4 * (p - q)) p := by
    have hb : HasDerivAt (fun x : ℝ => x - q) 1 p :=
      (hasDerivAt_id p).sub_const q
    have h := (hb.pow 2).const_mul (2 : ℝ)
    convert h using 1
    ring
  have h := (hlp.add hrp).sub hquad
  convert h using 1
  ring

theorem hasDerivAt_gapBinDeriv (q p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (gapBinDeriv q) (p⁻¹ + (1 - p)⁻¹ - 4) p := by
  unfold gapBinDeriv
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hlog1 : HasDerivAt (fun x => Real.log x) p⁻¹ p :=
    Real.hasDerivAt_log (ne_of_gt hp)
  have hin : HasDerivAt (fun x : ℝ => 1 - x) (-1) p := by
    simpa using (hasDerivAt_id p).const_sub (1 : ℝ)
  have hlog2 : HasDerivAt (fun x => Real.log (1 - x))
      ((1 - p)⁻¹ * (-1)) p :=
    (Real.hasDerivAt_log (ne_of_gt h1p)).comp p hin
  have hquad : HasDerivAt (fun x : ℝ => 4 * (x - q)) 4 p := by
    have hb : HasDerivAt (fun x : ℝ => x - q) 1 p :=
      (hasDerivAt_id p).sub_const q
    simpa using hb.const_mul 4
  have step1 : HasDerivAt (fun x => Real.log x - Real.log q) p⁻¹ p :=
    hlog1.sub_const _
  have step2 :
      HasDerivAt (fun x => Real.log x - Real.log q - Real.log (1 - x))
        (p⁻¹ - (1 - p)⁻¹ * (-1)) p :=
    step1.sub hlog2
  have step3 :
      HasDerivAt
        (fun x => Real.log x - Real.log q - Real.log (1 - x) +
          Real.log (1 - q))
        (p⁻¹ - (1 - p)⁻¹ * (-1)) p :=
    step2.add_const _
  have step4 := step3.sub hquad
  convert step4 using 1
  ring

theorem gapBinDeriv_diag (q : ℝ) : gapBinDeriv q q = 0 := by
  unfold gapBinDeriv
  ring

theorem gapBin_diag (q : ℝ) : gapBin q q = 0 := by
  unfold gapBin
  ring

/-- Elementary curvature lower bound used by binary Pinsker. -/
theorem inv_add_inv_ge_four (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    4 ≤ p⁻¹ + (1 - p)⁻¹ := by
  have h1p : (0 : ℝ) < 1 - p := by linarith
  rw [inv_eq_one_div, inv_eq_one_div,
    div_add_div _ _ (ne_of_gt hp) (ne_of_gt h1p),
    le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * p - 1)]

theorem differentiableAt_gapBin (q p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    DifferentiableAt ℝ (gapBin q) p :=
  (hasDerivAt_gapBin q p hp hp1).differentiableAt

theorem differentiableAt_gapBinDeriv
    (q p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    DifferentiableAt ℝ (gapBinDeriv q) p :=
  (hasDerivAt_gapBinDeriv q p hp hp1).differentiableAt

theorem deriv_gapBin (q p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    deriv (gapBin q) p = gapBinDeriv q p :=
  (hasDerivAt_gapBin q p hp hp1).deriv

theorem deriv_gapBinDeriv_nonneg
    (q p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 ≤ deriv (gapBinDeriv q) p := by
  rw [(hasDerivAt_gapBinDeriv q p hp hp1).deriv]
  have h := inv_add_inv_ge_four p hp hp1
  linarith

theorem monotoneOn_gapBinDeriv
    {a b q : ℝ} (ha : 0 < a) (hb : b < 1) :
    MonotoneOn (gapBinDeriv q) (Set.Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · intro x hx
    rw [Set.mem_Icc] at hx
    exact
      ((hasDerivAt_gapBinDeriv q x (by linarith [hx.1])
        (by linarith [hx.2])).continuousAt).continuousWithinAt
  · rw [interior_Icc]
    intro x hx
    rw [Set.mem_Ioo] at hx
    exact
      (differentiableAt_gapBinDeriv q x (by linarith [hx.1])
        (by linarith [hx.2])).differentiableWithinAt
  · rw [interior_Icc]
    intro x hx
    rw [Set.mem_Ioo] at hx
    exact deriv_gapBinDeriv_nonneg q x (by linarith [hx.1])
      (by linarith [hx.2])

theorem gapBin_nonneg
    (q p : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hp : 0 < p) (hp1 : p < 1) :
    0 ≤ gapBin q p := by
  rcases le_total q p with hqp | hpq
  · have hderiv_nonneg : ∀ x ∈ Set.Ioo q p, 0 ≤ deriv (gapBin q) x := by
      intro x hx
      rw [Set.mem_Ioo] at hx
      have hx0 : 0 < x := lt_trans hq hx.1
      have hx1 : x < 1 := lt_trans hx.2 hp1
      rw [deriv_gapBin q x hx0 hx1]
      have hmono :=
        monotoneOn_gapBinDeriv (a := q) (b := p) (q := q) hq hp1
      have hle : gapBinDeriv q q ≤ gapBinDeriv q x :=
        hmono
          (Set.mem_Icc.mpr ⟨le_refl q, hqp⟩)
          (Set.mem_Icc.mpr ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
          (le_of_lt hx.1)
      rwa [gapBinDeriv_diag] at hle
    have hmono : MonotoneOn (gapBin q) (Set.Icc q p) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc q p)
      · intro x hx
        rw [Set.mem_Icc] at hx
        exact
          ((hasDerivAt_gapBin q x (by linarith [hx.1])
            (by linarith [hx.2])).continuousAt).continuousWithinAt
      · rw [interior_Icc]
        intro x hx
        rw [Set.mem_Ioo] at hx
        exact
          (differentiableAt_gapBin q x (by linarith [hx.1])
            (by linarith [hx.2])).differentiableWithinAt
      · rw [interior_Icc]
        exact hderiv_nonneg
    have hle :=
      hmono
        (Set.mem_Icc.mpr ⟨le_refl q, hqp⟩)
        (Set.mem_Icc.mpr ⟨hqp, le_refl p⟩) hqp
    rwa [gapBin_diag] at hle
  · have hderiv_nonpos : ∀ x ∈ Set.Ioo p q, deriv (gapBin q) x ≤ 0 := by
      intro x hx
      rw [Set.mem_Ioo] at hx
      have hx0 : 0 < x := lt_trans hp hx.1
      have hx1 : x < 1 := lt_trans hx.2 hq1
      rw [deriv_gapBin q x hx0 hx1]
      have hmono :=
        monotoneOn_gapBinDeriv (a := p) (b := q) (q := q) hp hq1
      have hle : gapBinDeriv q x ≤ gapBinDeriv q q :=
        hmono
          (Set.mem_Icc.mpr ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
          (Set.mem_Icc.mpr ⟨hpq, le_refl q⟩)
          (le_of_lt hx.2)
      rwa [gapBinDeriv_diag] at hle
    have hanti : AntitoneOn (gapBin q) (Set.Icc p q) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc p q)
      · intro x hx
        rw [Set.mem_Icc] at hx
        exact
          ((hasDerivAt_gapBin q x (by linarith [hx.1])
            (by linarith [hx.2])).continuousAt).continuousWithinAt
      · rw [interior_Icc]
        intro x hx
        rw [Set.mem_Ioo] at hx
        exact
          (differentiableAt_gapBin q x (by linarith [hx.1])
            (by linarith [hx.2])).differentiableWithinAt
      · rw [interior_Icc]
        exact hderiv_nonpos
    have hle :=
      hanti
        (Set.mem_Icc.mpr ⟨le_refl p, hpq⟩)
        (Set.mem_Icc.mpr ⟨hpq, le_refl q⟩) hpq
    rwa [gapBin_diag] at hle

/-- Binary Pinsker on the open probability simplex. -/
theorem binary_pinsker_open
    (q p : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hp : 0 < p) (hp1 : p < 1) :
    2 * (p - q) ^ 2 ≤
      p * (Real.log p - Real.log q) +
        (1 - p) * (Real.log (1 - p) - Real.log (1 - q)) := by
  have h := gapBin_nonneg q p hq hq1 hp hp1
  unfold gapBin at h
  linarith

end UEOT.V3.InformationBinaryPinsker
