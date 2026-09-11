import UEOT.V3.PredictableOLSScore
import Mathlib.Tactic

/-!
# P-INV-05 — source-indexed adapted score process

The mathematical statement is naturally indexed by source times `t = 1,2,...`:

* `phi (t+1)` is measurable with respect to the past sigma-algebra `F t`;
* `xi (t+1)` is measurable with respect to the current sigma-algebra `F (t+1)`.

Mathlib's martingale accumulation lemmas are indexed from zero.  We therefore
shift the filtration and score process by one step.  The theorem below proves
that the score is strongly adapted; this removes `StronglyAdapted` as an
independent technical assumption from the eventual source-facing theorem.
-/

namespace UEOT.V3.PredictableOLSSourceAdapted

open MeasureTheory ProbabilityTheory

universe uΩ

variable {Ω : Type uΩ} [mΩ : MeasurableSpace Ω]

/-- Shift a Nat-indexed filtration so index `n` represents source time `n+1`. -/
def succFiltration (F : Filtration ℕ mΩ) : Filtration ℕ mΩ where
  seq n := F (n + 1)
  mono' := by
    intro i j hij
    exact F.mono (Nat.add_le_add_right hij 1)
  le' n := F.le (n + 1)

@[simp]
theorem succFiltration_apply (F : Filtration ℕ mΩ) (n : ℕ) :
    succFiltration F n = F (n + 1) := rfl

/-- Source-indexed score: Mathlib index `n` corresponds to source time `n+1`. -/
def shiftedScoreProcess {d : ℕ}
    (phi : ℕ → Ω → Fin d → ℝ) (xi : ℕ → Ω → ℝ) (j : Fin d) :
    ℕ → Ω → ℝ :=
  fun n ω => phi (n + 1) ω j * xi (n + 1) ω

/-- Predictable design plus current-time measurability of the noise implies
strong adaptedness of the shifted score process. -/
theorem shiftedScore_stronglyAdapted
    {d : ℕ}
    (F : Filtration ℕ mΩ)
    (phi : ℕ → Ω → Fin d → ℝ)
    (xi : ℕ → Ω → ℝ)
    (j : Fin d)
    (hphi : ∀ n j, @Measurable Ω ℝ (F n) inferInstance
      (fun ω => phi (n + 1) ω j))
    (hxi : ∀ n, @Measurable Ω ℝ (F (n + 1)) inferInstance
      (xi (n + 1))) :
    StronglyAdapted (succFiltration F) (shiftedScoreProcess phi xi j) := by
  apply Adapted.stronglyAdapted
  intro n
  change @Measurable Ω ℝ (F (n + 1)) inferInstance
    (fun ω => phi (n + 1) ω j * xi (n + 1) ω)
  have hphi_now : @Measurable Ω ℝ (F (n + 1)) inferInstance
      (fun ω => phi (n + 1) ω j) :=
    (hphi n j).mono (F.mono (Nat.le_add_right n 1)) le_rfl
  exact hphi_now.mul (hxi n)

end UEOT.V3.PredictableOLSSourceAdapted
