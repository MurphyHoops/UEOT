import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCMechanisticPaths
import Mathlib.Tactic.Linarith

/-!
# SISC quantitative stability: persistence of prediction error ≠ formation

Formation tolerance grows additively with world/parent residuals, while the
realization error is uniformly controlled by a contractive realized
transport, provided `0 ≤ M < 1`. These are two separate mechanisms.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

/-- The exact finite-time accumulation of formation residuals is linear. -/
theorem formation_path_budget_closed_form
    (tau deltaWorld deltaParent : ℝ) (n : ℕ) :
    formationPathBudget tau deltaWorld deltaParent n =
      tau + (n : ℝ) * (deltaWorld + deltaParent) := by
  induction n with
  | zero => simp [formationPathBudget]
  | succ n ih =>
      simp only [formationPathBudget, ih, Nat.cast_add, Nat.cast_one]
      ring

/-- A strict realized-transport contraction gives a horizon-independent
quantitative bound, even if formation residuals grow. -/
theorem accumulated_error_uniform_of_contraction
    (delta M : ℝ) (hdelta : 0 ≤ delta)
    (hM : 0 ≤ M) (hstrict : M < 1) (n : ℕ) :
    accumulatedPathError delta M n ≤ delta / (1 - M) := by
  have hden : 0 < 1 - M := by linarith
  induction n with
  | zero =>
      simp only [accumulatedPathError]
      exact div_nonneg hdelta (le_of_lt hden)
  | succ n ih =>
      have hmul : M * accumulatedPathError delta M n ≤
          M * (delta / (1 - M)) :=
        mul_le_mul_of_nonneg_left ih hM
      have hid : delta + M * (delta / (1 - M)) = delta / (1 - M) := by
        field_simp
        ring
      change delta + M * accumulatedPathError delta M n ≤ delta / (1 - M)
      linarith

/-- Mechanistic n-step realized continuation remains uniformly controlled
under strict contraction. The separately stated *formation* budget may still
grow, so this cannot certify ontic sameness or infinite-time objecthood. -/
theorem contracted_finite_mechanism_realization_bound
    {Obs : Type*} [Fintype Obs]
    {X : Type*} {P : Type*} {D : Type*} [PseudoMetricSpace D]
    (K : FiniteResponseChannel Obs Obs)
    (actual : X → Obs → ℝ) (predict : P → Obs → ℝ)
    (tx : X → X) (tp : P → P)
    (B : P → D) (T : D → D)
    (tau deltaWorld deltaParent deltaBind M : ℝ)
    (hdelta : 0 ≤ deltaBind) (hM : 0 ≤ M) (hstrict : M < 1)
    (hWorld : ∀ x j,
      |actual (tx x) j - ∑ i, K.weight j i * actual x i| ≤ deltaWorld)
    (hParent : ∀ p j,
      |predict (tp p) j - ∑ i, K.weight j i * predict p i| ≤ deltaParent)
    (hBind : ∀ p, dist (B (tp p)) (T (B p)) ≤ deltaBind)
    (hLip : ∀ d e, dist (T d) (T e) ≤ M * dist d e)
    (x : X) (p : P)
    (h0 : FormedByResponse actual predict tau x p) (n : ℕ) :
    ∃ s : X × P,
      DirectedFinitePath (PairedTransportEdge tx tp) n (x, p) s ∧
      FormedByResponse actual predict
        (formationPathBudget tau deltaWorld deltaParent n) s.1 s.2 ∧
      dist (B s.2) (iterateResponse T n (B p)) ≤ deltaBind / (1 - M) := by
  obtain ⟨s, hpath, hformed, herr⟩ :=
    finite_channel_formed_history_with_realization_bound K actual predict
      tx tp B T tau deltaWorld deltaParent deltaBind M hM
      hWorld hParent hBind hLip x p h0 n
  exact ⟨s, hpath, hformed,
    herr.trans (accumulated_error_uniform_of_contraction deltaBind M
      hdelta hM hstrict n)⟩

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
