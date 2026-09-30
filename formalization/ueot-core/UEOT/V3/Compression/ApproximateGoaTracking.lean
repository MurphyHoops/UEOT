import UEOT.V3.Compression.TransportCertificate
import UEOT.V3.Compression.ContractiveFixedPoint
import UEOT.V3.Compression.OccupationLimitInvariance
import UEOT.V3.CoreOperationalAssembly
import UEOT.V3.FiniteDiscountedApproxQuotientBounds

/-!
# Approximate Agency / near-GOA tracking under time-varying closed loops

This module is the first end-to-end quantitative lane that brings M-TC back
into the finite Agency -> GOD -> GOA architecture.

The key point is that an approximate or drifting agent need not itself induce
one stationary Markov kernel.  We therefore do not invent an "approximate
stationary law".  Instead, a Dobrushin-stable reference closed loop supplies a
unique invariant law, while a sequence of time-varying stochastic kernels is
allowed to drive the actual state law.  Rowwise TV defects are injected at each
step and M-TC's weighted-chain theorem propagates them toward the reference
GOA.
-/

namespace UEOT.V3.Compression.ApproximateGoaTracking

open scoped BigOperators
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.FiniteDobrushin
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.Compression.TransportCertificate
open UEOT.V3.Compression.ContractiveFixedPoint
open UEOT.V3.Compression.OccupationLimitInvariance

universe uS uA uM

noncomputable local instance stateDecidableEq (S : Type uS) : DecidableEq S :=
  Classical.decEq S

local instance stateMeasurableSpace (S : Type uS) : MeasurableSpace S := ⊤

/-- Time-varying kernels that remain rowwise close to one Dobrushin-stable
reference kernel track its invariant law with the exact M-TC weighted defect
formula.

Existence of `mustar` is supplied through the M-OI P-GOA-01 route.  The
Dobrushin margin then gives uniqueness through M-CF.  The quantitative tracking
bound itself is M-TC's `weighted_chain_bound`: contraction transports the old
defect and the rowwise kernel mismatch injects a fresh local defect `ε n`. -/
theorem timeVarying_kernel_near_goa
    {S : Type uS} [Fintype S] [Nonempty S]
    (Pstar : Matrix S S ℝ)
    (hPstar : Pstar ∈ Matrix.rowStochastic ℝ S)
    (halpha : dobrushinAlpha Pstar hPstar < 1)
    (Pseq : ℕ → Matrix S S ℝ)
    (hPseq : ∀ n, Pseq n ∈ Matrix.rowStochastic ℝ S)
    (mu : ℕ → stdSimplex ℝ S)
    (hmu : ∀ n, mu (n + 1) = step (Pseq n) (hPseq n) (mu n))
    (ε : ℕ → ℝ)
    (hrow : ∀ n x,
      crossRowTV Pstar hPstar (Pseq n) (hPseq n) x ≤ ε n) :
    ∃ mustar : stdSimplex ℝ S,
      step Pstar hPstar mustar = mustar ∧
      (∀ nu : stdSimplex ℝ S,
        step Pstar hPstar nu = nu → nu = mustar) ∧
      ∀ n,
        lawTV mustar (mu n) ≤
          (∏ _j ∈ Finset.range n, dobrushinAlpha Pstar hPstar) *
              lawTV mustar (mu 0) +
            ∑ k ∈ Finset.range n,
              ε k *
                ∏ _j ∈ Finset.Ico (k + 1) n,
                  dobrushinAlpha Pstar hPstar := by
  classical
  let s0 : S := Classical.choice inferInstance
  let mu0 : stdSimplex ℝ S := pureSimplex s0
  have hgoa := p_goa_01_via_occupationLimit Pstar hPstar mu0
  rcases hgoa.1 with ⟨mustar, phi, hphi, hlim⟩
  have hvec : Matrix.vecMul mustar.1 Pstar = mustar.1 :=
    hgoa.2 mustar phi hphi hlim
  have hmustar : step Pstar hPstar mustar = mustar := by
    apply Subtype.ext
    exact hvec
  have hcontract := dobrushin_contractiveWith Pstar hPstar halpha
  have hunique : ∀ nu : stdSimplex ℝ S,
      step Pstar hPstar nu = nu → nu = mustar := by
    intro nu hnu
    exact hcontract.fixedPoint_unique hnu hmustar
  refine ⟨mustar, hmustar, hunique, ?_⟩
  intro n
  let A : ℕ → Type uS := fun _ => stdSimplex ℝ S
  let defect : ∀ t, A t → A t → ℝ := fun _ ideal actual =>
    lawTV ideal actual
  let ideal : (t : ℕ) → A t := fun _ => mustar
  let actual : (t : ℕ) → A t := fun t => mu t
  let proxyStep : ∀ t, A t → A (t + 1) := fun _ nu =>
    step Pstar hPstar nu
  have hweighted := weighted_chain_bound
    defect ideal actual proxyStep
    (fun _ => dobrushinAlpha Pstar hPstar) ε
    (fun t => by
      dsimp [defect, ideal, actual, proxyStep]
      have hc := tv_step_le_dobrushin Pstar hPstar mustar (mu t)
      rw [hmustar] at hc
      exact hc)
    (fun t => by
      dsimp [defect, ideal, actual, proxyStep]
      exact lawTV_triangle mustar (step Pstar hPstar (mu t)) (mu (t + 1)))
    (fun t => by
      dsimp [defect, actual, proxyStep]
      rw [hmu t]
      exact tv_step_cross_le Pstar hPstar (Pseq t) (hPseq t)
        (mu t) (ε t) (hrow t))
    (fun _ => dobrushinAlpha_nonneg Pstar hPstar)
    n
  simpa [defect, ideal, actual] using hweighted

/-- Power form of the same near-GOA certificate. -/
theorem timeVarying_kernel_near_goa_power
    {S : Type uS} [Fintype S] [Nonempty S]
    (Pstar : Matrix S S ℝ)
    (hPstar : Pstar ∈ Matrix.rowStochastic ℝ S)
    (halpha : dobrushinAlpha Pstar hPstar < 1)
    (Pseq : ℕ → Matrix S S ℝ)
    (hPseq : ∀ n, Pseq n ∈ Matrix.rowStochastic ℝ S)
    (mu : ℕ → stdSimplex ℝ S)
    (hmu : ∀ n, mu (n + 1) = step (Pseq n) (hPseq n) (mu n))
    (ε : ℕ → ℝ)
    (hrow : ∀ n x,
      crossRowTV Pstar hPstar (Pseq n) (hPseq n) x ≤ ε n) :
    ∃ mustar : stdSimplex ℝ S,
      step Pstar hPstar mustar = mustar ∧
      (∀ nu : stdSimplex ℝ S,
        step Pstar hPstar nu = nu → nu = mustar) ∧
      ∀ n,
        lawTV mustar (mu n) ≤
          dobrushinAlpha Pstar hPstar ^ n * lawTV mustar (mu 0) +
            ∑ k ∈ Finset.range n,
              ε k * dobrushinAlpha Pstar hPstar ^ (n - (k + 1)) := by
  rcases timeVarying_kernel_near_goa
      Pstar hPstar halpha Pseq hPseq mu hmu ε hrow with
    ⟨mustar, hfix, huniq, hbound⟩
  refine ⟨mustar, hfix, huniq, ?_⟩
  intro n
  have h := hbound n
  simpa [Finset.prod_const, Nat.card_Ico] using h

/-- Uniform local kernel error gives a finite geometric near-GOA tube. -/
theorem timeVarying_kernel_near_goa_uniform
    {S : Type uS} [Fintype S] [Nonempty S]
    (Pstar : Matrix S S ℝ)
    (hPstar : Pstar ∈ Matrix.rowStochastic ℝ S)
    (halpha : dobrushinAlpha Pstar hPstar < 1)
    (Pseq : ℕ → Matrix S S ℝ)
    (hPseq : ∀ n, Pseq n ∈ Matrix.rowStochastic ℝ S)
    (mu : ℕ → stdSimplex ℝ S)
    (hmu : ∀ n, mu (n + 1) = step (Pseq n) (hPseq n) (mu n))
    (ε : ℕ → ℝ) (εbar : ℝ)
    (hrow : ∀ n x,
      crossRowTV Pstar hPstar (Pseq n) (hPseq n) x ≤ ε n)
    (hεbar : ∀ n, ε n ≤ εbar) :
    ∃ mustar : stdSimplex ℝ S,
      step Pstar hPstar mustar = mustar ∧
      (∀ nu : stdSimplex ℝ S,
        step Pstar hPstar nu = nu → nu = mustar) ∧
      ∀ n,
        lawTV mustar (mu n) ≤
          dobrushinAlpha Pstar hPstar ^ n * lawTV mustar (mu 0) +
            εbar *
              ∑ j ∈ Finset.range n, dobrushinAlpha Pstar hPstar ^ j := by
  rcases timeVarying_kernel_near_goa_power
      Pstar hPstar halpha Pseq hPseq mu hmu ε hrow with
    ⟨mustar, hfix, huniq, hbound⟩
  refine ⟨mustar, hfix, huniq, ?_⟩
  intro n
  let alpha := dobrushinAlpha Pstar hPstar
  have halpha0 : 0 ≤ alpha := dobrushinAlpha_nonneg Pstar hPstar
  have hsum :
      (∑ k ∈ Finset.range n, ε k * alpha ^ (n - (k + 1))) ≤
        εbar * ∑ k ∈ Finset.range n, alpha ^ (n - (k + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_right (hεbar k)
      (pow_nonneg halpha0 _)
  have hreverse :
      (∑ k ∈ Finset.range n, alpha ^ (n - (k + 1))) =
        ∑ j ∈ Finset.range n, alpha ^ j := by
    calc
      (∑ k ∈ Finset.range n, alpha ^ (n - (k + 1))) =
          ∑ k ∈ Finset.range n, (1 : ℝ) ^ k * alpha ^ (n - 1 - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hklt : k < n := Finset.mem_range.mp hk
        have hexp : n - (k + 1) = n - 1 - k := by omega
        simp [hexp]
      _ = ∑ k ∈ Finset.range n, alpha ^ k * (1 : ℝ) ^ (n - 1 - k) :=
        geom_sum₂_comm (1 : ℝ) alpha n
      _ = ∑ j ∈ Finset.range n, alpha ^ j :=
        geom_sum₂_with_one alpha n
  have hbase := hbound n
  change
    lawTV mustar (mu n) ≤
      alpha ^ n * lawTV mustar (mu 0) +
        εbar * ∑ j ∈ Finset.range n, alpha ^ j
  calc
    lawTV mustar (mu n) ≤
        alpha ^ n * lawTV mustar (mu 0) +
          ∑ k ∈ Finset.range n, ε k * alpha ^ (n - (k + 1)) := by
      simpa [alpha] using hbase
    _ ≤ alpha ^ n * lawTV mustar (mu 0) +
          εbar * ∑ k ∈ Finset.range n, alpha ^ (n - (k + 1)) :=
      add_le_add le_rfl hsum
    _ = alpha ^ n * lawTV mustar (mu 0) +
          εbar * ∑ j ∈ Finset.range n, alpha ^ j := by
      rw [hreverse]

/-! ## Approximate-control specialization -/

/-- P-QUO-02's lifted macro-greedy policy: the canonical near-optimal GOD for
an approximate quotient. -/
noncomputable def approximateGodPolicy
    {S : Type uS} [Fintype S]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (Q : ApproxControlQuotient S M Abar) :
    StationaryPolicy (fun s => Abar (Q.f s)) :=
  quotientLiftedPolicy Q

/-- Quantitative approximate Agency -> GOD -> near-GOA theorem.

The baseline approximate quotient supplies a lifted macro-greedy policy whose
micro regret is at most `2D`.  The baseline micro closed loop under that exact
same policy is the reference GOA dynamics.  A time-varying sequence of other
micro models may then drift around the reference, provided their policy-induced
rows stay within `ε n` in TV.  M-TC propagates those local defects into the
near-GOA tracking bound.

The time-varying models share the same state/action carrier and discount is not
used by the tracking half; their only long-run obligation here is stochastic
policy-row proximity. -/
theorem approximate_god_and_timeVarying_near_goa
    {S : Type uS} [Fintype S] [Nonempty S]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (Q : ApproxControlQuotient S M Abar)
    (halpha :
      dobrushinAlpha
        (policyMatrix Q.micro (approximateGodPolicy Q))
        (policyMatrix_rowStochastic Q.micro (approximateGodPolicy Q)) < 1)
    (Mseq : ℕ → Model S (fun s => Abar (Q.f s)))
    (mu : ℕ → stdSimplex ℝ S)
    (hmu : ∀ n,
      mu (n + 1) =
        step
          (policyMatrix (Mseq n) (approximateGodPolicy Q))
          (policyMatrix_rowStochastic (Mseq n) (approximateGodPolicy Q))
          (mu n))
    (ε : ℕ → ℝ)
    (hrow : ∀ n x,
      crossRowTV
        (policyMatrix Q.micro (approximateGodPolicy Q))
        (policyMatrix_rowStochastic Q.micro (approximateGodPolicy Q))
        (policyMatrix (Mseq n) (approximateGodPolicy Q))
        (policyMatrix_rowStochastic (Mseq n) (approximateGodPolicy Q)) x ≤ ε n) :
    (∀ {t : ℕ} (x : S),
      0 ≤ Q.micro.optimalValue x -
        CausalPolicy.infiniteValue
          (selectorPolicy (Q.liftSelector Q.macroModel.greedyAction))
          Q.micro (t := t) x ∧
      Q.micro.optimalValue x -
        CausalPolicy.infiniteValue
          (selectorPolicy (Q.liftSelector Q.macroModel.greedyAction))
          Q.micro (t := t) x ≤ 2 * Q.D) ∧
    ∃ mustar : stdSimplex ℝ S,
      step
          (policyMatrix Q.micro (approximateGodPolicy Q))
          (policyMatrix_rowStochastic Q.micro (approximateGodPolicy Q))
          mustar = mustar ∧
      (∀ nu : stdSimplex ℝ S,
        step
            (policyMatrix Q.micro (approximateGodPolicy Q))
            (policyMatrix_rowStochastic Q.micro (approximateGodPolicy Q))
            nu = nu → nu = mustar) ∧
      ∀ n,
        lawTV mustar (mu n) ≤
          dobrushinAlpha
              (policyMatrix Q.micro (approximateGodPolicy Q))
              (policyMatrix_rowStochastic Q.micro (approximateGodPolicy Q)) ^ n *
            lawTV mustar (mu 0) +
          ∑ k ∈ Finset.range n,
            ε k *
              dobrushinAlpha
                (policyMatrix Q.micro (approximateGodPolicy Q))
                (policyMatrix_rowStochastic Q.micro (approximateGodPolicy Q)) ^
                  (n - (k + 1)) := by
  constructor
  · exact Q.p_quo_02.2
  · apply timeVarying_kernel_near_goa_power
      (policyMatrix Q.micro (approximateGodPolicy Q))
      (policyMatrix_rowStochastic Q.micro (approximateGodPolicy Q))
      halpha
      (fun n => policyMatrix (Mseq n) (approximateGodPolicy Q))
      (fun n => policyMatrix_rowStochastic (Mseq n) (approximateGodPolicy Q))
      mu hmu ε hrow

end UEOT.V3.Compression.ApproximateGoaTracking
