import UEOT.V3.Compression.InvariantSetGaugeInvariance
import UEOT.V3.FiniteCesaroInvariant

/-!
# Cesaro occupation gauge invariance

Set-valued invariant GOA is only the stationary target set.  This module adds
the trajectory-facing statement: under exact finite kernel conjugacy, every
finite-time orbit law and every Cesaro occupation average commute exactly with
state relabeling.  Consequently every convergent Cesaro subsequence transports
to the relabeled limit.

No contraction, aperiodicity, irreducibility, or uniqueness is used.
-/

namespace UEOT.V3.Compression.CesaroOccupationGaugeInvariance

open Filter Topology
open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.FiniteCesaroInvariant
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.GoaGaugeInvariance
open UEOT.V3.Compression.GaugeSemanticTransfer

universe uX uS uA

noncomputable section

variable {S : Type uS} [Fintype S] [Nonempty S]

noncomputable local instance stateDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- The frozen finite-chain orbit is one repeated `step`. -/
theorem orbit_succ_eq_step
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (mu : stdSimplex ℝ S) (n : ℕ) :
    orbit P hP mu (n + 1) = step P hP (orbit P hP mu n) := by
  apply Subtype.ext
  exact orbit_succ P hP mu n

/-- Exact kernel conjugacy transports every finite-time orbit law. -/
theorem orbit_relabel_of_conjugate
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t))
    (mu : stdSimplex ℝ S) :
    ∀ n,
      relabelSimplex e (orbit P hP mu n) =
        orbit Q hQ (relabelSimplex e mu) n := by
  intro n
  induction n with
  | zero =>
      apply Subtype.ext
      funext y
      rcases e.surjective y with ⟨s, rfl⟩
      have hP0 := congrFun (orbit_zero P hP mu) s
      have hQ0 := congrFun (orbit_zero Q hQ (relabelSimplex e mu)) (e s)
      calc
        (relabelSimplex e (orbit P hP mu 0)) (e s) =
            (orbit P hP mu 0) s :=
          relabelSimplex_apply_e e (orbit P hP mu 0) s
        _ = mu s := hP0
        _ = (relabelSimplex e mu) (e s) :=
          (relabelSimplex_apply_e e mu s).symm
        _ = (orbit Q hQ (relabelSimplex e mu) 0) (e s) := hQ0.symm
  | succ n ih =>
      rw [orbit_succ_eq_step, orbit_succ_eq_step]
      rw [step_relabel_of_conjugate P Q hP hQ e hconj]
      rw [ih]

/-- Every finite Cesaro occupation average is exactly gauge covariant. -/
theorem cesaroRow_relabel_of_conjugate
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t))
    (mu : stdSimplex ℝ S) (n : ℕ) :
    relabelSimplex e (cesaroRow P hP mu n) =
      cesaroRow Q hQ (relabelSimplex e mu) n := by
  apply Subtype.ext
  funext y
  rcases e.surjective y with ⟨s, rfl⟩
  have hsource := congrFun (cesaroRow_coe P hP mu n) s
  have htarget :=
    congrFun (cesaroRow_coe Q hQ (relabelSimplex e mu) n) (e s)
  calc
    (relabelSimplex e (cesaroRow P hP mu n)) (e s) =
        (cesaroRow P hP mu n) s :=
      relabelSimplex_apply_e e (cesaroRow P hP mu n) s
    _ = ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ t ∈ Finset.range (n + 1), (orbit P hP mu t) s := by
      simpa only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] using hsource
    _ = ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ t ∈ Finset.range (n + 1),
          (orbit Q hQ (relabelSimplex e mu) t) (e s) := by
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      have hOrbit := orbit_relabel_of_conjugate P Q hP hQ e hconj mu t
      have hcoordRaw :=
        congrArg (fun nu : stdSimplex ℝ S => nu (e s)) hOrbit
      calc
        (orbit P hP mu t) s =
            (relabelSimplex e (orbit P hP mu t)) (e s) :=
          (relabelSimplex_apply_e e (orbit P hP mu t) s).symm
        _ = (orbit Q hQ (relabelSimplex e mu) t) (e s) := hcoordRaw
    _ = (cesaroRow Q hQ (relabelSimplex e mu) n) (e s) := by
      simpa only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] using htarget.symm

/-- Convergent Cesaro subsequences transport to the relabeled limiting law.

This gives a trajectory-level gauge statement compatible with P-GOA-01 even
when there are many invariant laws and the full Cesaro sequence is not assumed
to converge. -/
theorem cesaro_subseq_limit_relabel_of_conjugate
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t))
    (mu nu : stdSimplex ℝ S)
    (phi : ℕ → ℕ)
    (hlim : Tendsto (cesaroRow P hP mu ∘ phi) atTop (𝓝 nu)) :
    Tendsto
      (cesaroRow Q hQ (relabelSimplex e mu) ∘ phi)
      atTop (𝓝 (relabelSimplex e nu)) := by
  have hrelabeled : Tendsto
      (relabelSimplex e ∘ (cesaroRow P hP mu ∘ phi))
      atTop (𝓝 (relabelSimplex e nu)) := by
    rw [tendsto_subtype_rng]
    rw [tendsto_pi_nhds]
    intro y
    rcases e.surjective y with ⟨s, rfl⟩
    have hval : Tendsto
        (fun n => ((cesaroRow P hP mu ∘ phi) n) s)
        atTop (𝓝 (nu s)) := by
      have hcoe := tendsto_subtype_rng.mp hlim
      exact (tendsto_pi_nhds.mp hcoe) s
    convert hval using 1
    · funext i
      exact relabelSimplex_apply_e e ((cesaroRow P hP mu ∘ phi) i) s
    · exact congrArg nhds (relabelSimplex_apply_e e nu s)
  convert hrelabeled using 1
  funext n
  exact (cesaroRow_relabel_of_conjugate P Q hP hQ e hconj mu (phi n)).symm

/-- Exact semantic quotient gauge transports the complete finite Cesaro
occupation sequence for any deterministic selector. -/
theorem selectorCesaroRow_gaugeInvariant
    {X : Type uX} [Fintype X] [Nonempty X]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (Q R : ExactControlQuotient X S (fun _ => Act))
    (e : S ≃ S)
    (hsem : SemanticRelabel Q R e)
    (sigma : S → Act)
    (mu : stdSimplex ℝ S) (n : ℕ) :
    relabelSimplex e
        (cesaroRow
          (selectorClosedLoopMatrix Q.macroModel sigma)
          (selectorClosedLoopMatrix_rowStochastic Q.macroModel sigma)
          mu n) =
      cesaroRow
        (selectorClosedLoopMatrix R.macroModel (transportSelector e sigma))
        (selectorClosedLoopMatrix_rowStochastic
          R.macroModel (transportSelector e sigma))
        (relabelSimplex e mu) n := by
  apply cesaroRow_relabel_of_conjugate
  intro s t
  exact selectorClosedLoop_conjugate_of_semanticRelabel
    Q R e hsem sigma s t

end

end UEOT.V3.Compression.CesaroOccupationGaugeInvariance
