import UEOT.V3.FiniteCesaroInvariant
import UEOT.V3.FiniteDiscountedApproxQuotient
import UEOT.V3.TVSpan
import UEOT.V3.TransportDefect
import UEOT.V3.InformationZeroTV
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic

/-!
# P-GOA-02 — finite Dobrushin mixing margin

Frozen UEOT Core v3 §21.3 uses the canonical event-supremum total-variation
distance

`D_TV(p,q) = sup_A |p(A)-q(A)|`,

which on finite spaces is the standard `1/2 * L1` normalization.  For a finite
stochastic kernel `P`, the Dobrushin coefficient is the literal finite maximum

`alpha(P) = max_{x,x'} D_TV(P_x,P_x')`.

This module proves the exact Dobrushin contraction, combines it with P-GOA-01 to
obtain existence and uniqueness of an invariant law when `alpha(P) < 1`, and
proves the frozen stationary perturbation bound

`D_TV(mu,muhat) <= epsilon / (1 - alpha(P))`.

The proof stays in UEOT's event-supremum TV throughout; no raw-L1 surrogate or
factor-two renormalization is introduced.
-/

namespace UEOT.V3.FiniteDobrushin

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

universe uS

variable {S : Type uS} [Fintype S]

local instance : DecidableEq S := Classical.decEq S
local instance : MeasurableSpace S := ⊤

open UEOT.V3.FiniteDiscountedControl

/-- Canonical discrete PMF associated with a point of the finite probability simplex. -/
noncomputable def simplexPMF (mu : stdSimplex ℝ S) : PMF S :=
  FiniteProbabilityRow.ofRealRow mu.1
    (fun s => stdSimplex.zero_le mu s) (stdSimplex.sum_eq_one mu)

@[simp] theorem simplexPMF_toReal (mu : stdSimplex ℝ S) (s : S) :
    ((simplexPMF mu) s).toReal = mu.1 s := by
  exact FiniteProbabilityRow.ofRealRow_apply_toReal mu.1
    (fun x => stdSimplex.zero_le mu x) (stdSimplex.sum_eq_one mu) s

/-- Canonical discrete PMF associated with one row of a stochastic matrix. -/
noncomputable def rowPMF
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S) (x : S) : PMF S :=
  FiniteProbabilityRow.ofRealRow (P x)
    (fun _ => Matrix.nonneg_of_mem_rowStochastic hP)
    (Matrix.sum_row_of_mem_rowStochastic hP x)

@[simp] theorem rowPMF_toReal
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S) (x y : S) :
    ((rowPMF P hP x) y).toReal = P x y := by
  simp [rowPMF, FiniteProbabilityRow.ofRealRow_apply_toReal]

/-- One row-law step `mu P`, packaged back into the finite probability simplex. -/
def step
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (mu : stdSimplex ℝ S) : stdSimplex ℝ S := by
  refine ⟨Matrix.vecMul mu.1 P, ?_, ?_⟩
  · exact fun j =>
      Matrix.nonneg_vecMul_of_mem_rowStochastic hP
        (fun i => stdSimplex.zero_le mu i) j
  · have hm : mu.1 ⬝ᵥ (1 : S → ℝ) = 1 := by
      rw [dotProduct_one]
      exact stdSimplex.sum_eq_one mu
    have h := Matrix.vecMul_dotProduct_one_eq_one_rowStochastic hP hm
    simpa [dotProduct_one] using h

@[simp] theorem step_apply
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (mu : stdSimplex ℝ S) (y : S) :
    (step P hP mu).1 y = ∑ x, mu.1 x * P x y := by
  rfl

/-- Matrix row action agrees exactly with PMF bind by the row PMFs. -/
theorem simplexPMF_step_eq_bind
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (mu : stdSimplex ℝ S) :
    simplexPMF (step P hP mu) = (simplexPMF mu).bind (rowPMF P hP) := by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top (simplexPMF (step P hP mu)) y)
    (PMF.apply_ne_top ((simplexPMF mu).bind (rowPMF P hP)) y)).mp
  rw [simplexPMF_toReal, step_apply]
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (by
    intro a _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top (simplexPMF mu) a)
      (PMF.apply_ne_top (rowPMF P hP a) y))]
  simp_rw [ENNReal.toReal_mul, simplexPMF_toReal, rowPMF_toReal]

/-- Canonical event-supremum TV between two finite probability rows. -/
noncomputable def lawTV (mu nu : stdSimplex ℝ S) : ℝ :=
  FiniteProbabilityRow.tvDist (simplexPMF mu) (simplexPMF nu)

/-- Canonical event-supremum TV between two rows of the same kernel. -/
noncomputable def rowTV
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S) (x x' : S) : ℝ :=
  FiniteProbabilityRow.tvDist (rowPMF P hP x) (rowPMF P hP x')

/-- Canonical event-supremum TV between corresponding rows of two kernels. -/
noncomputable def crossRowTV
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S) (x : S) : ℝ :=
  FiniteProbabilityRow.tvDist (rowPMF P hP x) (rowPMF Q hQ x)

theorem lawTV_nonneg (mu nu : stdSimplex ℝ S) : 0 ≤ lawTV mu nu := by
  unfold lawTV FiniteProbabilityRow.tvDist
  exact UEOT.V3.TotalVariation.tvDist_nonneg _ _

theorem lawTV_triangle (mu nu rho : stdSimplex ℝ S) :
    lawTV mu rho ≤ lawTV mu nu + lawTV nu rho := by
  unfold lawTV FiniteProbabilityRow.tvDist
  exact UEOT.V3.TransportDefect.tvDist_triangle
    (simplexPMF mu).toMeasure (simplexPMF nu).toMeasure (simplexPMF rho).toMeasure

/-- A discrete PMF bind event probability is the expectation of the row-event probability. -/
theorem bind_measureReal_eq_integral
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (mu : stdSimplex ℝ S) (A : Set S) :
    ((simplexPMF mu).bind (rowPMF P hP)).toMeasure.real A =
      ∫ x, (rowPMF P hP x).toMeasure.real A ∂(simplexPMF mu).toMeasure := by
  rw [MeasureTheory.measureReal_def]
  rw [PMF.toMeasure_bind_apply
    (simplexPMF mu) (rowPMF P hP) A MeasurableSet.of_discrete]
  rw [tsum_fintype]
  rw [ENNReal.toReal_sum (by
    intro x _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top (simplexPMF mu) x)
      (measure_ne_top (rowPMF P hP x).toMeasure A))]
  simp_rw [ENNReal.toReal_mul, simplexPMF_toReal, ← MeasureTheory.measureReal_def]
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul, simplexPMF_toReal]

/-- Zero canonical TV between simplex laws implies equality of the laws. -/
theorem lawTV_eq_zero_imp_eq
    (mu nu : stdSimplex ℝ S) (hzero : lawTV mu nu = 0) : mu = nu := by
  have hmeasure : (simplexPMF mu).toMeasure = (simplexPMF nu).toMeasure := by
    unfold lawTV FiniteProbabilityRow.tvDist at hzero
    exact UEOT.V3.InformationZeroTV.measure_eq_of_tvDist_eq_zero _ _ hzero
  have hpmf : simplexPMF mu = simplexPMF nu := PMF.toMeasure_injective hmeasure
  apply Subtype.ext
  funext x
  have hx := congrArg (fun p : PMF S => (p x).toReal) hpmf
  simpa using hx

/-- Same-input perturbation: a uniform row-TV error bounds the one-step law error. -/
theorem tv_step_cross_le
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (mu : stdSimplex ℝ S) (epsilon : ℝ)
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    lawTV (step P hP mu) (step Q hQ mu) ≤ epsilon := by
  unfold lawTV FiniteProbabilityRow.tvDist
  change UEOT.V3.TotalVariation.tvDist
      (simplexPMF (step P hP mu)).toMeasure
      (simplexPMF (step Q hQ mu)).toMeasure ≤ epsilon
  unfold UEOT.V3.TotalVariation.tvDist
  refine csSup_le
    (UEOT.V3.TotalVariation.tvEventSet_nonempty
      (simplexPMF (step P hP mu)).toMeasure
      (simplexPMF (step Q hQ mu)).toMeasure) ?_
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  rw [simplexPMF_step_eq_bind, simplexPMF_step_eq_bind]
  rw [bind_measureReal_eq_integral, bind_measureReal_eq_integral]
  let gP : S → ℝ := fun x => (rowPMF P hP x).toMeasure.real A
  let gQ : S → ℝ := fun x => (rowPMF Q hQ x).toMeasure.real A
  have hPint : Integrable gP (simplexPMF mu).toMeasure := Integrable.of_finite
  have hQint : Integrable gQ (simplexPMF mu).toMeasure := Integrable.of_finite
  have hnorm : ‖∫ x, (gP x - gQ x) ∂(simplexPMF mu).toMeasure‖ ≤ epsilon := by
    have hbound := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (simplexPMF mu).toMeasure)
      (f := fun x => gP x - gQ x) (C := epsilon) <| by
        filter_upwards with x
        have htv := UEOT.V3.TotalVariation.tvEvent_le
          (rowPMF P hP x).toMeasure (rowPMF Q hQ x).toMeasure A hA
        have hcross : UEOT.V3.TotalVariation.tvDist
            (rowPMF P hP x).toMeasure (rowPMF Q hQ x).toMeasure =
            crossRowTV P hP Q hQ x := by rfl
        rw [hcross] at htv
        have hx := htv.trans (hrow x)
        simpa [gP, gQ, Real.norm_eq_abs] using hx
    simpa using hbound
  have hint :
      (∫ x, (gP x - gQ x) ∂(simplexPMF mu).toMeasure) =
        (∫ x, gP x ∂(simplexPMF mu).toMeasure) -
          ∫ x, gQ x ∂(simplexPMF mu).toMeasure := by
    exact integral_sub hPint hQint
  rw [hint, Real.norm_eq_abs] at hnorm
  simpa [gP, gQ] using hnorm

section Nonempty

variable [Nonempty S]

/-- Literal finite Dobrushin coefficient `max_{x,x'} D_TV(P_x,P_x')`. -/
noncomputable def dobrushinAlpha
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S) : ℝ :=
  Finset.univ.sup'
    (Finset.univ_nonempty : (Finset.univ : Finset (S × S)).Nonempty)
    (fun z : S × S => rowTV P hP z.1 z.2)

theorem rowTV_le_dobrushinAlpha
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S) (x x' : S) :
    rowTV P hP x x' ≤ dobrushinAlpha P hP := by
  let f : S × S → ℝ := fun z => rowTV P hP z.1 z.2
  have hle : f (x, x') ≤ Finset.univ.sup'
      (Finset.univ_nonempty : (Finset.univ : Finset (S × S)).Nonempty) f := by
    exact Finset.le_sup' f (by simp)
  exact hle

theorem eventRow_pairwise_abs_le_dobrushinAlpha
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (A : Set S) (x x' : S) :
    |(rowPMF P hP x).toMeasure.real A - (rowPMF P hP x').toMeasure.real A| ≤
      dobrushinAlpha P hP := by
  have htv := UEOT.V3.TotalVariation.tvEvent_le
    (rowPMF P hP x).toMeasure (rowPMF P hP x').toMeasure A MeasurableSet.of_discrete
  have hrow : UEOT.V3.TotalVariation.tvDist
      (rowPMF P hP x).toMeasure (rowPMF P hP x').toMeasure = rowTV P hP x x' := by
    rfl
  rw [hrow] at htv
  exact htv.trans (rowTV_le_dobrushinAlpha P hP x x')

theorem eventRow_span_le_dobrushinAlpha
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S) (A : Set S) :
    UEOT.V3.TVSpan.span (fun x => (rowPMF P hP x).toMeasure.real A) ≤
      dobrushinAlpha P hP := by
  let g : S → ℝ := fun x => (rowPMF P hP x).toMeasure.real A
  have hfin : (Set.range g).Finite := Set.toFinite _
  have hne : (Set.range g).Nonempty := Set.range_nonempty g
  have hsupmem := hne.csSup_mem hfin
  have hinfmem := hne.csInf_mem hfin
  rcases hsupmem with ⟨xhi, hxhi⟩
  rcases hinfmem with ⟨xlo, hxlo⟩
  unfold UEOT.V3.TVSpan.span
  rw [← hxhi, ← hxlo]
  calc
    g xhi - g xlo ≤ |g xhi - g xlo| := le_abs_self _
    _ ≤ dobrushinAlpha P hP :=
      eventRow_pairwise_abs_le_dobrushinAlpha P hP A xhi xlo

/-- Standard finite-kernel Dobrushin contraction with the exact source coefficient. -/
theorem tv_step_le_dobrushin
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (mu nu : stdSimplex ℝ S) :
    lawTV (step P hP mu) (step P hP nu) ≤
      dobrushinAlpha P hP * lawTV mu nu := by
  unfold lawTV FiniteProbabilityRow.tvDist
  change UEOT.V3.TotalVariation.tvDist
      (simplexPMF (step P hP mu)).toMeasure
      (simplexPMF (step P hP nu)).toMeasure ≤
    dobrushinAlpha P hP * UEOT.V3.TotalVariation.tvDist
      (simplexPMF mu).toMeasure (simplexPMF nu).toMeasure
  unfold UEOT.V3.TotalVariation.tvDist
  refine csSup_le
    (UEOT.V3.TotalVariation.tvEventSet_nonempty
      (simplexPMF (step P hP mu)).toMeasure
      (simplexPMF (step P hP nu)).toMeasure) ?_
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  rw [simplexPMF_step_eq_bind, simplexPMF_step_eq_bind]
  rw [bind_measureReal_eq_integral, bind_measureReal_eq_integral]
  let g : S → ℝ := fun x => (rowPMF P hP x).toMeasure.real A
  have hspan := UEOT.V3.TVSpan.abs_integral_sub_le_span
    (simplexPMF mu).toMeasure (simplexPMF nu).toMeasure g
    Measurable.of_discrete (Finite.bddBelow_range g) (Finite.bddAbove_range g)
  have htv0 := UEOT.V3.TotalVariation.tvDist_nonneg
    (simplexPMF mu).toMeasure (simplexPMF nu).toMeasure
  calc
    |∫ x, (rowPMF P hP x).toMeasure.real A ∂(simplexPMF mu).toMeasure -
        ∫ x, (rowPMF P hP x).toMeasure.real A ∂(simplexPMF nu).toMeasure| ≤
      UEOT.V3.TVSpan.span g *
        UEOT.V3.TotalVariation.tvDist
          (simplexPMF mu).toMeasure (simplexPMF nu).toMeasure := by
            simpa [g] using hspan
    _ ≤ dobrushinAlpha P hP *
        UEOT.V3.TotalVariation.tvDist
          (simplexPMF mu).toMeasure (simplexPMF nu).toMeasure :=
      mul_le_mul_of_nonneg_right (eventRow_span_le_dobrushinAlpha P hP A) htv0

theorem invariant_eq_of_dobrushin_lt_one
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (halpha : dobrushinAlpha P hP < 1)
    (mu nu : stdSimplex ℝ S)
    (hmu : step P hP mu = mu) (hnu : step P hP nu = nu) : mu = nu := by
  have hc := tv_step_le_dobrushin P hP mu nu
  rw [hmu, hnu] at hc
  have hd0 := lawTV_nonneg mu nu
  have hz : lawTV mu nu = 0 := by
    nlinarith
  exact lawTV_eq_zero_imp_eq mu nu hz

/-- A simplex vertex used only to seed the P-GOA-01 existence theorem. -/
noncomputable def pureSimplex (x0 : S) : stdSimplex ℝ S :=
  ⟨Pi.single x0 1, single_mem_stdSimplex ℝ x0⟩

theorem exists_invariant
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S) :
    ∃ mu : stdSimplex ℝ S, step P hP mu = mu := by
  let x0 : S := Classical.choice inferInstance
  let mu0 : stdSimplex ℝ S := pureSimplex x0
  have hgoa := UEOT.V3.FiniteCesaroInvariant.p_goa_01 P hP mu0
  rcases hgoa.1 with ⟨nu, phi, hphi, hlim⟩
  refine ⟨nu, ?_⟩
  have hinv := hgoa.2 nu phi hphi hlim
  apply Subtype.ext
  exact hinv

theorem existsUnique_invariant
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (halpha : dobrushinAlpha P hP < 1) :
    ∃! mu : stdSimplex ℝ S, step P hP mu = mu := by
  rcases exists_invariant P hP with ⟨mu, hmu⟩
  refine ⟨mu, hmu, ?_⟩
  intro nu hnu
  exact invariant_eq_of_dobrushin_lt_one P hP halpha nu mu hnu hmu

/-- Frozen stationary perturbation bound with the baseline coefficient `alpha(P)`. -/
theorem stationary_perturbation
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (halpha : dobrushinAlpha P hP < 1)
    (mu muhat : stdSimplex ℝ S)
    (hmu : step P hP mu = mu)
    (hmuhat : step Q hQ muhat = muhat)
    (epsilon : ℝ)
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    lawTV mu muhat ≤ epsilon / (1 - dobrushinAlpha P hP) := by
  have htri := lawTV_triangle mu (step P hP muhat) muhat
  have hcontract := tv_step_le_dobrushin P hP mu muhat
  rw [hmu] at hcontract
  have hkernel := tv_step_cross_le P hP Q hQ muhat epsilon hrow
  rw [hmuhat] at hkernel
  have hd : lawTV mu muhat ≤ dobrushinAlpha P hP * lawTV mu muhat + epsilon := by
    linarith
  have hden : 0 < 1 - dobrushinAlpha P hP := sub_pos.mpr halpha
  rw [le_div_iff₀ hden]
  nlinarith

/-- **P-GOA-02.** Exact finite Dobrushin uniqueness and stationary perturbation
bound from frozen §21.3.  Existence in the unique-invariant clause is supplied by
P-GOA-01, not assumed. -/
theorem p_goa_02
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (halpha : dobrushinAlpha P hP < 1) :
    (∃! mu : stdSimplex ℝ S, step P hP mu = mu) ∧
      ∀ (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
        (mu muhat : stdSimplex ℝ S) (epsilon : ℝ),
        step P hP mu = mu →
        step Q hQ muhat = muhat →
        (∀ x, crossRowTV P hP Q hQ x ≤ epsilon) →
        lawTV mu muhat ≤ epsilon / (1 - dobrushinAlpha P hP) := by
  constructor
  · exact existsUnique_invariant P hP halpha
  · intro Q hQ mu muhat epsilon hmu hmuhat hrow
    exact stationary_perturbation P hP Q hQ halpha mu muhat hmu hmuhat epsilon hrow

end Nonempty

end

end UEOT.V3.FiniteDobrushin
