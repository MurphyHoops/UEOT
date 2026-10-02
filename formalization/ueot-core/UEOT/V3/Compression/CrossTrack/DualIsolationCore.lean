import UEOT.V3.Compression.CrossTrack.ParentBindingStatic

/-!
# Dual Isolation Theory — binding identifiability × semantic isolation

Track S supplies a semantic isolation margin for long-run invariant semantics.
Parent Binding supplies a forward realization bound from assembly distance to
parent-kernel distance.  The missing inverse leg is a lower-gain certificate
for the diagnostic map that identifies richer parent assemblies from lower-
level evidence.

The two positive margins are deliberately kept distinct:

* `beta` — binding / assembly identifiability;
* `kappa` — long-run semantic isolation.

The first controls inversion of the observation/diagnostic map.  The second
controls inversion of the stationary residual equation.
-/

namespace UEOT.V3.Compression.CrossTrack

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe uP uC uA uY uS

noncomputable section

variable {P : Type uP} {C : Type uC}
variable {A : Type uA} {Y : Type uY}
variable [MetricSpace A] [PseudoMetricSpace Y]
variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance dualIsolationDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- A positive lower-gain certificate for a parent-assembly diagnostic.

`beta * d_A(a,b) <= d_Y(D a,D b)` says that distinct assemblies cannot be
arbitrarily collapsed by the lower-level diagnostic.  No dynamics, invariant
law, objective, or long-run conclusion is part of this certificate. -/
structure BindingIsolation (diagnostic : A → Y) (beta : ℝ) : Prop where
  beta_pos : 0 < beta
  lower : ∀ a b,
    beta * dist a b ≤ dist (diagnostic a) (diagnostic b)

/-- Positive binding isolation implies exact diagnostic identifiability. -/
theorem BindingIsolation.injective
    (diagnostic : A → Y) (beta : ℝ)
    (hiso : BindingIsolation diagnostic beta) :
    Function.Injective diagnostic := by
  intro a b hab
  have hlower := hiso.lower a b
  rw [hab, dist_self] at hlower
  have hdist0 : dist a b = 0 := by
    by_contra hne
    have hdistPos : 0 < dist a b := lt_of_le_of_ne dist_nonneg (Ne.symm hne)
    have hmulPos : 0 < beta * dist a b := mul_pos hiso.beta_pos hdistPos
    exact (not_lt_of_ge hlower) hmulPos
  exact dist_eq_zero.mp hdist0

/-- One noisy diagnostic ball of radius `eta` has assembly diameter at most
`2 * eta / beta` under positive binding isolation. -/
theorem assemblyDist_le_two_mul_error_div_bindingIsolation
    (diagnostic : A → Y) (beta eta : ℝ)
    (hiso : BindingIsolation diagnostic beta)
    (y : Y) {a b : A}
    (ha : dist (diagnostic a) y ≤ eta)
    (hb : dist (diagnostic b) y ≤ eta) :
    dist a b ≤ 2 * eta / beta := by
  have hdiag : dist (diagnostic a) (diagnostic b) ≤ 2 * eta := by
    calc
      dist (diagnostic a) (diagnostic b)
          ≤ dist (diagnostic a) y + dist y (diagnostic b) :=
        dist_triangle _ _ _
      _ = dist (diagnostic a) y + dist (diagnostic b) y := by
        rw [dist_comm y]
      _ ≤ eta + eta := add_le_add ha hb
      _ = 2 * eta := by ring
  have hlower := (hiso.lower a b).trans hdiag
  apply (le_div_iff₀ hiso.beta_pos).2
  simpa [mul_comm] using hlower

/-- Pairwise dual-isolation bound.

Lower-level diagnostic uncertainty is first inverted through `beta`, then
transported through parent-dynamics sensitivity `L`, and finally inverted
through the Track-S semantic isolation margin `kappa`. -/
theorem dualIsolation_pairwiseSemanticBound
    (repr : P → A)
    (diagnostic : A → Y)
    (beta eta : ℝ)
    (hiso : BindingIsolation diagnostic beta)
    (heta : 0 ≤ eta)
    (observed : Y)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (bind : ParentBindingLipschitz repr K hK)
    (mu : P → stdSimplex ℝ S)
    (hmu : ∀ p, mu p ∈ invariantLawSet (K p) (hK p))
    (kappaMin : ℝ)
    (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    {p q : P}
    (hpObs : dist (diagnostic (repr p)) observed ≤ eta)
    (hqObs : dist (diagnostic (repr q)) observed ≤ eta)
    (hpIso : kappaMin ≤ l1ResidualConorm (K p)) :
    lawTV (mu p) (mu q) ≤
      bind.L * (2 * eta / beta) / kappaMin := by
  have hassembly : dist (repr p) (repr q) ≤ 2 * eta / beta :=
    assemblyDist_le_two_mul_error_div_bindingIsolation
      diagnostic beta eta hiso observed hpObs hqObs
  have hrow : ∀ x,
      crossRowTV (K p) (hK p) (K q) (hK q) x ≤
        bind.L * (2 * eta / beta) := by
    intro x
    calc
      crossRowTV (K p) (hK p) (K q) (hK q) x
          ≤ bind.L * dist (repr p) (repr q) :=
        bind.row_lipschitz p q x
      _ ≤ bind.L * (2 * eta / beta) :=
        mul_le_mul_of_nonneg_left hassembly bind.L_nonneg
  have hsource : 0 < l1ResidualConorm (K p) :=
    lt_of_lt_of_le hkappaMin hpIso
  have htrack := suppliedInvariant_tracking
    (K p) (hK p) (K q) (hK q)
    (mu p) (mu q) (hmu p) (hmu q)
    (bind.L * (2 * eta / beta)) hcard hsource hrow
  have hdelta0 : 0 ≤ 2 * eta / beta :=
    div_nonneg (mul_nonneg (by norm_num) heta) hiso.beta_pos.le
  have hnum0 : 0 ≤ bind.L * (2 * eta / beta) :=
    mul_nonneg bind.L_nonneg hdelta0
  exact htrack.trans
    (div_le_div_of_nonneg_left hnum0 hkappaMin hpIso)

/-- Fibre-wide dual-isolation theorem.

Every richer parent completion in the child fibre is required only to lie in
one diagnostic ball of radius `eta`.  Positive binding isolation turns that
ball into an assembly-diameter bound, after which Parent Binding + Track S
yield the semantic diameter bound. -/
theorem dualIsolation_fiberSemanticDiameter
    (pi : P → C)
    (repr : P → A)
    (diagnostic : A → Y)
    (beta eta : ℝ)
    (hiso : BindingIsolation diagnostic beta)
    (heta : 0 ≤ eta)
    (observed : Y)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (bind : ParentBindingLipschitz repr K hK)
    (mu : P → stdSimplex ℝ S)
    (hmu : ∀ p, mu p ∈ invariantLawSet (K p) (hK p))
    (c : C)
    (hfiberNonempty : ∃ p, pi p = c)
    (kappaMin : ℝ)
    (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hobs : ∀ p, pi p = c →
      dist (diagnostic (repr p)) observed ≤ eta)
    (hisolationFloor : ∀ p, pi p = c →
      kappaMin ≤ l1ResidualConorm (K p)) :
    fiberSemanticDiameter pi mu c ≤
      bind.L * (2 * eta / beta) / kappaMin := by
  apply parentSemanticDiameter_of_binding
      pi repr K hK bind mu hmu c hfiberNonempty
      (2 * eta / beta) kappaMin
  · exact div_nonneg (mul_nonneg (by norm_num) heta) hiso.beta_pos.le
  · exact hkappaMin
  · exact hcard
  · intro p q hp hq
    exact assemblyDist_le_two_mul_error_div_bindingIsolation
      diagnostic beta eta hiso observed (hobs p hp) (hobs q hq)
  · exact hisolationFloor

/-- The same bound in the symmetric "two inverse margins" form.

`2 * L * eta / (beta * kappa)` makes the two positive isolation margins
visible in one denominator. -/
theorem dualIsolation_fiberSemanticDiameter_normalized
    (pi : P → C)
    (repr : P → A)
    (diagnostic : A → Y)
    (beta eta : ℝ)
    (hiso : BindingIsolation diagnostic beta)
    (heta : 0 ≤ eta)
    (observed : Y)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (bind : ParentBindingLipschitz repr K hK)
    (mu : P → stdSimplex ℝ S)
    (hmu : ∀ p, mu p ∈ invariantLawSet (K p) (hK p))
    (c : C)
    (hfiberNonempty : ∃ p, pi p = c)
    (kappaMin : ℝ)
    (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hobs : ∀ p, pi p = c →
      dist (diagnostic (repr p)) observed ≤ eta)
    (hisolationFloor : ∀ p, pi p = c →
      kappaMin ≤ l1ResidualConorm (K p)) :
    fiberSemanticDiameter pi mu c ≤
      (2 * bind.L * eta) / (beta * kappaMin) := by
  have h := dualIsolation_fiberSemanticDiameter
    pi repr diagnostic beta eta hiso heta observed K hK bind mu hmu
    c hfiberNonempty kappaMin hkappaMin hcard hobs hisolationFloor
  convert h using 1
  field_simp [ne_of_gt hiso.beta_pos, ne_of_gt hkappaMin]

end

end UEOT.V3.Compression.CrossTrack
