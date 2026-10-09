import UEOT.V3.DualDriveGauge
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCJoint2DRejection
import Mathlib.Tactic

/-!
# UMC-04 — exact scalar dual-drive gauge *completeness*

The existing P-DDH-01 proves that a joint pi/phi gauge transform preserves
Pi - lambda Phi. The NEW converse below proves that, for fixed lambda,
any two pointwise decompositions of the exact same scalar objective
are gauge related. Thus the observable scalar identifies precisely the
gauge orbit, not the two physical drives. This result does NOT prove
physical dual-drive ontology or the C5 common-two-dimensional mechanism.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.DualDriveGauge

universe uX

/-- The scalar objective J(x) constructed from the two drives. -/
def driveObjective {X : Type uX} (piVal phiVal : X → ℝ)
    (lambda : ℝ) (x : X) : ℝ :=
  piVal x - lambda * phiVal x

/-- Exact classification: two decompositions represent the same scalar
function if and only if they differ by the P-DDH-01 gauge field chi.
The converse is new relative to the original one-way invariance theorem. -/
theorem same_objective_iff_gauge_related
    {X : Type uX}
    (pi phi pi' phi' : X → ℝ) (lambda : ℝ) :
    driveObjective pi phi lambda = driveObjective pi' phi' lambda ↔
    ∃ chi : X → ℝ,
      (∀ x, pi' x = pi x + lambda * chi x) ∧
      (∀ x, phi' x = phi x + chi x) := by
  constructor
  · intro h
    refine ⟨fun x => phi' x - phi x, ?_, ?_⟩
    · intro x
      have hx := congrFun h x
      dsimp [driveObjective] at hx
      linarith
    · intro x
      ring
  · rintro ⟨chi, hpi, hphi⟩
    funext x
    have h := p_ddh_01_pointwise pi phi chi lambda x
    dsimp [driveObjective]
    rw [hpi x, hphi x]
    exact h.symm

/-- If one independently anchors the phi coordinate then the measured
objective determines pi uniquely: an explicit identifiability premise. -/
theorem pi_identified_of_phi_anchor
    {X : Type uX} (pi phi pi' phi' : X → ℝ) (lambda : ℝ)
    (hJ : driveObjective pi phi lambda = driveObjective pi' phi' lambda)
    (hphi : phi = phi') : pi = pi' := by
  funext x
  have h := congrFun hJ x
  have hanchor := congrFun hphi x
  dsimp [driveObjective] at h
  rw [hanchor] at h
  linarith

/-- Under nonzero lambda, independent anchoring of pi also identifies
phi. With lambda = 0 the observable J ignores phi entirely. -/
theorem phi_identified_of_pi_anchor
    {X : Type uX} (pi phi pi' phi' : X → ℝ) (lambda : ℝ)
    (hlambda : lambda ≠ 0)
    (hJ : driveObjective pi phi lambda = driveObjective pi' phi' lambda)
    (hpi : pi = pi') : phi = phi' := by
  funext x
  have h := congrFun hJ x
  have hanchor := congrFun hpi x
  dsimp [driveObjective] at h
  have hmul : lambda * (phi x - phi' x) = 0 := by linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hlambda)

/-- Non-vacuous exact negative control: the same observable drive J
admits two distinct pi/phi decompositions at lambda = 1. -/
theorem unanchored_drive_is_not_uniquely_identified :
    ∃ (pi phi pi' phi' : PUnit → ℝ),
      driveObjective pi phi 1 = driveObjective pi' phi' 1 ∧
      pi ≠ pi' ∧ phi ≠ phi' := by
  refine ⟨(fun _ => 0), (fun _ => 0),
    (fun _ => 1), (fun _ => 1), ?_, ?_, ?_⟩
  · funext x
    cases x
    norm_num [driveObjective]
  · intro h
    have hx := congrFun h PUnit.unit
    norm_num at hx
  · intro h
    have hx := congrFun h PUnit.unit
    norm_num at hx

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
