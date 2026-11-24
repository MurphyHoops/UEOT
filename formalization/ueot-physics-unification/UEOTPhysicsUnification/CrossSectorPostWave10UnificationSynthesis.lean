import UEOTPhysicsUnification.UnifiedCausalChiralUnimodularSynthesis
import UEOTPhysicsUnification.Nonperturbative4DMeasureLimitH1d4
import UEOTPhysicsUnification.ConformalControlGravityGates
import UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2
import UEOTPhysicsUnification.DimensionlessCouplingsFlavorAndVacuumWindowH3
import UEOTPhysicsUnification.BellCHSHAndBlindHoldoutContractH4
import Mathlib.Tactic

/-!
# Wave 11 Cross-Sector Synthesis (`SYNTH-11` / `SPEC-20261124-06` / `C-UNIFIED-SYNTH-11`)

Unites Wave 7/10 `UnifiedCausalChiralUnimodularSynthesis` (`UnifiedCoupledSystem`),
Wave 10 `H1` operational closure (`Nonperturbative4DMeasureLimitH1d4`),
`ConformalControlGravityGates` (§1–§4), and Wave 11 `M1` (`H2`), `M2` (`H3`), `M3` (`H4`)
into a single non-fragmented pure-kernel synthesis while proving 4-way logical independence
across the four remaining irreducible open frontiers:

1. `H1d4d_NonPolynomial4DMeasureDecoupling` (exact 4D non-polynomial decoupling proof),
2. `H2d_Clay4DYangMillsContinuumMeasure` (4D continuum chiral Yang–Mills existence & mass gap),
3. `H3d_ExactAPrioriDimensionlessConstants` (exact a priori derivation of `(I_Λ^*, α_i, y_f)`),
4. `H4d_RawHardwareBlindHoldoutExecution` (raw hardware blind-holdout shot execution).

## Pure-Kernel Guarantee
Axioms strictly `⊆ {propext, Classical.choice, Quot.sound}`; `0 sorryAx`; `0 native_decide`;
`0` custom `axiom` or `opaque`; `"physical_unification": "OPEN"` and `deviceCertified = false`
remain strictly preserved.
-/

namespace UEOTPhysicsUnification.CrossSectorPostWave10UnificationSynthesis

open Function Matrix Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

abbrev H1d4Sub := Nonperturbative4DMeasureLimitH1d4.H1d4SubHypothesis
abbrev H1d4Cand := Nonperturbative4DMeasureLimitH1d4.H1d4LayerCandidate
abbrev H2Sub := NonAbelianLatticeMassGapAndChiralIntegrabilityH2.H2SubHypothesis
abbrev H2Cand := NonAbelianLatticeMassGapAndChiralIntegrabilityH2.H2LayerCandidate
abbrev H3Sub := DimensionlessCouplingsFlavorAndVacuumWindowH3.H3SubHypothesis
abbrev H3Cand := DimensionlessCouplingsFlavorAndVacuumWindowH3.H3LayerCandidate
abbrev H4Sub := BellCHSHAndBlindHoldoutContractH4.H4SubHypothesis
abbrev H4Cand := BellCHSHAndBlindHoldoutContractH4.H4LayerCandidate

/-! ## 1. Four Irreducible Post-Wave-10 Open Frontiers & Honest Governance -/

/-- The four remaining irreducible open frontiers after operational closure of `H1a–H1d4c`,
`H2a–H2c`, `H3a–H3c`, and `H4a–H4c`. -/
inductive PostWave10OpenFrontier : Type
  | H1d4d_NonPolynomial4DMeasureDecoupling
  | H2d_Clay4DYangMillsContinuumMeasure
  | H3d_ExactAPrioriDimensionlessConstants
  | H4d_RawHardwareBlindHoldoutExecution
  deriving DecidableEq, Repr

instance : Fintype PostWave10OpenFrontier where
  elems := {
    .H1d4d_NonPolynomial4DMeasureDecoupling,
    .H2d_Clay4DYangMillsContinuumMeasure,
    .H3d_ExactAPrioriDimensionlessConstants,
    .H4d_RawHardwareBlindHoldoutExecution
  }
  complete h := by cases h <;> decide

/-- Combined cross-sector layer state across `H1d4`, `H2`, `H3`, and `H4`. -/
structure PostWave10UnificationState where
  h1 : H1d4Cand
  h2 : H2Cand
  h3 : H3Cand
  h4 : H4Cand

/-- Joint operational closure of all twelve sub-frontiers (`H1d4a–c`, `H2a–c`, `H3a–c`, `H4a–c`). -/
def PostWave10UnificationState.OperationalSubClosuresHold
    (S : PostWave10UnificationState) : Prop :=
  (S.h1.Satisfies .H1d4a_WeightedBanachInfiniteTruncationConvergence ∧
    S.h1.Satisfies .H1d4b_OSWeakLimitGNSReconstructionAndNonTriviality ∧
    S.h1.Satisfies .H1d4c_OperationalHorizonUVScreeningEquivalence) ∧
  (S.h2.Satisfies .h2a_perturbative_overlap ∧
    S.h2.Satisfies .h2b_strong_coupling_dobrushin ∧
    S.h2.Satisfies .h2c_ah01_lattice_uv_screening) ∧
  (S.h3.Satisfies .h3a_unit_unimodular_reduction ∧
    S.h3.Satisfies .h3b_eft_flavor_viability_windows ∧
    S.h3.Satisfies .h3c_horizon_indistinguishability) ∧
  (S.h4.Satisfies .h4a_chsh_tsirelson_and_witness_thresholds ∧
    S.h4.Satisfies .h4b_nonselective_multicell_holdout_soundness ∧
    S.h4.Satisfies .h4c_calibration_power_and_portfolio_contracts)

/-- Satisfaction predicate for each of the four remaining open frontiers. -/
def PostWave10UnificationState.SatisfiesOpenFrontier
    (S : PostWave10UnificationState) : PostWave10OpenFrontier → Prop
  | .H1d4d_NonPolynomial4DMeasureDecoupling =>
      S.h1.Satisfies .H1d4d_UnconditionalExact4DNonPolynomialDecouplingProof
  | .H2d_Clay4DYangMillsContinuumMeasure =>
      S.h2.Satisfies .h2d_clay_4d_continuum_measure
  | .H3d_ExactAPrioriDimensionlessConstants =>
      S.h3.Satisfies .h3d_exact_apriori_constants_selection
  | .H4d_RawHardwareBlindHoldoutExecution =>
      S.h4.Satisfies .h4d_raw_hardware_shot_execution

/-- Full unconditional post-Wave-10 physical unification requires simultaneous closure of all
four sectors (`H1d4`, `H2`, `H3`, `H4`). -/
def PostWave10UnificationState.FullPostWave10Unification
    (S : PostWave10UnificationState) : Prop :=
  S.h1.FullH1d4Closure ∧ S.h2.FullH2Closure ∧ S.h3.FullH3Closure ∧ S.h4.FullH4Closure

/-- Actual Wave 11 repository constructive witness: all twelve operational sublayers closed,
all four open frontiers `(H1d4d, H2d, H3d, H4d)` honestly open. -/
def currentWave11RepoState : PostWave10UnificationState where
  h1 := Nonperturbative4DMeasureLimitH1d4.wave10H1d4ConstructiveWitness
  h2 := NonAbelianLatticeMassGapAndChiralIntegrabilityH2.wave11H2ConstructiveWitness
  h3 := DimensionlessCouplingsFlavorAndVacuumWindowH3.wave11H3ConstructiveWitness
  h4 := BellCHSHAndBlindHoldoutContractH4.wave11H4ConstructiveWitness

/-- **Wave 11 Frontier Governance & 4-Way Logical Independence Theorem**:
1. Exactly `4` irreducible open frontiers remain post-Wave-10 / post-`M1..M3`;
2. `currentWave11RepoState` closes all `12` operational sublayers while refuting all `4` open frontiers;
3. Whenever operational subclosures hold, `FullPostWave10Unification ↔ ∀ f, SatisfiesOpenFrontier f`;
4. Each of the `4` open frontiers is strictly logically independent of the other `3` plus all
   `12` operational subclosures;
5. Absent complete raw hardware shots, `deviceCertified sub = false` and
   `physicalUnificationStatus = .OPEN`. -/
theorem post_wave10_frontier_status_and_honest_open_governance :
    Fintype.card PostWave10OpenFrontier = 4 ∧
    (currentWave11RepoState.OperationalSubClosuresHold ∧
      ∀ f : PostWave10OpenFrontier, ¬ currentWave11RepoState.SatisfiesOpenFrontier f) ∧
    (∀ S : PostWave10UnificationState,
      S.OperationalSubClosuresHold →
      (S.FullPostWave10Unification ↔ ∀ f : PostWave10OpenFrontier, S.SatisfiesOpenFrontier f)) ∧
    (∀ f : PostWave10OpenFrontier,
      ∃ S : PostWave10UnificationState,
        S.OperationalSubClosuresHold ∧
        (∀ f' : PostWave10OpenFrontier, f' ≠ f → S.SatisfiesOpenFrontier f') ∧
        ¬ S.SatisfiesOpenFrontier f) ∧
    (∀ sub : MesoscopicDecoherenceGravimetry.PreRegisteredHardwareSubmission,
      sub.rawShotsComplete = false →
      MesoscopicDecoherenceGravimetry.deviceCertified sub = false ∧
      MathV42ClosedTestsAndMechanismBridge.physicalUnificationStatus
        (Fintype.card PostWave10OpenFrontier)
        (MesoscopicDecoherenceGravimetry.deviceCertified sub) = .OPEN) ∧
    MathV42ClosedTestsAndMechanismBridge.physicalUnificationStatus
      (Fintype.card PostWave10OpenFrontier) false = .OPEN := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, by decide⟩
  · refine ⟨⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩, ?_⟩
    intro f
    cases f <;> simp [currentWave11RepoState, PostWave10UnificationState.SatisfiesOpenFrontier,
      Nonperturbative4DMeasureLimitH1d4.wave10H1d4ConstructiveWitness,
      Nonperturbative4DMeasureLimitH1d4.H1d4LayerCandidate.Satisfies,
      NonAbelianLatticeMassGapAndChiralIntegrabilityH2.wave11H2ConstructiveWitness,
      NonAbelianLatticeMassGapAndChiralIntegrabilityH2.H2LayerCandidate.Satisfies,
      DimensionlessCouplingsFlavorAndVacuumWindowH3.wave11H3ConstructiveWitness,
      DimensionlessCouplingsFlavorAndVacuumWindowH3.H3LayerCandidate.Satisfies,
      BellCHSHAndBlindHoldoutContractH4.wave11H4ConstructiveWitness,
      BellCHSHAndBlindHoldoutContractH4.H4LayerCandidate.Satisfies]
  · intro S hOp
    rcases hOp with ⟨⟨h1a, h1b, h1c⟩, ⟨h2a, h2b, h2c⟩, ⟨h3a, h3b, h3c⟩, ⟨h4a, h4b, h4c⟩⟩
    dsimp [Nonperturbative4DMeasureLimitH1d4.H1d4LayerCandidate.Satisfies,
      NonAbelianLatticeMassGapAndChiralIntegrabilityH2.H2LayerCandidate.Satisfies,
      DimensionlessCouplingsFlavorAndVacuumWindowH3.H3LayerCandidate.Satisfies,
      BellCHSHAndBlindHoldoutContractH4.H4LayerCandidate.Satisfies] at h1a h1b h1c h2a h2b h2c h3a h3b h3c h4a h4b h4c
    constructor
    · rintro ⟨h1f, h2f, h3f, h4f⟩ f
      cases f
      · exact h1f.2.2.2
      · exact h2f.2.2.2
      · exact h3f.2.2.2
      · exact h4f.2.2.2
    · intro hall
      have h1d : S.h1.nonPolynomialDecouplingDefect = 0 :=
        hall .H1d4d_NonPolynomial4DMeasureDecoupling
      have h2d : S.h2.clay4DContinuumMeasureDefect = 0 :=
        hall .H2d_Clay4DYangMillsContinuumMeasure
      have h3d : S.h3.exactAprioriSelectionDefect = 0 :=
        hall .H3d_ExactAPrioriDimensionlessConstants
      have h4d : S.h4.rawHardwareShotDefect = 0 :=
        hall .H4d_RawHardwareBlindHoldoutExecution
      exact ⟨⟨h1a, h1b, h1c, h1d⟩, ⟨h2a, h2b, h2c, h2d⟩, ⟨h3a, h3b, h3c, h3d⟩, ⟨h4a, h4b, h4c, h4d⟩⟩
  · intro f
    cases f with
    | H1d4d_NonPolynomial4DMeasureDecoupling =>
      refine ⟨⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩,
        ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩, ?_, ?_⟩
      · intro f' hne
        cases f' with
        | H1d4d_NonPolynomial4DMeasureDecoupling => exact absurd rfl hne
        | H2d_Clay4DYangMillsContinuumMeasure => rfl
        | H3d_ExactAPrioriDimensionlessConstants => rfl
        | H4d_RawHardwareBlindHoldoutExecution => rfl
      · simp [PostWave10UnificationState.SatisfiesOpenFrontier,
          Nonperturbative4DMeasureLimitH1d4.H1d4LayerCandidate.Satisfies]
    | H2d_Clay4DYangMillsContinuumMeasure =>
      refine ⟨⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩,
        ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩, ?_, ?_⟩
      · intro f' hne
        cases f' with
        | H1d4d_NonPolynomial4DMeasureDecoupling => rfl
        | H2d_Clay4DYangMillsContinuumMeasure => exact absurd rfl hne
        | H3d_ExactAPrioriDimensionlessConstants => rfl
        | H4d_RawHardwareBlindHoldoutExecution => rfl
      · simp [PostWave10UnificationState.SatisfiesOpenFrontier,
          NonAbelianLatticeMassGapAndChiralIntegrabilityH2.H2LayerCandidate.Satisfies]
    | H3d_ExactAPrioriDimensionlessConstants =>
      refine ⟨⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩,
        ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩, ?_, ?_⟩
      · intro f' hne
        cases f' with
        | H1d4d_NonPolynomial4DMeasureDecoupling => rfl
        | H2d_Clay4DYangMillsContinuumMeasure => rfl
        | H3d_ExactAPrioriDimensionlessConstants => exact absurd rfl hne
        | H4d_RawHardwareBlindHoldoutExecution => rfl
      · simp [PostWave10UnificationState.SatisfiesOpenFrontier,
          DimensionlessCouplingsFlavorAndVacuumWindowH3.H3LayerCandidate.Satisfies]
    | H4d_RawHardwareBlindHoldoutExecution =>
      refine ⟨⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩⟩,
        ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩, ?_, ?_⟩
      · intro f' hne
        cases f' with
        | H1d4d_NonPolynomial4DMeasureDecoupling => rfl
        | H2d_Clay4DYangMillsContinuumMeasure => rfl
        | H3d_ExactAPrioriDimensionlessConstants => rfl
        | H4d_RawHardwareBlindHoldoutExecution => exact absurd rfl hne
      · simp [PostWave10UnificationState.SatisfiesOpenFrontier,
          BellCHSHAndBlindHoldoutContractH4.H4LayerCandidate.Satisfies]
  · intro sub hraw
    have hcert : MesoscopicDecoherenceGravimetry.deviceCertified sub = false :=
      (MesoscopicDecoherenceGravimetry.no_vacuous_pass_on_empty_calibration_or_missing_raw_shots
        sub).1 hraw
    refine ⟨hcert, ?_⟩
    rw [hcert]
    decide

/-! ## 2. Non-Fragmented Post-Wave-10 Coupled System & Master Synthesis (`C-UNIFIED-SYNTH-11`) -/

section CoupledSection

open Classical in
/-- **Single Non-Fragmented Post-Wave-10 Coupled Architecture**:
Couples `UnifiedCoupledSystem m X A` directly to:
- `ConformalControlGravityGates` §1–§4 (`ξ = 1/6`, stabilized `χ φ ψ` control, covariant
  stress-divergence cancellation driving unimodular Bianchi integrability on `U.gravConsts.1.G`,
  and `Weyl²` harmonic counterterm),
- `H1d4` weighted Banach truncation + OS/GNS/Ursell + `AH01` UV screening on `U`'s horizon floor,
- `H2` Wilson transfer + Dobrushin mass gap + Lüscher/Overlap stability + `(3,3,1)` `ClosedTests`
  & `AH01` lattice UV screening on `U`'s `qPovm`/`instKernel`/`AH01` floor,
- `H3` 2-loop `(3,3,1)` threshold repair + two-sided cosmological viability window enclosing
  `I_obs = invariantILambda U.gravConsts.1` + `AH01` `BinaryTesting` indistinguishability on `U`,
- `H4` Bell–CHSH / holdout / calibration / portfolio contracts with honest uncertified hardware record. -/
structure PostWave10CoupledSystem
    (m nOS nWil mUp nOv mMat nOrb lLoop : ℕ)
    (X A XBanach PhysHilbert UVCompletion IREFTData Val SDob UAdm OrbitSpace
      LatticeReg IREFTDataLat ValLat XCos : Type)
    [Fintype X] [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] [MeasurableSpace A]
    [Fintype SDob] [Nonempty SDob] [MeasurableSpace XCos] where
  -- Base Wave 7/10 non-fragmented coupled system
  U : UnifiedCausalChiralUnimodularSynthesis.UnifiedCoupledSystem m X A
  -- Conformal / local control / Bianchi / Weyl² parameters
  t0 : ℝ
  t1 : ℝ
  LambdaEff : ℝ → ℝ
  lamC : ℝ
  mChiSq : ℝ
  gChi : ℝ
  g4 : ℝ
  chiCtrl : ℝ → ℝ
  phiCtrl : ℝ → ℝ
  psiCtrl : ℝ → ℝ
  dNuChi : ℝ → ℝ
  dNuPhi : ℝ → ℝ
  dNuPsi : ℝ → ℝ
  dVchi : ℝ → ℝ
  dVphi : ℝ → ℝ
  dVpsi : ℝ → ℝ
  ellWeyl : ℝ
  nsWeyl : ℝ
  vWeyl : ℝ
  gammaRWeyl : ℝ
  hkWeyl : ℝ
  -- H1d4 parameters
  dBanach : UEOT.V3.Compression.ContractiveFixedPoint.DistanceLike XBanach
  phiBanach : XBanach → XBanach
  phiNBanach : ℕ → XBanach → XBanach
  kappaBanach : ℝ
  cTailBanach : ℝ
  rhoBanach : ℝ
  uInfBanach : XBanach
  uNBanach : ℕ → XBanach
  sOS : ℕ → (Fin nOS → ℝ) → (Fin nOS → ℝ) → ℝ
  sInfOS : (Fin nOS → ℝ) → (Fin nOS → ℝ) → ℝ
  mInfOS : Matrix (Fin nOS) (Fin nOS) ℝ
  qGNS : (Fin nOS → ℝ) → PhysHilbert
  qIRH1 : UVCompletion → IREFTData
  oPhysH1 : UVCompletion → Val
  kObsH1 : ℝ
  cUVH1 : ℝ
  dTVH1 : ℝ
  epsExpH1 : ℝ
  deltaAdvH1 : ℝ
  nShotsH1 : ℝ
  -- H2 parameters
  kWil : Matrix (Fin nWil) (Fin nWil) ℝ
  tWil : Matrix (Fin nWil) (Fin nWil) ℝ
  uPlaq : ℝ
  cWil : ℝ
  rWil : ℕ
  wLoop : ℕ → ℝ
  oLatSym : ℝ → ℝ
  remSym : ℝ → ℝ
  oContSym : ℝ
  c2Sym : ℝ
  c4Sym : ℝ
  aMaxSym : ℝ
  a0Sym : ℝ
  upWil : Matrix (Fin mUp) (Fin mUp) ℂ
  pDob : Matrix SDob SDob ℝ
  hpDob : pDob ∈ Matrix.rowStochastic ℝ SDob
  piOrb : UAdm → OrbitSpace
  wInvOrb : OrbitSpace → ℂ
  phiBerry : UAdm → ℝ
  gammaLoop : Fin (lLoop + 1) → UAdm
  pProj : Matrix (Fin mMat) (Fin mMat) ℂ
  d1P : Matrix (Fin mMat) (Fin mMat) ℂ
  d2P : Matrix (Fin mMat) (Fin mMat) ℂ
  gMat : Matrix (Fin mMat) (Fin mMat) ℂ
  gInvMat : Matrix (Fin mMat) (Fin mMat) ℂ
  hW : Matrix (Fin nOv) (Fin nOv) ℂ
  dHW : Matrix (Fin nOv) (Fin nOv) ℂ
  delta0Ov : ℝ
  etaOv : ℝ
  aOv : ℝ
  gamma5Ov : Matrix (Fin nOrb) (Fin nOrb) ℂ
  vOv : Matrix (Fin nOrb) (Fin nOrb) ℂ
  qIRH2 : LatticeReg → IREFTDataLat
  oLatH2 : LatticeReg → ValLat
  kObsH2 : ℝ
  cLatH2 : ℝ
  dTVH2 : ℝ
  epsExpH2 : ℝ
  deltaAdvH2 : ℝ
  nShotsH2 : ℝ
  z0H2 : ℂ
  -- H3 parameters
  b1RGE : ℝ
  b2RGE : ℝ
  b3RGE : ℝ
  db1RGE : ℝ
  db2RGE : ℝ
  db3RGE : ℝ
  c2_1RGE : ℝ
  c2_2RGE : ℝ
  c2_3RGE : ℝ
  dTh1RGE : ℝ
  dTh2RGE : ℝ
  dTh3RGE : ℝ
  aEmInvPDG : ℝ
  s2WPDG : ℝ
  alphaSPDG : ℝ
  tGutMin : ℝ
  iMinCos : ℝ
  iMaxCos : ℝ
  p0Cos : Measure XCos
  p1Cos : Measure XCos
  hp0Cos : IsProbabilityMeasure p0Cos
  hp1Cos : IsProbabilityMeasure p1Cos
  cIRCos : ℝ
  rRatioCos : ℝ
  i1Cos : ℝ
  i2Cos : ℝ
  deltaAdvCos : ℝ
  -- H4 submission governance record
  hwSub : MesoscopicDecoherenceGravimetry.PreRegisteredHardwareSubmission

/-- Joint structural admissibility predicate across all sectors of `PostWave10CoupledSystem`. -/
structure PostWave10CoupledSystem.Admissible
    {m nOS nWil mUp nOv mMat nOrb lLoop : ℕ}
    {X A XBanach PhysHilbert UVCompletion IREFTData Val SDob UAdm OrbitSpace
      LatticeReg IREFTDataLat ValLat XCos : Type}
    [Fintype X] [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] [MeasurableSpace A]
    [Fintype SDob] [Nonempty SDob] [MeasurableSpace XCos]
    (S : PostWave10CoupledSystem m nOS nWil mUp nOv mMat nOrb lLoop
      X A XBanach PhysHilbert UVCompletion IREFTData Val SDob UAdm OrbitSpace
      LatticeReg IREFTDataLat ValLat XCos) : Prop where
  hU : S.U.Admissible
  -- ConformalControlGravityGates + Bianchi coupling
  htSlab : S.t0 < S.t1
  hmChi : 0 ≤ S.mChiSq
  hgChi : 0 < S.gChi
  hg4 : 0 < S.g4
  hQuadThresh : S.lamC ^ 2 ≤ 2 * S.g4 * S.mChiSq
  hvWeyl : S.vWeyl ≠ 0
  hbianchiCtrl : ∀ t ∈ Set.Icc S.t0 S.t1,
    HasDerivWithinAt S.LambdaEff
      (8 * Real.pi * S.U.gravConsts.1.G *
        (let boxChi := S.lamC * S.phiCtrl t * S.psiCtrl t + S.dVchi t
         let boxPhi := S.lamC * S.chiCtrl t * S.psiCtrl t + S.dVphi t
         let boxPsi := S.lamC * S.chiCtrl t * S.phiCtrl t + S.dVpsi t
         let dNuInt :=
           S.lamC * (S.dNuChi t * S.phiCtrl t * S.psiCtrl t +
             S.chiCtrl t * S.dNuPhi t * S.psiCtrl t +
             S.chiCtrl t * S.phiCtrl t * S.dNuPsi t) +
           (S.dVchi t * S.dNuChi t + S.dVphi t * S.dNuPhi t + S.dVpsi t * S.dNuPsi t)
         boxChi * S.dNuChi t + boxPhi * S.dNuPhi t + boxPsi * S.dNuPsi t - dNuInt))
      (Set.Icc S.t0 S.t1) t
  -- H1d4 admissibility (coupled to U's AH01 floor)
  hContr : UEOT.V3.Compression.ContractiveFixedPoint.ContractiveWith
    S.dBanach S.kappaBanach S.phiBanach
  hCTail : 0 ≤ S.cTailBanach
  hRho : 1 < S.rhoBanach
  huInf : S.phiBanach S.uInfBanach = S.uInfBanach
  huN : ∀ N : ℕ, S.phiNBanach N (S.uNBanach N) = S.uNBanach N
  htailBanach : ∀ N : ℕ,
    S.dBanach.d (S.phiNBanach N (S.uNBanach N)) (S.phiBanach (S.uNBanach N)) ≤
      S.cTailBanach / S.rhoBanach ^ N
  hOSm : ∀ m0 : ℕ, ∀ psi : Fin nOS → ℝ, 0 ≤ S.sOS m0 psi psi
  hweakOS : ∀ psi : Fin nOS → ℝ,
    Filter.Tendsto (fun m0 : ℕ => S.sOS m0 psi psi) Filter.atTop (nhds (S.sInfOS psi psi))
  hSymmOS : S.mInfOSᵀ = S.mInfOS
  hPSDOS : ∀ psi : Fin nOS → ℝ, 0 ≤ dotProduct psi (S.mInfOS.mulVec psi)
  hqGNS : Surjective S.qGNS
  hkerGNS : ∀ u v : Fin nOS → ℝ, S.qGNS u = S.qGNS v →
    dotProduct (u - v) (S.mInfOS.mulVec (u - v)) = 0
  hqIRH1 : Surjective S.qIRH1
  hcompH1 : UEOT.V3.Compression.QuotientDescent.FiberCompatible S.qIRH1 S.oPhysH1
  hkH1 : 0 < S.kObsH1
  hCuvH1 : 0 < S.cUVH1
  hepsH1 : 0 < S.epsExpH1
  hdNNH1 : 0 ≤ S.dTVH1
  hdLeH1 : S.dTVH1 ≤ S.cUVH1 * (S.kObsH1 ^ 2 *
    ((2 * S.U.eMin / S.U.lamSys) * (S.U.gravConsts.1.hbar * S.U.gravConsts.1.G / S.U.gravConsts.1.c ^ 3)))
  hdeltaH1 : 0 < S.deltaAdvH1
  hNH1 : 0 ≤ S.nShotsH1
  hhoeffH1 : S.deltaAdvH1 ≤ 2 * S.nShotsH1 * S.dTVH1 ^ 2
  -- H2 admissibility (coupled to U's AH01 floor)
  hSymmWil : S.tWilᵀ = S.tWil
  hPSDWil : ∀ v : Fin nWil → ℝ, 0 ≤ dotProduct v (S.tWil.mulVec v)
  huPosWil : 0 < S.uPlaq
  huLtWil : S.uPlaq < 1
  hcWWil : 0 ≤ S.cWil
  hrWil : 1 ≤ S.rWil
  hWWil : ∀ t : ℕ, |S.wLoop t| ≤ S.cWil * S.uPlaq ^ (S.rWil * t)
  haMaxSym : 0 < S.aMaxSym
  ha0PosSym : 0 < S.a0Sym
  ha0LeSym : S.a0Sym ≤ S.aMaxSym
  hOSym : ∀ a : ℝ, 0 < a → a ≤ S.aMaxSym →
    S.oLatSym a = S.oContSym + S.c2Sym * a ^ 2 + S.remSym a
  hremSym : ∀ a : ℝ, 0 < a → a ≤ S.aMaxSym → |S.remSym a| ≤ S.c4Sym * a ^ 4
  hUpWil : S.upWilᴴ * S.upWil = 1
  halphaDob : UEOT.V3.FiniteDobrushin.dobrushinAlpha S.pDob S.hpDob < 1
  hpiOrb : Surjective S.piOrb
  hloopOrb : S.piOrb (S.gammaLoop ⟨lLoop, Nat.lt_succ_self lLoop⟩) = S.piOrb (S.gammaLoop 0)
  hcobOrb : ∀ u u' : UAdm, S.piOrb u = S.piOrb u' → S.phiBerry u' - S.phiBerry u = 0
  hggrOrb : S.gMat * S.gInvMat = 1
  hgglOrb : S.gInvMat * S.gMat = 1
  hHHerm : S.hWᴴ = S.hW
  hdHHerm : S.dHWᴴ = S.dHW
  hdelta0Ov : 0 < S.delta0Ov
  hetaNN : 0 ≤ S.etaOv
  hetaLt : S.etaOv < S.delta0Ov
  hgapOv : ∀ v : Fin nOv → ℂ, S.delta0Ov ^ 2 *
    ChiralGaugeOverlapClockBridge.l2NormSq v ≤
    ChiralGaugeOverlapClockBridge.l2NormSq (S.hW.mulVec v)
  hpertOv : ∀ v : Fin nOv → ℂ,
    ChiralGaugeOverlapClockBridge.l2NormSq (S.dHW.mulVec v) ≤
    S.etaOv ^ 2 * ChiralGaugeOverlapClockBridge.l2NormSq v
  haOv : S.aOv ≠ 0
  hg5Herm : S.gamma5Ovᴴ = S.gamma5Ov
  hg5Sq : S.gamma5Ov * S.gamma5Ov = 1
  hVHerm : S.vOvᴴ = S.vOv
  hVSq : S.vOv * S.vOv = 1
  hqIRH2 : Surjective S.qIRH2
  hcompH2 : UEOT.V3.Compression.QuotientDescent.FiberCompatible S.qIRH2 S.oLatH2
  hkH2 : 0 < S.kObsH2
  hClatH2 : 0 < S.cLatH2
  hepsH2 : 0 < S.epsExpH2
  hdNNH2 : 0 ≤ S.dTVH2
  hdLeH2 : S.dTVH2 ≤ S.cLatH2 * (S.kObsH2 ^ 2 *
    ((2 * S.U.eMin / S.U.lamSys) * (S.U.gravConsts.1.hbar * S.U.gravConsts.1.G / S.U.gravConsts.1.c ^ 3)))
  hdeltaH2 : 0 < S.deltaAdvH2
  hNH2 : 0 ≤ S.nShotsH2
  hhoeffH2 : S.deltaAdvH2 ≤ 2 * S.nShotsH2 * S.dTVH2 ^ 2
  -- H3 admissibility (coupled to U's invariantILambda & AH01 floor)
  haEmLo : 127924 / 1000 ≤ S.aEmInvPDG
  haEmHi : S.aEmInvPDG ≤ 127978 / 1000
  hs2WLo : 23117 / 100000 ≤ S.s2WPDG
  hs2WHi : S.s2WPDG ≤ 23141 / 100000
  haSLo : 1153 / 10000 ≤ S.alphaSPDG
  haSHi : S.alphaSPDG ≤ 1207 / 10000
  hDdbNeg : CoreUnitGaugeAndDimensionlessConstants.collinearityDefect
    (41 / 10) (-19 / 6) (-7) S.db1RGE S.db2RGE S.db3RGE < 0
  hDthBd : |CoreUnitGaugeAndDimensionlessConstants.collinearityDefect
    (41 / 10) (-19 / 6) (-7) (S.c2_1RGE + S.dTh1RGE) (S.c2_2RGE + S.dTh2RGE) (S.c2_3RGE + S.dTh3RGE)| < 38
  hiMinPos : 0 < S.iMinCos
  hiMinLe : S.iMinCos ≤ (2829 : ℝ) / 10 ^ 125
  hiObsLo : (2829 : ℝ) / 10 ^ 125 ≤
    CoreUnitGaugeAndDimensionlessConstants.invariantILambda S.U.gravConsts.1
  hiObsHi : CoreUnitGaugeAndDimensionlessConstants.invariantILambda S.U.gravConsts.1 ≤
    (2948 : ℝ) / 10 ^ 125
  hiMaxGt : (2948 : ℝ) / 10 ^ 125 < S.iMaxCos
  hcIRCos : 0 < S.cIRCos
  hrRatioCos : 0 < S.rRatioCos
  htvCos : UEOT.V3.TotalVariation.tvDist S.p0Cos S.p1Cos ≤ S.cIRCos * S.rRatioCos * |S.i1Cos - S.i2Cos|
  hgapCos : |S.i1Cos - S.i2Cos| < (2 * S.deltaAdvCos) / (S.cIRCos * S.rRatioCos)
  -- H4 raw hardware non-certification lock
  hRawFalse : S.hwSub.rawShotsComplete = false

/-- **Master Post-Wave-10 Non-Fragmented Cross-Sector Closure (`C-UNIFIED-SYNTH-11`)**:
From a single `S.Admissible` system, proves simultaneously without fragmentation:
1. All `7` coupled laws of `unified_non_fragmented_cross_sector_synthesis S.U hS.hU`, yielding the
   shared `AH01` clock energy `E_tot`;
2. `ConformalControlGravityGates` §1–§4 (`ξ = 1/6`, SOS control stability & semiboundedness,
   exact stress-divergence cancellation feeding `unimodular_bianchi_integrability_requires_chiral_anomaly_cancellation`
   on `S.U.gravConsts.1.G` to lock `LambdaEff t = LambdaEff t0` across `[t0, t1]`, and `Weyl²`
   harmonic counterterm cancellation);
3. `H1d4` closure (Banach truncation convergence + OS weak-limit GNS quotient + `AH01` UV
   screening on `S.U`'s floor and `E_tot`);
4. `H2a–H2c` closure (Wilson plaquette transfer positivity & area law + Dobrushin mass gap +
   Lüscher/Overlap stability + `(3,3,1)` `ClosedTests` & `AH01` lattice UV screening on `S.U`'s
   `qPovm`/`instKernel`/`AH01` floor and `E_tot`);
5. `H3a–H3c` closure (2-loop `(3,3,1)` GUT repair polytope across PDG-2024 `3σ` + Jarlskog
   ceiling `1/(6√3)` + two-sided cosmological viability window containing
   `I_obs = invariantILambda S.U.gravConsts.1` + `AH01` `BinaryTesting` lower bound on `S.U`'s floor);
6. `H4a–H4c` closure (CHSH `≤ 2` / Tsirelson `2√2` + nonselective `2δ` / multi-cell TV / Ville
   optional stopping + `Θ_0.99` / power margin / paired baseline / `P-COSMO-02` / 3-ch flavor
   contracts + `deviceCertified S.hwSub = false` and `.OPEN` governance). -/
theorem post_wave10_unified_cross_sector_closure
    {m nOS nWil mUp nOv mMat nOrb lLoop : ℕ}
    {X A XBanach PhysHilbert UVCompletion IREFTData Val SDob UAdm OrbitSpace
      LatticeReg IREFTDataLat ValLat XCos : Type}
    [Fintype X] [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] [MeasurableSpace A]
    [Fintype SDob] [Nonempty SDob] [MeasurableSpace XCos]
    (S : PostWave10CoupledSystem m nOS nWil mUp nOv mMat nOrb lLoop
      X A XBanach PhysHilbert UVCompletion IREFTData Val SDob UAdm OrbitSpace
      LatticeReg IREFTDataLat ValLat XCos)
    (hS : S.Admissible) :
    let U := S.U
    let L_min := Real.sqrt (2 * U.eMin / U.lamSys)
    let l_P := CoreUnitGaugeAndDimensionlessConstants.planckLength U.gravConsts.1
    let L_min_sq := (2 * U.eMin / U.lamSys) *
      (U.gravConsts.1.hbar * U.gravConsts.1.G / U.gravConsts.1.c ^ 3)
    let I_obs := CoreUnitGaugeAndDimensionlessConstants.invariantILambda U.gravConsts.1
    -- (1) Wave 7/10 UnifiedCoupledSystem 7-law synthesis
    ((0 < UnifiedCausalChiralUnimodularSynthesis.causalSimplex41VolSq U.alphaTilt U.aLat ∧
        0 < UnifiedCausalChiralUnimodularSynthesis.causalSimplex32VolSq U.alphaTilt U.aLat ∧
        0 < L_min * l_P ∧ L_min * l_P < U.sensorL) ∧
      (0 < (CoreUnitGaugeAndDimensionlessConstants.posInvariantILambda U.gravConsts).1) ∧
      (U.nGen * ChiralGaugeOverlapClockBridge.totalWeylDimension
        ChiralGaugeOverlapClockBridge.smChiralGeneration15 = 45) ∧
      (∃ E_tot : ℝ, U.eMin * U.gravConsts.1.hbar * U.gravConsts.1.c ≤ E_tot * U.sensorL ∧
        2 * U.gravConsts.1.G * E_tot < U.lamSys * U.gravConsts.1.c ^ 4 * U.sensorL)) ∧
    -- (2) ConformalControlGravityGates §1-§4 + Unimodular Bianchi integrability
    (((∀ chi kappa Q : ℝ,
        ConformalControlGravityGates.bulkCurvatureCoupling (1 / 6) chi kappa Q = 0 ∧
        ConformalControlGravityGates.netScalarEndpoint (1 / 6) kappa Q = 0) ∧
      (∀ chi phi psi : ℝ,
        0 ≤ ConformalControlGravityGates.stabilizedControlPotential S.mChiSq 0 S.g4 S.lamC chi phi psi) ∧
      (∀ chi phi psi : ℝ,
        -(S.lamC ^ 4 / (16 * S.gChi * S.g4 ^ 2)) ≤
          ConformalControlGravityGates.stabilizedControlPotential S.mChiSq S.gChi S.g4 S.lamC chi phi psi) ∧
      (∀ t ∈ Set.Icc S.t0 S.t1, S.LambdaEff t = S.LambdaEff S.t0) ∧
      (let Cm := (8 / 3) * S.ellWeyl * (S.ellWeyl - 3) * (S.nsWeyl / (960 * S.vWeyl))
       let gammaWK := S.gammaRWeyl - S.nsWeyl * S.hkWeyl / (960 * S.vWeyl)
       Cm * S.hkWeyl + (8 / 3) * S.ellWeyl * (S.ellWeyl - 3) * gammaWK =
         (8 / 3) * S.ellWeyl * (S.ellWeyl - 3) * S.gammaRWeyl))) ∧
    -- (3) H1d4 operational closure coupled to U's AH01 floor
    ((∀ N : ℕ, S.dBanach.d (S.uNBanach N) S.uInfBanach ≤
        (S.cTailBanach / (1 - S.kappaBanach)) / S.rhoBanach ^ N) ∧
      (∀ psi : Fin nOS → ℝ, 0 ≤ S.sInfOS psi psi) ∧
      ((0 < L_min_sq ∧ L_min_sq < U.sensorL ^ 2) ∧
        (S.kObsH1 ^ 2 * L_min_sq < S.epsExpH1 / S.cUVH1 → S.dTVH1 < S.epsExpH1) ∧
        S.deltaAdvH1 / (2 * S.cUVH1 ^ 2 * (S.kObsH1 ^ 2 * L_min_sq) ^ 2) ≤ S.nShotsH1 ∧
        ∃! O_IR : IREFTData → Val, O_IR ∘ S.qIRH1 = S.oPhysH1)) ∧
    -- (4) H2a-H2c closure coupled to U's ClosedTests & AH01 floor
    ((0 < NonAbelianLatticeMassGapAndChiralIntegrabilityH2.wilsonStringTension S.uPlaq ∧
        (∀ m : ℕ, ∀ v : Fin nWil → ℝ, 0 ≤ dotProduct v ((S.tWil ^ m).mulVec v))) ∧
      (0 < NonAbelianLatticeMassGapAndChiralIntegrabilityH2.dobrushinGapRate
          (UEOT.V3.FiniteDobrushin.dobrushinAlpha S.pDob S.hpDob) ∧
        ∃! mu_inv : stdSimplex ℝ SDob,
          UEOT.V3.FiniteDobrushin.step S.pDob S.hpDob mu_inv = mu_inv) ∧
      ((S.hW + S.dHW)ᴴ = S.hW + S.dHW ∧ 0 < S.delta0Ov - S.etaOv ∧
        ∀ v : Fin nOv → ℂ, (S.delta0Ov - S.etaOv) ^ 2 *
          ChiralGaugeOverlapClockBridge.l2NormSq v ≤
          ChiralGaugeOverlapClockBridge.l2NormSq ((S.hW + S.dHW).mulVec v)) ∧
      ((S.kObsH2 ^ 2 * L_min_sq < S.epsExpH2 / S.cLatH2 → S.dTVH2 < S.epsExpH2) ∧
        (∃! O_IR : IREFTDataLat → ValLat, O_IR ∘ S.qIRH2 = S.oLatH2) ∧
        (∃! K : Kernel (unitInterval × A) unitInterval,
          IsMarkovKernel K ∧ ∀ (b : ProbabilityMeasure X) (a : A),
            (UEOT.V3.Compression.TheoryCompletion.ScientificClosure.c1BeliefTransitionKernel
              U.instKernel
              (UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableBeliefQuotient.observation
                U.qPovm U.hqMeas) (b, a)).map
                (UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableBeliefQuotient.coordinate
                  U.qPovm) =
              K (UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableBeliefQuotient.coordinate
                  U.qPovm b, a)))) ∧
    -- (5) H3a-H3c closure coupled to U's invariantILambda & AH01 BinaryTesting floor
    ((∃ tI tGUT : ℝ, S.tGutMin ≤ tGUT ∧ 0 < tGUT - tI ∧
        CoreUnitGaugeAndDimensionlessConstants.collinearityDefect (41 / 10) (-19 / 6) (-7)
            S.db1RGE S.db2RGE S.db3RGE * (tGUT - tI) +
          CoreUnitGaugeAndDimensionlessConstants.collinearityDefect (41 / 10) (-19 / 6) (-7)
            (S.c2_1RGE + S.dTh1RGE) (S.c2_2RGE + S.dTh2RGE) (S.c2_3RGE + S.dTh3RGE) =
          CoreUnitGaugeAndDimensionlessConstants.delta123SM
            ((3 / 5 : ℝ) * (1 - S.s2WPDG) * S.aEmInvPDG)
            (S.s2WPDG * S.aEmInvPDG) (1 / S.alphaSPDG)) ∧
      (∀ V : Matrix (Fin 3) (Fin 3) ℂ, V * Vᴴ = 1 →
        |DimensionlessCouplingsFlavorAndVacuumWindowH3.ckmJarlskog V| ≤ 1 / (6 * Real.sqrt 3)) ∧
      ((S.iMinCos ≤ I_obs ∧ I_obs < S.iMaxCos) ∧
        (∀ n : ℕ, (UEOT.V3.ViabilityKernel.viabilityIter
          (UnimodularVacuumConstantSelection.cosmicHaloTransition I_obs S.iMaxCos)
          UnimodularVacuumConstantSelection.boundViableSet n).Nonempty) ∧
        (∀ Aset : Set XCos, MeasurableSet Aset →
          1 / 2 - S.deltaAdvCos < UEOT.V3.BinaryTesting.binaryRisk S.p0Cos S.p1Cos Aset))) ∧
    -- (6) H4a-H4c protocol closure & honest non-certified status
    ((∀ a0 a1 b0 b1 : ℝ, |a0| ≤ 1 → |a1| ≤ 1 → |b0| ≤ 1 → |b1| ≤ 1 →
        |BellCHSHAndBlindHoldoutContractH4.chshLHVKernel a0 a1 b0 b1| ≤ 2) ∧
      (∀ (A0 A1 B0 B1 : Matrix (Fin 2) (Fin 2) ℂ) (ρ : UEOTQM.Density MesoscopicDecoherenceGravimetry.Qubit2),
        A0 * A0 = MesoscopicDecoherenceGravimetry.pauliI →
        A1 * A1 = MesoscopicDecoherenceGravimetry.pauliI →
        B0 * B0 = MesoscopicDecoherenceGravimetry.pauliI →
        B1 * B1 = MesoscopicDecoherenceGravimetry.pauliI →
        A0ᴴ = A0 → A1ᴴ = A1 → B0ᴴ = B0 → B1ᴴ = B1 →
        |UEOTQM.pairing (BellCHSHAndBlindHoldoutContractH4.chshOp A0 A1 B0 B1) ρ.matrix| ≤ 2 * Real.sqrt 2) ∧
      (MesoscopicDecoherenceGravimetry.deviceCertified S.hwSub = false ∧
        MathV42ClosedTestsAndMechanismBridge.physicalUnificationStatus
          (Fintype.card PostWave10OpenFrontier)
          (MesoscopicDecoherenceGravimetry.deviceCertified S.hwSub) = .OPEN)) := by
  intro U L_min l_P L_min_sq I_obs
  have hSynth := UnifiedCausalChiralUnimodularSynthesis.unified_non_fragmented_cross_sector_synthesis
    S.U hS.hU
  rcases hSynth with ⟨hC1, hC2, hC3, hC4, _, _, _⟩
  rcases hC4 with ⟨⟨E_tot, hclock, hnotrap⟩, _, _⟩
  have hL_pos : 0 < U.sensorL := lt_trans hC1.2.2.1 hC1.2.2.2
  -- ConformalControlGravityGates §1-§4 + Bianchi integrability
  have hXi := (ConformalControlGravityGates.conformal_xi_simultaneous_vanishing (1 / 6)).mpr rfl
  have hNonneg := (ConformalControlGravityGates.stabilized_control_nonneg_iff_mass_threshold hS.hg4).mpr
    hS.hQuadThresh
  have hLow : ∀ chi phi psi : ℝ,
      -(S.lamC ^ 4 / (16 * S.gChi * S.g4 ^ 2)) ≤
        ConformalControlGravityGates.stabilizedControlPotential S.mChiSq S.gChi S.g4 S.lamC chi phi psi :=
    fun chi phi psi =>
      ConformalControlGravityGates.stabilized_control_global_lower_bound hS.hmChi hS.hgChi hS.hg4 chi phi psi
  let A_anom : ℝ → ℝ := fun t =>
    let boxChi := S.lamC * S.phiCtrl t * S.psiCtrl t + S.dVchi t
    let boxPhi := S.lamC * S.chiCtrl t * S.psiCtrl t + S.dVphi t
    let boxPsi := S.lamC * S.chiCtrl t * S.phiCtrl t + S.dVpsi t
    let dNuInt :=
      S.lamC * (S.dNuChi t * S.phiCtrl t * S.psiCtrl t +
        S.chiCtrl t * S.dNuPhi t * S.psiCtrl t +
        S.chiCtrl t * S.phiCtrl t * S.dNuPsi t) +
      (S.dVchi t * S.dNuChi t + S.dVphi t * S.dNuPhi t + S.dVpsi t * S.dNuPsi t)
    boxChi * S.dNuChi t + boxPhi * S.dNuPhi t + boxPsi * S.dNuPsi t - dNuInt
  have hAnom0 : ∀ t ∈ Set.Icc S.t0 S.t1, A_anom t = 0 := fun t _ =>
    ConformalControlGravityGates.covariant_stress_divergence_cancels
      S.lamC (S.chiCtrl t) (S.phiCtrl t) (S.psiCtrl t)
      (S.dNuChi t) (S.dNuPhi t) (S.dNuPsi t) (S.dVchi t) (S.dVphi t) (S.dVpsi t)
  have hBianchi :=
    (UnifiedCausalChiralUnimodularSynthesis.unimodular_bianchi_integrability_requires_chiral_anomaly_cancellation
      hS.htSlab U.gravConsts.1.hG S.LambdaEff A_anom hS.hbianchiCtrl).1.mpr hAnom0
  have hWeyl := ConformalControlGravityGates.weyl_counterterm_cancels_all_harmonics
    S.ellWeyl S.nsWeyl S.vWeyl S.gammaRWeyl S.hkWeyl hS.hvWeyl
  -- H1d4 operational closure coupled to U's AH01 floor and E_tot
  have hBanach := Nonperturbative4DMeasureLimitH1d4.weighted_banach_infinite_truncation_convergence
    S.dBanach S.phiBanach S.phiNBanach hS.hContr hS.hCTail hS.hRho
    S.uInfBanach hS.huInf S.uNBanach hS.huN hS.htailBanach
  have hOS := Nonperturbative4DMeasureLimitH1d4.os_reflection_positivity_closed_under_weak_limits_and_gns_quotient
    S.sOS S.sInfOS hS.hOSm hS.hweakOS S.mInfOS hS.hSymmOS hS.hPSDOS S.qGNS hS.hqGNS hS.hkerGNS
  have hH1AH := Nonperturbative4DMeasureLimitH1d4.ah01_horizon_uv_screening_and_finite_shot_indistinguishability
    S.qIRH1 S.oPhysH1 hS.hqIRH1 hS.hcompH1
    hL_pos hS.hU.heMin U.gravConsts.1.hHbar U.gravConsts.1.hC U.gravConsts.1.hG hS.hU.hlamSys
    hclock hnotrap hS.hkH1 hS.hCuvH1 hS.hepsH1 hS.hdNNH1 hS.hdLeH1 hS.hdeltaH1 hS.hNH1 hS.hhoeffH1
  -- H2a-H2c operational closure coupled to U's ClosedTests, AH01 floor, and E_tot
  have hWil := NonAbelianLatticeMassGapAndChiralIntegrabilityH2.wilson_plaquette_transfer_positivity_and_strong_coupling_area_law
    S.kWil S.tWil hS.hSymmWil hS.hPSDWil S.wLoop hS.huPosWil hS.huLtWil hS.hcWWil hS.hrWil hS.hWWil
    S.oLatSym S.remSym hS.haMaxSym hS.ha0PosSym hS.ha0LeSym hS.hOSym hS.hremSym S.upWil hS.hUpWil
  have hDob := NonAbelianLatticeMassGapAndChiralIntegrabilityH2.dobrushin_lattice_cluster_mass_gap
    S.pDob S.hpDob hS.halphaDob
  have hLusch := NonAbelianLatticeMassGapAndChiralIntegrabilityH2.luscher_berry_loop_holonomy_and_overlap_gap_stability
    S.piOrb hS.hpiOrb S.wInvOrb S.phiBerry lLoop S.gammaLoop hS.hloopOrb hS.hcobOrb
    S.pProj S.d1P S.d2P S.gMat S.gInvMat hS.hggrOrb hS.hgglOrb S.hW S.dHW hS.hHHerm hS.hdHHerm
    hS.hdelta0Ov hS.hetaNN hS.hetaLt hS.hgapOv hS.hpertOv S.aOv hS.haOv S.gamma5Ov S.vOv
    hS.hg5Herm hS.hg5Sq hS.hVHerm hS.hVSq
  have hH2AH := NonAbelianLatticeMassGapAndChiralIntegrabilityH2.ah01_lattice_uv_screening_and_h2_decomposition
    U.qPovm U.hqMeas U.instKernel U.zeroRep U.oneRep hS.hU.hzero hS.hU.hone
    S.qIRH2 S.oLatH2 hS.hqIRH2 hS.hcompH2
    hL_pos hS.hU.heMin U.gravConsts.1.hHbar U.gravConsts.1.hC U.gravConsts.1.hG hS.hU.hlamSys
    hclock hnotrap hS.hkH2 hS.hClatH2 hS.hepsH2 hS.hdNNH2 hS.hdLeH2 hS.hdeltaH2 hS.hNH2 hS.hhoeffH2
    S.z0H2
  -- H3a-H3c closure coupled to U's invariantILambda, AH01 floor, and E_tot
  have hTwoLoop := DimensionlessCouplingsFlavorAndVacuumWindowH3.two_loop_threshold_collinearity_and_proton_decay_bound
    (41 / 10) (-19 / 6) (-7) S.db1RGE S.db2RGE S.db3RGE S.c2_1RGE S.c2_2RGE S.c2_3RGE
    S.dTh1RGE S.dTh2RGE S.dTh3RGE
  have hRGE := hTwoLoop.2.2.2.1
    (aEmInv := S.aEmInvPDG) (s2W := S.s2WPDG) (alphaS := S.alphaSPDG) (tGutMin := S.tGutMin)
    hS.haEmLo hS.haEmHi hS.hs2WLo hS.hs2WHi hS.haSLo hS.haSHi hS.hDdbNeg hS.hDthBd
  have hJar := DimensionlessCouplingsFlavorAndVacuumWindowH3.jarlskog_invariant_rephasing_and_ceiling
  have hViab := (DimensionlessCouplingsFlavorAndVacuumWindowH3.two_sided_cosmological_viability_and_operational_ilambda_indistinguishability.{0, 0, 0}).2.2.1
    hS.hiMinPos hS.hiMinLe hS.hiObsLo hS.hiObsHi hS.hiMaxGt
  have := S.hp0Cos
  have := S.hp1Cos
  have hBinCos := (DimensionlessCouplingsFlavorAndVacuumWindowH3.two_sided_cosmological_viability_and_operational_ilambda_indistinguishability.{0, 0, 0}).2.2.2.2
    S.p0Cos S.p1Cos
    hL_pos hS.hU.heMin U.gravConsts.1.hHbar U.gravConsts.1.hC U.gravConsts.1.hG hS.hU.hlamSys
    hclock hnotrap hS.hcIRCos hS.hrRatioCos hS.htvCos hS.hgapCos
  -- H4a-H4c protocol closure & honest device status
  have hCHSH := BellCHSHAndBlindHoldoutContractH4.chsh_lhv_bound_two_and_tsirelson_two_sqrt_two
  have hGov := post_wave10_frontier_status_and_honest_open_governance.2.2.2.2.1 S.hwSub hS.hRawFalse
  exact ⟨⟨⟨hC1.1, hC1.2.1, hC1.2.2.1, hC1.2.2.2⟩, hC2.2.1, hC3.1, ⟨E_tot, hclock, hnotrap⟩⟩,
    ⟨hXi, hNonneg, hLow, hBianchi, hWeyl⟩,
    ⟨hBanach.1, hOS.1, hH1AH⟩,
    ⟨⟨hWil.2.2.1.1, hWil.2.1⟩, ⟨hDob.1.2, hDob.2.1⟩, hLusch.2.2.2.1,
      ⟨hH2AH.2.1.2.1, hH2AH.2.1.2.2.2, hH2AH.1.2.2.2.mp hS.hU.hClosed⟩⟩,
    ⟨hRGE.2.2.2, hJar.2.2.1, ⟨⟨hViab.2.1, hViab.2.2.1⟩, hViab.2.2.2, hBinCos.2⟩⟩,
    ⟨hCHSH.1, hCHSH.2.2.1, hGov⟩⟩

/-! ## 3. Constructive Non-Vacuity Witness (`exists_admissible_post_wave10_unified_system`) -/

private noncomputable def unitIntervalScalarDist :
    UEOT.V3.Compression.ContractiveFixedPoint.DistanceLike ℝ where
  d x y := |x - y|
  nonneg _ _ := abs_nonneg _
  triangle x y z := abs_sub_le x y z
  eq_of_zero h := sub_eq_zero.mp (abs_eq_zero.mp h)

/-- **Constructive Joint Consistency Witness**:
Explicitly inhabits `PostWave10CoupledSystem` using a Planck-scaled `UnifiedCoupledSystem 2 Bool Bool`
witness (`I_Λ = 2888 / 10^125` inside Planck-2018+BAO `1σ`, `α = 2/3 > 7/12`, `a_lat = 2 > 1`)
and proves `S.Admissible`, ruling out any hidden cross-sector inconsistency across `H1–H4` and
`ConformalControlGravityGates`. -/
theorem exists_admissible_post_wave10_unified_system :
    ∃ (S : PostWave10CoupledSystem 2 1 2 2 2 2 2 4
      Bool Bool ℝ Unit Unit Unit ℝ (Fin 2) Unit Unit Unit Unit Unit Bool),
      S.Admissible := by
  let grav : CoreUnitGaugeAndDimensionlessConstants.PosGravVacuumConstants :=
    ⟨CoreUnitGaugeAndDimensionlessConstants.planckGaugeSection ((2888 : ℝ) / 10 ^ 125),
      by simp [CoreUnitGaugeAndDimensionlessConstants.planckGaugeSection]⟩
  let H0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
  let Γ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  let instK : Kernel (Bool × Bool) Bool :=
    Kernel.deterministic (fun xa => Bool.xor xa.1 xa.2) (measurable_of_countable _)
  let U0 : UnifiedCausalChiralUnimodularSynthesis.UnifiedCoupledSystem 2 Bool Bool := {
    gravConsts := grav
    alphaTilt := 2 / 3
    aLat := 2
    sensorL := 3
    eMin := 1
    lamSys := 2
    gMetric := UnifiedCausalChiralUnimodularSynthesis.minkowskiEta4D
    gMetricInv := UnifiedCausalChiralUnimodularSynthesis.minkowskiEta4D
    tDyn := 0
    cBos := 1
    dRhoPhase := 1 / 2
    nGen := 3
    nLapse := fun _ => 1
    nMin := 1
    delta0 := 1
    h0Dirac := H0
    gammaDirac := Γ
    omegaSea := ![1, 1]
    rIdle := ⟨1 / 4, by norm_num⟩
    rRep := ⟨3 / 4, by norm_num⟩
    hrIdle1 := Subtype.mk_le_mk.mpr (by norm_num)
    hrRep1 := Subtype.mk_le_mk.mpr (by norm_num)
    cRep := 1
    walletB := 2
    betaCoh := 1
    orgFlow := UnifiedCausalChiralUnimodularSynthesis.dissipativeHomeostaticFlow
    xInit := 1
    qPovm := id
    hqMeas := measurable_id
    zeroRep := false
    oneRep := true
    instKernel := instK
    instMarkov := inferInstance
  }
  have hLp : CoreUnitGaugeAndDimensionlessConstants.planckLength grav.1 = 1 := by
    simp [grav, CoreUnitGaugeAndDimensionlessConstants.planckLength,
      CoreUnitGaugeAndDimensionlessConstants.planckLengthSq,
      CoreUnitGaugeAndDimensionlessConstants.planckGaugeSection]
  have hLmin : Real.sqrt (2 * U0.eMin / U0.lamSys) = 1 := by
    dsimp [U0]; norm_num
  have heta : UnifiedCausalChiralUnimodularSynthesis.minkowskiEta4D *
      UnifiedCausalChiralUnimodularSynthesis.minkowskiEta4D = 1 := by
    unfold UnifiedCausalChiralUnimodularSynthesis.minkowskiEta4D
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hS_one : ChiralGaugeOverlapClockBridge.sqrtLapseMatrix U0.nLapse = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [ChiralGaugeOverlapClockBridge.sqrtLapseMatrix, U0]
    · simp [ChiralGaugeOverlapClockBridge.sqrtLapseMatrix,
        Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hU_adm : U0.Admissible := {
    halpha := by dsimp [U0]; norm_num
    heMin := by dsimp [U0]; norm_num
    hlamSys := by dsimp [U0]; norm_num
    haLat_gt := by rw [hLmin, hLp]; dsimp [U0]; norm_num
    haLat_le := by dsimp [U0]; norm_num
    hgInv := heta
    hnGen := rfl
    hnMin := by dsimp [U0]; norm_num
    hdelta0 := by dsimp [U0]; norm_num
    hnLapse := fun _ => le_refl 1
    hh0Herm := by ext i j; fin_cases i <;> fin_cases j <;> simp [U0, H0]
    hh0Anti := by ext i j; fin_cases i <;> fin_cases j <;> simp [U0, H0, Γ]
    hcommS := by rw [hS_one, Matrix.one_mul, Matrix.mul_one]
    hgap0 := by
      intro u
      dsimp [U0, H0, ChiralGaugeOverlapClockBridge.l2NormSq]
      simp [Fin.sum_univ_two, Matrix.mulVec, dotProduct]
    hrLt := Subtype.mk_lt_mk.mpr (by norm_num)
    hcRep := by dsimp [U0]; norm_num
    hwallet := by dsimp [U0]; norm_num
    hbeta := by dsimp [U0]; norm_num
    hflowStay := by
      intro t
      change (1 / 2 : ℝ) + Real.exp (-(t : ℝ)) * (1 - 1 / 2) ∈ Set.Icc (0 : ℝ) 1
      have hexp_pos : 0 < Real.exp (-(t : ℝ)) := Real.exp_pos _
      have hexp_le : Real.exp (-(t : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by simp)
      constructor <;> nlinarith
    hzero := rfl
    hone := rfl
    hClosed := by
      intro x x' hxx' a
      have hxeq : x = x' := hxx'
      subst hxeq
      rfl
  }
  let K_wil : Matrix (Fin 2) (Fin 2) ℝ := !![(1 : ℝ), 0; 0, (1 / 2 : ℝ)]
  let T_wil : Matrix (Fin 2) (Fin 2) ℝ := K_wilᵀ * K_wil
  obtain ⟨P_mix, hMix, _, hDob_lt, _, _⟩ :=
    NonAbelianLatticeMassGapAndChiralIntegrabilityH2.dobrushin_lattice_cluster_concrete_witness
  let dH_ov : Matrix (Fin 2) (Fin 2) ℂ := !![((1 / 4 : ℝ) : ℂ), 0; 0, ((1 / 4 : ℝ) : ℂ)]
  let pBool : Measure Bool := Measure.dirac true
  let hw : MesoscopicDecoherenceGravimetry.PreRegisteredHardwareSubmission := {
    rawShotsComplete := false
    calibrationPolytopeNonEmpty := true
    singleEventPowerPassed := true
    holdoutBlindedAndPassed := true
    holdoutWitnessUpper95 := 0
  }
  let S : PostWave10CoupledSystem 2 1 2 2 2 2 2 4
      Bool Bool ℝ Unit Unit Unit ℝ (Fin 2) Unit Unit Unit Unit Unit Bool := {
    U := U0
    t0 := 0
    t1 := 1
    LambdaEff := fun _ => 1
    lamC := 1
    mChiSq := 1
    gChi := 1
    g4 := 1
    chiCtrl := fun _ => 0
    phiCtrl := fun _ => 0
    psiCtrl := fun _ => 0
    dNuChi := fun _ => 0
    dNuPhi := fun _ => 0
    dNuPsi := fun _ => 0
    dVchi := fun _ => 0
    dVphi := fun _ => 0
    dVpsi := fun _ => 0
    ellWeyl := 8
    nsWeyl := 1
    vWeyl := 1
    gammaRWeyl := 1
    hkWeyl := 1
    dBanach := unitIntervalScalarDist
    phiBanach := fun _ => 0
    phiNBanach := fun _ _ => 0
    kappaBanach := 1 / 2
    cTailBanach := 0
    rhoBanach := 2
    uInfBanach := 0
    uNBanach := fun _ => 0
    sOS := fun _ _ _ => 0
    sInfOS := fun _ _ => 0
    mInfOS := 0
    qGNS := fun _ => ()
    qIRH1 := id
    oPhysH1 := fun _ => 0
    kObsH1 := 1
    cUVH1 := 1
    dTVH1 := 1
    epsExpH1 := 2
    deltaAdvH1 := 1
    nShotsH1 := 1
    kWil := K_wil
    tWil := T_wil
    uPlaq := 1 / 9
    cWil := 1
    rWil := 1
    wLoop := fun t => (1 / 9 : ℝ) ^ t
    oLatSym := fun a => 1 + (1 / 4 : ℝ) * a ^ 2 + a ^ 4
    remSym := fun a => a ^ 4
    oContSym := 1
    c2Sym := 1 / 4
    c4Sym := 1
    aMaxSym := 1
    a0Sym := 1 / 2
    upWil := NonAbelianChiralConstructiveBoundary.su2Cayley (1 / 12 : ℝ) 0 0
    pDob := P_mix
    hpDob := hMix
    piOrb := id
    wInvOrb := fun _ => 0
    phiBerry := fun _ => 0
    gammaLoop := fun _ => ()
    pProj := 1
    d1P := 0
    d2P := 0
    gMat := 1
    gInvMat := 1
    hW := H0
    dHW := dH_ov
    delta0Ov := 1
    etaOv := 1 / 4
    aOv := 1
    gamma5Ov := H0
    vOv := H0
    qIRH2 := id
    oLatH2 := fun _ => 0
    kObsH2 := 1
    cLatH2 := 1
    dTVH2 := 1
    epsExpH2 := 2
    deltaAdvH2 := 1
    nShotsH2 := 1
    z0H2 := 0
    b1RGE := 41 / 10
    b2RGE := -19 / 6
    b3RGE := -7
    db1RGE := 0
    db2RGE := 4
    db3RGE := 4
    c2_1RGE := 0
    c2_2RGE := 0
    c2_3RGE := 0
    dTh1RGE := 0
    dTh2RGE := 0
    dTh3RGE := 0
    aEmInvPDG := 127950 / 1000
    s2WPDG := 23122 / 100000
    alphaSPDG := 1180 / 10000
    tGutMin := 0
    iMinCos := (2829 : ℝ) / 10 ^ 125
    iMaxCos := (2949 : ℝ) / 10 ^ 125
    p0Cos := pBool
    p1Cos := pBool
    hp0Cos := inferInstance
    hp1Cos := inferInstance
    cIRCos := 1
    rRatioCos := 1
    i1Cos := 0
    i2Cos := 0
    deltaAdvCos := 1 / 4
    hwSub := hw
  }
  have hH0_herm : H0ᴴ = H0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [H0]
  have hH0_sq : H0 * H0 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [H0, Matrix.mul_apply, Fin.sum_univ_two]
  have hI_obs : CoreUnitGaugeAndDimensionlessConstants.invariantILambda U0.gravConsts.1 =
      (2888 : ℝ) / 10 ^ 125 := by
    simp [U0, grav, CoreUnitGaugeAndDimensionlessConstants.invariantILambda,
      CoreUnitGaugeAndDimensionlessConstants.planckGaugeSection]
  refine ⟨S, {
    hU := hU_adm
    htSlab := by norm_num
    hmChi := by norm_num
    hgChi := by norm_num
    hg4 := by norm_num
    hQuadThresh := by norm_num
    hvWeyl := by norm_num
    hbianchiCtrl := by
      intro t _
      have h0 : (8 * Real.pi * U0.gravConsts.1.G * (0 : ℝ)) = 0 := by ring
      simpa [S, U0] using (hasDerivWithinAt_const t (Set.Icc (0 : ℝ) 1) (1 : ℝ))
    hContr := {
      alpha_nonneg := by norm_num
      alpha_lt_one := by norm_num
      contract := fun x y => by simp [S, unitIntervalScalarDist]
    }
    hCTail := by norm_num
    hRho := by norm_num
    huInf := rfl
    huN := fun _ => rfl
    htailBanach := fun _ => by simp [S, unitIntervalScalarDist]
    hOSm := fun _ _ => le_refl 0
    hweakOS := fun _ => tendsto_const_nhds
    hSymmOS := by ext i j; simp [S]
    hPSDOS := fun _ => by simp [S]
    hqGNS := fun u => ⟨0, Subsingleton.elim _ u⟩
    hkerGNS := fun _ _ _ => by simp [S]
    hqIRH1 := surjective_id
    hcompH1 := fun _ _ _ => rfl
    hkH1 := by norm_num
    hCuvH1 := by norm_num
    hepsH1 := by norm_num
    hdNNH1 := by norm_num
    hdLeH1 := by
      dsimp [S, U0, grav, CoreUnitGaugeAndDimensionlessConstants.planckGaugeSection]
      norm_num
    hdeltaH1 := by norm_num
    hNH1 := by norm_num
    hhoeffH1 := by norm_num
    hSymmWil := by dsimp [S, T_wil]; rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    hPSDWil := fun v => by
      dsimp [S, T_wil]
      rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_transpose]
      unfold dotProduct
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    huPosWil := by norm_num
    huLtWil := by norm_num
    hcWWil := by norm_num
    hrWil := by norm_num
    hWWil := fun t => by
      dsimp [S]
      rw [one_mul, one_mul, abs_of_nonneg (pow_nonneg (by norm_num) t)]
    haMaxSym := by norm_num
    ha0PosSym := by norm_num
    ha0LeSym := by norm_num
    hOSym := fun _ _ _ => rfl
    hremSym := fun a ha _ => by
      dsimp [S]
      rw [abs_of_nonneg (pow_nonneg (le_of_lt ha) 4), one_mul]
    hUpWil := (NonAbelianChiralConstructiveBoundary.su2Cayley_exact_unitary_and_noncommuting.1
      (1 / 12) 0 0).2
    halphaDob := hDob_lt
    hpiOrb := surjective_id
    hloopOrb := rfl
    hcobOrb := fun _ _ _ => sub_self 0
    hggrOrb := mul_one 1
    hgglOrb := mul_one 1
    hHHerm := hH0_herm
    hdHHerm := by ext i j; fin_cases i <;> fin_cases j <;> simp [S, dH_ov]
    hdelta0Ov := by norm_num
    hetaNN := by norm_num
    hetaLt := by norm_num
    hgapOv := fun v => by
      dsimp [S, ChiralGaugeOverlapClockBridge.l2NormSq]
      rw [Fin.sum_univ_two, Fin.sum_univ_two]
      have hv0 : (H0.mulVec v) 0 = v 0 := by simp [H0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have hv1 : (H0.mulVec v) 1 = -v 1 := by simp [H0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [hv0, hv1, norm_neg, one_pow, one_mul]
    hpertOv := fun v => by
      dsimp [S, ChiralGaugeOverlapClockBridge.l2NormSq]
      rw [Fin.sum_univ_two, Fin.sum_univ_two]
      have hv0 : (dH_ov.mulVec v) 0 = ((1 / 4 : ℝ) : ℂ) * v 0 := by
        simp [dH_ov, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have hv1 : (dH_ov.mulVec v) 1 = ((1 / 4 : ℝ) : ℂ) * v 1 := by
        simp [dH_ov, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [hv0, hv1, norm_mul, norm_mul, Complex.norm_of_nonneg (by norm_num), mul_pow, mul_pow]
      linarith
    haOv := one_ne_zero
    hg5Herm := hH0_herm
    hg5Sq := hH0_sq
    hVHerm := hH0_herm
    hVSq := hH0_sq
    hqIRH2 := surjective_id
    hcompH2 := fun _ _ _ => rfl
    hkH2 := by norm_num
    hClatH2 := by norm_num
    hepsH2 := by norm_num
    hdNNH2 := by norm_num
    hdLeH2 := by
      dsimp [S, U0, grav, CoreUnitGaugeAndDimensionlessConstants.planckGaugeSection]
      norm_num
    hdeltaH2 := by norm_num
    hNH2 := by norm_num
    hhoeffH2 := by norm_num
    haEmLo := by norm_num
    haEmHi := by norm_num
    hs2WLo := by norm_num
    hs2WHi := by norm_num
    haSLo := by norm_num
    haSHi := by norm_num
    hDdbNeg := by
      dsimp [S, CoreUnitGaugeAndDimensionlessConstants.collinearityDefect]
      norm_num
    hDthBd := by
      dsimp [S, CoreUnitGaugeAndDimensionlessConstants.collinearityDefect]
      norm_num
    hiMinPos := by norm_num
    hiMinLe := by norm_num
    hiObsLo := by rw [hI_obs]; norm_num
    hiObsHi := by rw [hI_obs]; norm_num
    hiMaxGt := by norm_num
    hcIRCos := by norm_num
    hrRatioCos := by norm_num
    htvCos := by
      dsimp [S]
      unfold UEOT.V3.TotalVariation.tvDist
      refine csSup_le (UEOT.V3.TotalVariation.tvEventSet_nonempty _ _) ?_
      intro r hr
      rcases hr with ⟨A, _, rfl⟩
      simp
    hgapCos := by norm_num
    hRawFalse := rfl
  }⟩

end CoupledSection

end UEOTPhysicsUnification.CrossSectorPostWave10UnificationSynthesis
