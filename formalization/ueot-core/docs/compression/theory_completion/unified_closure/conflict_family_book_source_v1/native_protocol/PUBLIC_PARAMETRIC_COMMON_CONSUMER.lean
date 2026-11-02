import UEOT
namespace IndependentConflictCommon
open MeasureTheory Filter Topology
open UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.AgencyGodGoaAssembly
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.FiniteCesaroInvariant
open ConflictParametricSource ConflictParametricPath ConflictParametricCommonConsumer
noncomputable section
abbrev theta : ℝ:=4/9
theorem h0 : 0≤theta:=by norm_num
theorem h1 : theta≤1:=by norm_num
theorem hs : theta<1:=by norm_num

theorem same_actual_record_stationary_ALLtimes (n : ℕ) :
 (law theta h0 h1 n).map (riskLastState n)=
 ConflictParametricStationary.actualMarginal theta h0 h1 (PMF.pure (true,false)) n :=full_record_stationary_source _ _ _ _
theorem terminal_at_six_not_first_exit :
 (law theta h0 h1 6).toMeasure.real {h|(riskLastState 6 h).1=false}=(4/9:ℝ) :=terminal_damage_probability theta h0 h1 5
theorem same_T2_three_events :
 (law theta h0 h1 2).toMeasure.real {h|¬survives 2 h}=(56/81:ℝ) ∧
 (law theta h0 h1 2).toMeasure.real {h|(riskLastState 2 h).1=false}=(4/9:ℝ) ∧
 (law theta h0 h1 2).toMeasure.real {h|returned h}=(20/81:ℝ) :=by
 rw [actual_first_exit_probability,terminal_damage_probability,two_step_return_probability]
 norm_num [theta]
theorem initial_record_not_stationary :
 (law theta h0 h1 0).map (riskLastState 0)=PMF.pure (true,false) :=by
 change (PMF.pure (true,false) : PMF State).map id=_
 exact PMF.map_id _
theorem endpoint_one_terminal_and_return :
 (law 1 (by norm_num) (by norm_num) 2).toMeasure.real {h|(riskLastState 2 h).1=false}=1 ∧
 (law 1 (by norm_num) (by norm_num) 2).toMeasure.real {h|returned h}=0 :=by
 rw [terminal_damage_probability,two_step_return_probability];norm_num
theorem endpoint_zero_terminal_and_return :
 (law 0 (by norm_num) (by norm_num) 2).toMeasure.real {h|(riskLastState 2 h).1=false}=0 ∧
 (law 0 (by norm_num) (by norm_num) 2).toMeasure.real {h|returned h}=0 :=by
 rw [terminal_damage_probability,two_step_return_probability];norm_num

theorem original_greedy_matrix_AND_original_GOA (q : stdSimplex ℝ State) :
 greedyClosedLoopMatrix M=closedMatrix 1 ∧
 (q∈GreedyInvariantGOASet M ↔ q.val=fun y=>(mu 1 (by norm_num) (by norm_num) y).toReal) :=
 ⟨original_greedy_matrix,original_unrestricted_GOA_iff q⟩
theorem unrestricted_original_GOA_bad :
 lawSimplex (mu 1 (by norm_num) (by norm_num))∈GreedyInvariantGOASet M :=original_unrestricted_GOA_mu_one
theorem unrestricted_actual_GOA_outside (x : State) (hx:x∈(mu 1 (by norm_num) (by norm_num)).support) :
 x.1=false :=original_unrestricted_GOA_outside_safe x hx
theorem intermediate_mixture_NOT_unrestricted_GOA :
 lawSimplex (mu theta h0 h1)∉GreedyInvariantGOASet M :=by
 intro hh
 have he:=congrFun ((original_unrestricted_GOA_iff _).mp hh) (false,true)
 change (mu theta h0 h1 (false,true)).toReal=(mu 1 (by norm_num) (by norm_num) (false,true)).toReal at he
 rw [mu_real,mu_real] at he
 norm_num [theta] at he

theorem original_Cesaro_GOA_ALLtheta (t : ℝ) (a : 0≤t) (b : t≤1) :
 CesaroLimitGOA (ConflictParametricStationary.P t) (ConflictParametricStationary.matrix_stochastic t a b)
 (lawSimplex ConflictParametricStationary.initial) (lawSimplex (mu t a b)) :=original_cesaro_limit_GOA t a b
theorem original_InvariantLawGOA_from_actual_Cesaro_ALLtheta (t : ℝ) (a : 0≤t) (b : t≤1) :
 InvariantLawGOA (ConflictParametricStationary.P t) (ConflictParametricStationary.matrix_stochastic t a b)
 (lawSimplex (mu t a b)) :=
 cesaroLimitGOA_is_invariant _ _ _ _ (original_cesaro_limit_GOA t a b)
theorem original_restricted_GOA_ALLrows (q : stdSimplex ℝ State) :
 q∈GreedyInvariantGOASet ConflictParametricControl.R ↔
 ∃t : ℝ,∃a : 0≤t,∃b : t≤1,q=lawSimplex (mu t a b) :=original_restricted_GOA_all_rows q
theorem intermediate_mixture_IS_restricted_GOA :
 lawSimplex (mu theta h0 h1)∈GreedyInvariantGOASet ConflictParametricControl.R :=
 (original_restricted_GOA_all_rows _).mpr ⟨theta,h0,h1,rfl⟩
theorem original_restricted_safe_delta_Cesaro_unique (q : stdSimplex ℝ State) :
 CesaroLimitGOA (greedyClosedLoopMatrix ConflictParametricControl.R)
 (greedyClosedLoopMatrix_rowStochastic ConflictParametricControl.R)
 (lawSimplex ConflictParametricStationary.initial) q ↔ q=lawSimplex (mu 0 (by norm_num) (by norm_num)) :=
 original_restricted_cesaro_GOA_iff q
theorem safe_original_restricted_GOA_unique (p : PMF State)
 (hp:UEOT.V3.ViabilityKernel.StaysIn p conflictSurvivalRegion)
 (hg:lawSimplex p∈GreedyInvariantGOASet ConflictParametricControl.R) :
 p=mu 0 (by norm_num) (by norm_num) :=original_safe_restricted_GOA_unique p hp hg
theorem nonzero_mixture_is_not_safe :
 ¬UEOT.V3.ViabilityKernel.StaysIn (mu theta h0 h1) conflictSurvivalRegion :=by
 rw [mixture_safe_iff];norm_num [theta]

theorem same_QSD_original_initial : original_safe_initial.map Subtype.val=PMF.pure (true,false) :=original_safe_initial_map
theorem same_QSD_complete_record_ALLhorizons (n : ℕ) :
 law theta h0 h1 n=ConflictParametricQSD.actualLaw theta h0 h1 original_safe_initial n :=same_full_record_qsd_source _ _ _ _
theorem same_QSD_complete_event_ALLrecords (n : ℕ) (h : History n) :
 survives n h ↔ ¬riskEverFailure (fun x=>x∉ConflictParametricQSD.K) n h :=same_original_survival_event n h
theorem fair_safe_subtype_maps_to_real_mu0 :
 ConflictParametricQSD.fairPMF.map Subtype.val=mu 0 (by norm_num) (by norm_num) :=actual_qsd_fair_is_mu_zero
theorem same_actual_fullpath_filter_terminal (n : ℕ) :
 ((law theta h0 hs.le (n+1)).filter {h|survives (n+1) h}
 (survival_supported theta h0 hs (n+1))).map (riskLastState (n+1))=mu 0 (by norm_num) (by norm_num) :=by
 rw [full_conditioned_path_eq_zero_policy theta h0 hs (n+1),actual_terminal_pmf]
end
#print axioms h0
#print axioms h1
#print axioms hs
#print axioms same_actual_record_stationary_ALLtimes
#print axioms terminal_at_six_not_first_exit
#print axioms same_T2_three_events
#print axioms initial_record_not_stationary
#print axioms endpoint_one_terminal_and_return
#print axioms endpoint_zero_terminal_and_return
#print axioms original_greedy_matrix_AND_original_GOA
#print axioms unrestricted_original_GOA_bad
#print axioms unrestricted_actual_GOA_outside
#print axioms intermediate_mixture_NOT_unrestricted_GOA
#print axioms original_Cesaro_GOA_ALLtheta
#print axioms original_InvariantLawGOA_from_actual_Cesaro_ALLtheta
#print axioms original_restricted_GOA_ALLrows
#print axioms intermediate_mixture_IS_restricted_GOA
#print axioms original_restricted_safe_delta_Cesaro_unique
#print axioms safe_original_restricted_GOA_unique
#print axioms nonzero_mixture_is_not_safe
#print axioms same_QSD_original_initial
#print axioms same_QSD_complete_record_ALLhorizons
#print axioms same_QSD_complete_event_ALLrecords
#print axioms fair_safe_subtype_maps_to_real_mu0
#print axioms same_actual_fullpath_filter_terminal
end IndependentConflictCommon
