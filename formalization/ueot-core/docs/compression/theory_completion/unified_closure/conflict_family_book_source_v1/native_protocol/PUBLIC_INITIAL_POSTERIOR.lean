import UEOT
namespace IndependentConflictInitialPosterior
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure UEOT.V3.PathError
open SupportViabilityClosure
open ConflictOrganizationalSource.Posterior
noncomputable section
theorem actual_initial_positive (pi : ObservedPolicy) :
 true∈(coarseLaw initial Prod.fst source pi 0).support :=by
 rw [mem_coarseLaw_zero_support_iff]
 exact ⟨(true,false),by simp [initialSupport,initial]⟩
theorem actual_initial_existing_posterior (pi : ObservedPolicy) :
 (PosteriorSupportCoverageCheck.fiberTerminalPosterior (microLaw initial Prod.fst source pi 0)
 (projectHistory Prod.fst 0) (riskLastState 0) true (actual_initial_positive pi)).support={(true,false)} :=by
 exact (traceSupport_eq_fiberTerminalPosterior_support initial Prod.fst source pi 0 true (actual_initial_positive pi)).symm.trans initial_true_support
end
#print axioms actual_initial_positive
#print axioms actual_initial_existing_posterior
end IndependentConflictInitialPosterior
