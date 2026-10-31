import UEOT
namespace UEOTFiniteTerminalPolicyScope
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultControlModel
noncomputable section
abbrev port : Fin 1:=0
theorem eps_ok : (1/4 : NNReal)≤1 :=by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)
def mech : Mechanism:=⟨true,11/5⟩
def damaged : State 1:=fun _=>false
theorem compiled_terminal_payoff :
    expectedModePayoff port (PMF.pure false) mech (1/2) (1/4) eps_ok
      damaged (interpret (compile port true) damaged)= -3/40 :=by
  rw [expectedModePayoff_eq]
  simp only [stage,expectedChildren_eq]
  norm_num [mech,damaged,compile,interpret,update,cost,repairChance]
theorem idle_terminal_payoff :
    expectedModePayoff port (PMF.pure false) mech (1/2) (1/4) eps_ok
      damaged (interpret (.emit none) damaged)=0 :=by
  rw [expectedModePayoff_eq]
  simp only [stage,expectedChildren_eq]
  norm_num [mech,damaged,interpret,update,cost,repairChance]
theorem compiled_terminal_strictly_worse :
    expectedModePayoff port (PMF.pure false) mech (1/2) (1/4) eps_ok
      damaged (interpret (compile port true) damaged)<
    expectedModePayoff port (PMF.pure false) mech (1/2) (1/4) eps_ok
      damaged (interpret (.emit none) damaged) :=by
  rw [compiled_terminal_payoff,idle_terminal_payoff]
  norm_num
#print axioms compiled_terminal_payoff
#print axioms idle_terminal_payoff
#print axioms compiled_terminal_strictly_worse
end
end UEOTFiniteTerminalPolicyScope
