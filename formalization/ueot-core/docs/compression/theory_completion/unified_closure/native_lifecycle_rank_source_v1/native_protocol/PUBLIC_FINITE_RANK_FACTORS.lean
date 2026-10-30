import UEOT
namespace IndependentFiniteRankFactor
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
noncomputable section
abbrev Input:=Fin 4→ℝ
abbrev Output:=Fin 3→ℝ

def H : Input →ₗ[ℝ] TwoDriveLatent where
  toFun x:=![2*x 0+x 2,x 1-3*x 3]
  map_add':=by intros;ext i;fin_cases i <;> simp <;> ring
  map_smul':=by intros;ext i;fin_cases i <;> simp <;> ring

def G : TwoDriveLatent →ₗ[ℝ] Output where
  toFun z:=![z 0+z 1,2*z 0-z 1,5*z 1]
  map_add':=by intros;ext i;fin_cases i <;> simp <;> ring
  map_smul':=by intros;ext i;fin_cases i <;> simp <;> ring

def J : Input →ₗ[ℝ] Output:=G.comp H

theorem mixed_response : J ![1,-2,3,4]=![-9,24,-70] :=by
  ext i;fin_cases i <;> norm_num [J,H,G,Matrix.cons_val_two,Matrix.cons_val_three]

theorem H_onto : Function.Surjective H :=by
  intro z
  refine ⟨![0,z 1,z 0,0],?_⟩
  ext i;fin_cases i <;> simp [H,Matrix.cons_val_two,Matrix.cons_val_three]

theorem G_one_to_one : Function.Injective G :=by
  intro z w hh
  have h0:=congrFun hh 0
  have h1:=congrFun hh 1
  change z 0+z 1=w 0+w 1 at h0
  change 2*z 0-z 1=2*w 0-w 1 at h1
  ext i;fin_cases i <;> dsimp <;> linarith

theorem response_rank : Module.finrank ℝ (LinearMap.range J)=2 :=by
  change Module.finrank ℝ (LinearMap.range (G.comp H))=2
  rw [LinearMap.range_comp_of_range_eq_top G (LinearMap.range_eq_top.mpr H_onto),
    LinearMap.finrank_range_of_inj G_one_to_one]
  simp [TwoDriveLatent]

-- Existence is actually obtained FROM rank, not by returning our known H/G.
theorem rank_creates_factor :
    ∃ (E : Input →ₗ[ℝ] TwoDriveLatent) (D : TwoDriveLatent →ₗ[ℝ] Output),
      J=D.comp E ∧ Function.Surjective E ∧ Function.Injective D :=
  rank_two_exists_nondegenerate_factorization J response_rank

theorem arbitrary_factor_nondegenerate (E : Input →ₗ[ℝ] TwoDriveLatent)
    (D : TwoDriveLatent →ₗ[ℝ] Output) (hh : J=D.comp E) :
    Function.Surjective E ∧ Function.Injective D :=rank_two_factorization_nondegenerate J response_rank E D hh

def observed : Matrix (Fin 3) (Fin 4) ℝ:=!![2,1,1,-3;4,-1,2,3;0,5,0,-15]
theorem exact_observed_entries : observed=!![2,1,1,-3;4,-1,2,3;0,5,0,-15] :=rfl

theorem actual_matrix_binding : observed.mulVecLin=J :=by
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i <;>
    norm_num [observed,Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_four,J,H,G,
      Matrix.cons_val_two,Matrix.cons_val_three] <;> ring
theorem observed_rank : observed.rank=2 :=by
  change Module.finrank ℝ (LinearMap.range observed.mulVecLin)=2
  rw [actual_matrix_binding]
  exact response_rank
example : ∃ (E : Input →ₗ[ℝ] TwoDriveLatent) (D : TwoDriveLatent →ₗ[ℝ] Output),observed.mulVecLin=D.comp E :=
  (matrix_rank_le_two_iff_linear_factorization observed).mp observed_rank.le

def S : TwoDriveLatent ≃ₗ[ℝ] TwoDriveLatent:=driveShear (-2/3)
def Hs : Input →ₗ[ℝ] TwoDriveLatent:=S.toLinearMap.comp H
def Gs : TwoDriveLatent →ₗ[ℝ] Output:=G.comp S.symm.toLinearMap
theorem same_actual_response : J=Gs.comp Hs :=by
  ext x i
  simp [J,Hs,Gs,LinearMap.comp_apply]
theorem genuinely_different_encoder : Hs≠H :=by
  intro hh
  have hv:=congrArg (fun K : Input →ₗ[ℝ] TwoDriveLatent=>K ![0,1,0,0] 0) hh
  norm_num [Hs,H,S,driveShear,Matrix.cons_val_two,Matrix.cons_val_three] at hv

theorem old_GL_consumed : ∃! A : TwoDriveLatent ≃ₗ[ℝ] TwoDriveLatent,
    Hs=A.toLinearMap.comp H ∧ Gs=G.comp A.symm.toLinearMap :=
  rank_two_factorizations_unique_gauge J response_rank H Hs G Gs rfl same_actual_response

def intervention (i : Fin 2) : Input:=if i=0 then ![1/2,0,0,0] else ![0,1,0,0]
theorem units_registered : ∀i,H (intervention i)=driveUnitAxis i :=by
  intro i;fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [intervention,H,driveUnitAxis,Matrix.cons_val_two,Matrix.cons_val_three]
theorem sheared_fails_registered_unit : Hs (intervention 1)≠driveUnitAxis 1 :=by
  intro hh
  have hv:=congrFun hh 0
  norm_num [Hs,H,S,driveShear,intervention,driveUnitAxis,Matrix.cons_val_two,Matrix.cons_val_three] at hv

theorem old_anchor_consumed (E : Input →ₗ[ℝ] TwoDriveLatent)
    (D : TwoDriveLatent →ₗ[ℝ] Output) (hh : J=D.comp E)
    (ha : ∀i,E (intervention i)=driveUnitAxis i) : H=E ∧ G=D :=
  rank_two_registered_units_identify J response_rank H E G D rfl hh intervention (fun i=>⟨units_registered i,ha i⟩)

-- Rank0/1 existence includes unused coordinates, with no nondegeneracy claim.
theorem rank_zero_factor : ∃ (E : Input →ₗ[ℝ] TwoDriveLatent) (D : TwoDriveLatent →ₗ[ℝ] Output),
    (0 : Input →ₗ[ℝ] Output)=D.comp E :=
  (finite_rank_le_two_iff_linear_factorization (0 : Input →ₗ[ℝ] Output)).mp (by rw [LinearMap.range_zero];simp)

def H1 : ℝ →ₗ[ℝ] TwoDriveLatent where
  toFun x:=![x,0]
  map_add':=by intros;ext i;fin_cases i <;> simp
  map_smul':=by intros;ext i;fin_cases i <;> simp

def G1 : TwoDriveLatent →ₗ[ℝ] ℝ:=LinearMap.proj 0

theorem rank_one_exact : (LinearMap.id : ℝ →ₗ[ℝ] ℝ)=G1.comp H1 :=by ext;rfl
example : Module.finrank ℝ (LinearMap.range (LinearMap.id : ℝ →ₗ[ℝ] ℝ))=1 :=by rw [LinearMap.range_id];simp
example : ∃ (E : ℝ →ₗ[ℝ] TwoDriveLatent) (D : TwoDriveLatent →ₗ[ℝ] ℝ),
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ)=D.comp E :=
  (finite_rank_le_two_iff_linear_factorization (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).mp (by rw [LinearMap.range_id];simp)
theorem rank_one_not_nondegenerate : ¬Function.Surjective H1 ∧ ¬Function.Injective G1 :=by
  constructor
  · intro hs
    obtain ⟨x,hx⟩:=hs ![0,1]
    have hh:=congrFun hx 1
    norm_num [H1] at hh
  · intro hi
    have hh : G1 ![0,1]=G1 0:=rfl
    have hx:=congrFun (hi hh) 1
    norm_num at hx

-- A different rank3 response, not the author's identity example.
def rankThree : (Fin 3→ℝ) →ₗ[ℝ] (Fin 3→ℝ):=2 • LinearMap.id

theorem rank_three : Module.finrank ℝ (LinearMap.range rankThree)=3 :=by
  have hh : Function.Surjective rankThree :=by
    intro x
    refine ⟨(1/2 : ℝ) • x,?_⟩
    ext i
    simp [rankThree]
  rw [LinearMap.range_eq_top.mpr hh]
  simp

theorem rank_three_no_factor : ¬∃ (E : (Fin 3→ℝ) →ₗ[ℝ] TwoDriveLatent)
    (D : TwoDriveLatent →ₗ[ℝ] (Fin 3→ℝ)),rankThree=D.comp E :=by
  intro h
  have hh:=(finite_rank_le_two_iff_linear_factorization rankThree).mpr h
  rw [rank_three] at hh
  norm_num at hh

def observedThree : Matrix (Fin 3) (Fin 3) ℝ:=LinearMap.toMatrix' rankThree
theorem rank_three_matrix_no_factor : ¬∃ (E : (Fin 3→ℝ) →ₗ[ℝ] TwoDriveLatent)
    (D : TwoDriveLatent →ₗ[ℝ] (Fin 3→ℝ)),observedThree.mulVecLin=D.comp E :=by
  intro h
  have hh:=(matrix_rank_le_two_iff_linear_factorization observedThree).mpr h
  change Module.finrank ℝ (LinearMap.range observedThree.mulVecLin)≤2 at hh
  rw [show observedThree.mulVecLin=rankThree from Matrix.toLin'_toMatrix' rankThree,rank_three] at hh
  norm_num at hh

-- The output need NOT be finite dimensional; the finite input bound suffices.
example (F : (Fin 2→ℝ) →ₗ[ℝ] (ℕ→ℝ)) :
    ∃ (E : (Fin 2→ℝ) →ₗ[ℝ] TwoDriveLatent) (D : TwoDriveLatent →ₗ[ℝ] (ℕ→ℝ)),F=D.comp E :=
  (finite_rank_le_two_iff_linear_factorization F).mp (by simpa using F.finrank_range_le)

#print axioms response_rank
#print axioms rank_creates_factor
#print axioms arbitrary_factor_nondegenerate
#print axioms exact_observed_entries
#print axioms observed_rank
#print axioms old_GL_consumed
#print axioms old_anchor_consumed
#print axioms rank_zero_factor
#print axioms rank_one_not_nondegenerate
#print axioms rank_three_no_factor
#print axioms rank_three_matrix_no_factor
end
end IndependentFiniteRankFactor
