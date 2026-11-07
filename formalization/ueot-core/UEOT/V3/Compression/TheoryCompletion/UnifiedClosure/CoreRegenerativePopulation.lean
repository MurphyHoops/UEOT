import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeFeedback

/-!
# Actual identities and marked ancestry on the same regenerative source

The local transaction is exactly `CoreRegenerativeSource.step`; the fixed-program
tree is exactly `CoreRegenerativeFeedback.NoiseTree`.  This wrapper supplies
permanent identity, age, birth time, actual parent pointers and census ancestry.
Retention and strict birth are different marks.  A newborn is returned to the
next recursive census, never executed again in its birth census.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativePopulation

open CoreRegenerativeSource CoreRegenerativeFeedback

structure Identity where
  founder : ℕ
  births : List ℕ
  deriving DecidableEq, Repr

def childIdentity (t : ℕ) (parent : Identity) : Identity :=
  ⟨parent.founder, parent.births ++ [t + 1]⟩

theorem childIdentity_ne (t : ℕ) (parent : Identity) :
    childIdentity t parent ≠ parent := by
  intro h
  have hlen := congrArg (fun x : Identity => x.births.length) h
  simp [childIdentity] at hlen

theorem childIdentity_injective (t : ℕ) : Function.Injective (childIdentity t) := by
  intro x y h
  have hf := congrArg Identity.founder h
  change x.founder = y.founder at hf
  have hb : x.births = y.births := by
    have ha := congrArg Identity.births h
    simpa [childIdentity] using ha
  cases x
  cases y
  simp_all

def ValidIdentity (t : ℕ) (i : Identity) : Prop :=
  ∀ b ∈ i.births, b ≤ t

theorem childIdentity_fresh (t : ℕ) (parent old : Identity)
    (h : ValidIdentity t old) : childIdentity t parent ≠ old := by
  intro he
  have hm : t + 1 ∈ old.births := by
    rw [← he]
    simp [childIdentity]
  have := h (t + 1) hm
  omega

theorem valid_childIdentity (t : ℕ) (parent : Identity)
    (h : ValidIdentity t parent) : ValidIdentity (t + 1) (childIdentity t parent) := by
  intro b hb
  simp only [childIdentity, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact Nat.le_trans (h b hb) (Nat.le_succ t)
  · exact le_rfl

/-- `newborn=false` is same-individual continuation; it is not `OffspringOf`. -/
structure AncestralEdge where
  census : ℕ
  sourceId : Identity
  targetId : Identity
  newborn : Bool
  sourceKind : Kind
  targetKind : Kind
  deriving DecidableEq, Repr

structure Member where
  identity : Identity
  parent : Option Identity
  bornAt : ℕ
  age : ℕ
  body : Body
  ancestry : List AncestralEdge
  deriving DecidableEq, Repr

/-- Every live output capital is the one unit actually debited by `step_budget`. -/
def capital (_ : Member) : ℕ := 1

def founder (index : ℕ) (theta kind tag : Bool) : Member :=
  ⟨⟨index, []⟩, none, 0, 0, programBody theta kind tag, []⟩

def retainedMember (t : ℕ) (old : Member) (status : Status) (body : Body) : Member :=
  { old with
    age := if status = .executed then old.age + 1 else old.age
    body := body
    ancestry := old.ancestry ++
      [⟨t + 1, old.identity, old.identity, false, diagnostic old.body, diagnostic body⟩] }

def newbornMember (t : ℕ) (old : Member) (body : Body) : Member :=
  { identity := childIdentity t old.identity
    parent := some old.identity
    bornAt := t + 1
    age := 0
    body := body
    ancestry := old.ancestry ++
      [⟨t + 1, old.identity, childIdentity t old.identity, true,
        diagnostic old.body, diagnostic body⟩] }

def liftResult (t : ℕ) (old : Member) (r : LocalResult) : List Member :=
  r.retained.toList.map (retainedMember t old r.status) ++
    r.newborn.toList.map (newbornMember t old)

def actualStep (t : ℕ) (old : Member) (a : Action) (z : Noise) : List Member :=
  liftResult t old (step old.body a z)

theorem retained_identity (t : ℕ) (old : Member) (status : Status) (body : Body) :
    (retainedMember t old status body).identity = old.identity ∧
    (retainedMember t old status body).parent = old.parent ∧
    (retainedMember t old status body).bornAt = old.bornAt := by
  exact ⟨rfl, rfl, rfl⟩

theorem newborn_actual_parent (t : ℕ) (old : Member) (body : Body) :
    (newbornMember t old body).parent = some old.identity ∧
    (newbornMember t old body).identity ≠ old.identity ∧
    (newbornMember t old body).bornAt = t + 1 ∧
    (newbornMember t old body).age = 0 := by
  exact ⟨rfl, childIdentity_ne t old.identity, rfl, rfl⟩

theorem newborn_fresh_from_old_population (t : ℕ) (old : Member) (body : Body)
    (population : List Member)
    (hvalid : ∀ m ∈ population, ValidIdentity t m.identity) :
    ∀ m ∈ population, (newbornMember t old body).identity ≠ m.identity := by
  intro m hm
  exact childIdentity_fresh t old.identity m.identity (hvalid m hm)

theorem liftResult_length (t : ℕ) (old : Member) (r : LocalResult) :
    (liftResult t old r).length = outputCapital r := by
  cases hr : r.retained <;> cases hb : r.newborn <;>
    simp [liftResult, outputCapital, optionCount, hr, hb]

theorem actualStep_length_le_two (t : ℕ) (old : Member) (a : Action) (z : Noise) :
    (actualStep t old a z).length ≤ 2 := by
  rw [actualStep, liftResult_length]
  exact outputCapital_le_two _

theorem actualStep_budget (t : ℕ) (old : Member) (a : Action) (z : Noise) :
    (step old.body a z).repairPaid + (step old.body a z).operationPaid +
      (actualStep t old a z).length + (step old.body a z).refund = capital old + 5 := by
  simpa [actualStep, liftResult_length, capital] using step_budget old.body a z

/-- The tree traverses the actual two output slots, including death as `none`. -/
def descendants : (T : ℕ) → ℕ → Member → NoiseTree T → List Member
  | 0, _, old, _ => [old]
  | T + 1, t, old, w =>
    let r := programStep old.body w.1
    (match r.retained with
      | none => []
      | some body => descendants T (t + 1) (retainedMember t old r.status body) w.2.1) ++
    (match r.newborn with
      | none => []
      | some body => descendants T (t + 1) (newbornMember t old body) w.2.2)

/-- The count used by the feedback law is exactly the count of actual records. -/
theorem descendants_length (T t : ℕ) (old : Member) (w : NoiseTree T) :
    (descendants T t old w).length = treeCount T old.body w := by
  induction T generalizing t old with
  | zero => rfl
  | succ T ih =>
    simp only [descendants, treeCount, List.length_append]
    generalize programStep old.body w.1 = r
    cases hr : r.retained <;> cases hb : r.newborn <;>
      simp [optionValue, ih, retainedMember, newbornMember]

def bodyPath (initial : Kind) (m : Member) : List Kind :=
  initial :: m.ancestry.map AncestralEdge.targetKind

def markedPath (m : Member) : List (Bool × Kind) :=
  m.ancestry.map (fun e => (e.newborn, e.targetKind))

/-- Every appended ancestral edge is sourced by the actual old identity. -/
theorem actual_edge_provenance (t : ℕ) (old : Member) (status : Status) (body : Body) :
    (retainedMember t old status body).ancestry = old.ancestry ++
      [⟨t + 1, old.identity, old.identity, false, diagnostic old.body, diagnostic body⟩] ∧
    (newbornMember t old body).ancestry = old.ancestry ++
      [⟨t + 1, old.identity, childIdentity t old.identity, true,
        diagnostic old.body, diagnostic body⟩] := by
  exact ⟨rfl, rfl⟩

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativePopulation
