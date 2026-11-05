import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionSource

/-!
# Executable observation state and informative receipt counts

The update functions take only their previous public memory, the controller's
own requested action and the delivered birth/payment receipt.  `root` and
`child` are reconstructed physical bits.  The first append can allocate slot1;
later appends never refill a missing slot1.  `fresh` records that distinction.
The separate source module proves this reconstruction against the original
packed and native Store; no reconstruction certificate is an input field.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionObserver

open scoped BigOperators
open RegisterJointDecisionSource

structure Local where
  root : Bool
  child : Option Bool
  stopped : Bool
  fresh : Bool
  deriving DecidableEq, Repr, Fintype

def init (goal : Bool) : Local := ⟨!goal, none, false, true⟩

def selected (q : Local) (j : Bool) : Option Bool :=
  if j then q.child else some q.root

def normalReceipt (goal : Bool) (q : Local) (a : Act) : Obs :=
  let request := effective q.stopped a
  match selected q request.1 with
  | none => (false, false)
  | some bit => (request.2.getD bit == goal, request.2.isSome)

/-- The finite local prediction for a physical mode. The label is irrelevant
to this permitted receipt, while the full native record retains that label. -/
def receipt (goal : Bool) (q : Local) (a : Act) (mode : Bool) : Obs :=
  if mode then normalReceipt goal q a else (false, false)

def normalSeen (o : Obs) : Bool := o.1 || o.2

/-- A tick is informative precisely when its normal receipt differs from its
fault receipt. Missing-slot and damaged-idle zeros are not fault samples. -/
def informative (goal : Bool) (q : Local) (a : Act) : Bool :=
  normalSeen (normalReceipt goal q a)

def bitOfBirth (goal birth : Bool) : Bool := if birth then goal else !goal

def update (goal : Bool) (q : Local) (a : Act) (o : Obs) : Local :=
  let request := effective q.stopped a
  { root := if request.1 then q.root else bitOfBirth goal o.1
    child := if q.fresh then (if o.1 then some goal else none)
      else if request.1 then q.child.map (fun _ => bitOfBirth goal o.1) else q.child
    stopped := q.stopped || a.isNone
    fresh := false }

def successIncrement (goal : Bool) (q : Local) (a : Act) (o : Obs) : ℕ :=
  if informative goal q a && normalSeen o then 1 else 0

def failureIncrement (goal : Bool) (q : Local) (a : Act) (o : Obs) : ℕ :=
  if informative goal q a && !normalSeen o then 1 else 0

structure Stat where
  elapsed : ℕ
  s : ℕ
  f : ℕ
  paidCount : ℕ
  q : Local
  deriving DecidableEq, Repr

def initialStat (goal : Bool) : Stat := ⟨0, 0, 0, 0, init goal⟩

def updateStat (goal : Bool) (st : Stat) (a : Act) (o : Obs) : Stat :=
  { elapsed := st.elapsed + 1
    s := st.s + successIncrement goal st.q a o
    f := st.f + failureIncrement goal st.q a o
    paidCount := st.paidCount + if o.2 then 1 else 0
    q := update goal st.q a o }

abbrev History := List (Act × Obs)

/-- Histories are chronological; no hidden mode, theta, label or Store enters
this fold. The returned statistics are operational controller memory. -/
def summarizeFrom (goal : Bool) (st : Stat) (h : History) : Stat :=
  h.foldl (fun st e => updateStat goal st e.1 e.2) st

def summarize (goal : Bool) (h : History) : Stat := summarizeFrom goal (initialStat goal) h

def compatible (goal : Bool) (q : Local) (a : Act) (o : Obs) : Prop :=
  o = normalReceipt goal q a ∨ o = (false, false)

instance (goal : Bool) (q : Local) (a : Act) (o : Obs) :
    Decidable (compatible goal q a o) := inferInstanceAs
      (Decidable (o = normalReceipt goal q a ∨ o = (false, false)))

/-- Exact marginal receipt probability at fixed persistent normal rate r.
When both modes yield zero the two terms sum to one, rather than recording a
fictional fault. Hidden fair labels have already been summed out. -/
def likelihood (r : ℚ) (goal : Bool) (q : Local) (a : Act) (o : Obs) : ℚ :=
  (if normalReceipt goal q a = o then r else 0) +
    (if (false, false) = o then 1 - r else 0)

@[simp] theorem update_fresh (goal : Bool) (q : Local) (a : Act) (o : Obs) :
    (update goal q a o).fresh = false := rfl

@[simp] theorem update_stopped (goal : Bool) (q : Local) (a : Act) (o : Obs) :
    (update goal q a o).stopped = (q.stopped || a.isNone) := rfl

theorem missing_child_stays_missing (goal : Bool) (q : Local) (a : Act) (o : Obs)
    (hf : q.fresh = false) (hc : q.child = none) :
    (update goal q a o).child = none := by
  simp [update, hf, hc]

theorem first_append_decides_child (goal : Bool) (q : Local) (a : Act) (o : Obs)
    (hf : q.fresh = true) :
    (update goal q a o).child = if o.1 then some goal else none := by
  simp [update, hf]

theorem informative_selected (goal : Bool) (q : Local) (a : Act) :
    informative goal q a =
      match selected q (effective q.stopped a).1 with
      | none => false
      | some bit => (effective q.stopped a).2.isSome || (bit == goal) := by
  unfold informative normalSeen normalReceipt
  cases hs : selected q (effective q.stopped a).1 with
  | none => rfl
  | some bit =>
      cases ha : (effective q.stopped a).2 with
      | none => simp
      | some value => simp

theorem uninformative_receipt (goal : Bool) (q : Local) (a : Act)
    (hi : informative goal q a = false) (mode : Bool) :
    receipt goal q a mode = (false, false) := by
  have hn : normalReceipt goal q a = (false, false) := by
    rcases hn : normalReceipt goal q a with ⟨birth, paid⟩
    cases birth <;> cases paid <;> simp_all [informative, normalSeen]
  cases mode <;> simp [receipt, hn]

theorem informative_receipt_identifies_mode (goal : Bool) (q : Local) (a : Act)
    (hi : informative goal q a = true) (mode : Bool) :
    normalSeen (receipt goal q a mode) = mode := by
  cases mode <;> simp_all [receipt, informative, normalSeen]

theorem increments_le_one (goal : Bool) (q : Local) (a : Act) (o : Obs) :
    successIncrement goal q a o + failureIncrement goal q a o ≤ 1 := by
  cases hi : informative goal q a <;> cases hn : normalSeen o <;>
    simp [successIncrement, failureIncrement, hi, hn]

theorem uninformative_increments (goal : Bool) (q : Local) (a : Act) (o : Obs)
    (hi : informative goal q a = false) :
    successIncrement goal q a o = 0 ∧ failureIncrement goal q a o = 0 := by
  simp [successIncrement, failureIncrement, hi]

theorem likelihood_nonneg (r : ℚ) (hr : 0 ≤ r ∧ r ≤ 1)
    (goal : Bool) (q : Local) (a : Act) (o : Obs) :
    0 ≤ likelihood r goal q a o := by
  unfold likelihood
  split_ifs <;> linarith

theorem likelihood_total (r : ℚ) (goal : Bool) (q : Local) (a : Act) :
    ∑ o : Obs, likelihood r goal q a o = 1 := by
  rcases hn : normalReceipt goal q a with ⟨birth, paid⟩
  cases birth <;> cases paid <;>
    simp [likelihood, hn, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The exact Bernoulli count factor, including impossible observations and
endpoint rates. In particular 0^0=1 is retained when a count is zero. -/
theorem likelihood_counts (r : ℚ) (goal : Bool) (q : Local) (a : Act) (o : Obs) :
    likelihood r goal q a o =
      if compatible goal q a o then
        r ^ successIncrement goal q a o * (1-r) ^ failureIncrement goal q a o
      else 0 := by
  rcases hn : normalReceipt goal q a with ⟨birth, paid⟩
  rcases o with ⟨ob, op⟩
  cases birth <;> cases paid <;> cases ob <;> cases op <;>
    simp [likelihood, compatible, successIncrement, failureIncrement,
      informative, normalSeen, hn]

theorem positive_likelihood_compatible (r : ℚ) (goal : Bool) (q : Local) (a : Act)
    (o : Obs) (hp : 0 < likelihood r goal q a o) : compatible goal q a o := by
  by_contra hc
  rw [likelihood_counts, if_neg hc] at hp
  exact (lt_irrefl 0 hp)

@[simp] theorem summarizeFrom_nil (goal : Bool) (st : Stat) :
    summarizeFrom goal st [] = st := rfl

@[simp] theorem summarizeFrom_cons (goal : Bool) (st : Stat) (a : Act) (o : Obs)
    (h : History) : summarizeFrom goal st ((a, o) :: h) =
      summarizeFrom goal (updateStat goal st a o) h := rfl

theorem summarizeFrom_append (goal : Bool) (st : Stat) (h : History) (a : Act) (o : Obs) :
    summarizeFrom goal st (h ++ [(a,o)]) = updateStat goal (summarizeFrom goal st h) a o := by
  simp [summarizeFrom, List.foldl_append]

theorem summarize_append (goal : Bool) (h : History) (a : Act) (o : Obs) :
    summarize goal (h ++ [(a,o)]) = updateStat goal (summarize goal h) a o :=
  summarizeFrom_append goal (initialStat goal) h a o

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionObserver
