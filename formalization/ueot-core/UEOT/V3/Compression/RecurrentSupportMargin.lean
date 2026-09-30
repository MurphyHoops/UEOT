import UEOT.V3.Compression.ApproximateRecurrentGaugeStability

/-!
# Recurrent support margins and class-structure lock

Small metric perturbation alone cannot preserve recurrent classes: a zero edge
can become an arbitrarily small positive edge and merge communicating classes.
This module isolates a sufficient support-separation condition under which that
failure mode is impossible.

The key ingredients are:

* every positive one-step transition of both kernels is separated from zero by
  one common margin `gamma`;
* every matrix entry moves by strictly less than `gamma`.

Those hypotheses force equality of the positive-edge support graph.  For
finite stochastic kernels, equality of one-step support then propagates to
every matrix power, finite-step reachability, communication, and recurrent
carriers.
-/

namespace UEOT.V3.Compression.RecurrentSupportMargin

open UEOT.V3
open UEOT.V3.Compression.RecurrentClassGaugeInvariance

universe uS

noncomputable section

variable {S : Type uS} [Fintype S] [DecidableEq S]

/-- Equality of positive one-step transition support. -/
def TransitionSupportEq (P Q : Matrix S S ℝ) : Prop :=
  ∀ x y, 0 < P x y ↔ 0 < Q x y

/-- Inclusion of positive one-step support.  This is the natural relation for
post-bifurcation analysis: source edges may survive while genuinely new target
edges are allowed to appear. -/
def TransitionSupportLe (P Q : Matrix S S ℝ) : Prop :=
  ∀ x y, 0 < P x y → 0 < Q x y

/-- A positive-support margin: every entry is either exactly zero or at least
`gamma`.  This is intentionally stronger than stochasticity and is the
zero-pattern separation needed to prevent tiny new edges. -/
def HasTransitionGap (P : Matrix S S ℝ) (gamma : ℝ) : Prop :=
  ∀ x y, P x y = 0 ∨ gamma ≤ P x y

/-- A structured perturbation preserves source zeros when it never creates a
new positive/probability edge where the source kernel had exactly zero mass. -/
def PreservesZeroSupport (P Q : Matrix S S ℝ) : Prop :=
  ∀ x y, P x y = 0 → Q x y = 0

/-- Two kernels that both have the same positive gap and are entrywise closer
than that gap have identical positive support. -/
theorem transitionSupportEq_of_gap
    (P Q : Matrix S S ℝ) (gamma : ℝ)
    (hgamma : 0 < gamma)
    (hPgap : HasTransitionGap P gamma)
    (hQgap : HasTransitionGap Q gamma)
    (hclose : ∀ x y, |Q x y - P x y| < gamma) :
    TransitionSupportEq P Q := by
  intro x y
  constructor
  · intro hPpos
    rcases hQgap x y with hQzero | hQlarge
    · have hPlarge : gamma ≤ P x y := by
        rcases hPgap x y with hPzero | hPlarge
        · rw [hPzero] at hPpos
          exact (lt_irrefl 0 hPpos).elim
        · exact hPlarge
      have hc := hclose x y
      rw [hQzero, zero_sub, abs_neg, abs_of_pos hPpos] at hc
      exact (not_lt_of_ge hPlarge hc).elim
    · exact hgamma.trans_le hQlarge
  · intro hQpos
    rcases hPgap x y with hPzero | hPlarge
    · have hQlarge : gamma ≤ Q x y := by
        rcases hQgap x y with hQzero | hQlarge
        · rw [hQzero] at hQpos
          exact (lt_irrefl 0 hQpos).elim
        · exact hQlarge
      have hc := hclose x y
      rw [hPzero, sub_zero, abs_of_pos hQpos] at hc
      exact (not_lt_of_ge hQlarge hc).elim
    · exact hgamma.trans_le hPlarge

/-- A more operational one-sided support-lock criterion.  It is enough that the
source positive edges have a margin, source-zero edges remain exactly zero in
the target, and every entry moves by less than the source margin.  No target
positive-gap certificate is needed. -/
theorem transitionSupportEq_of_sourceGap_zeroGuard
    (P Q : Matrix S S ℝ) (gamma : ℝ)
    (hgamma : 0 < gamma)
    (hPgap : HasTransitionGap P gamma)
    (hzero : PreservesZeroSupport P Q)
    (hclose : ∀ x y, |Q x y - P x y| < gamma) :
    TransitionSupportEq P Q := by
  intro x y
  constructor
  · intro hPpos
    have hPlarge : gamma ≤ P x y := by
      rcases hPgap x y with hPzero | hPlarge
      · rw [hPzero] at hPpos
        exact (lt_irrefl 0 hPpos).elim
      · exact hPlarge
    by_contra hQnot
    have hQzero : Q x y = 0 := by
      rcases lt_or_ge 0 (Q x y) with hQpos | hQnonpos
      · exact (hQnot hQpos).elim
      · have hQnonneg : 0 ≤ Q x y := by
          by_contra hneg
          have hneg' : Q x y < 0 := lt_of_not_ge hneg
          have hc := hclose x y
          have hPnonneg : 0 ≤ P x y := hPpos.le
          have : gamma < gamma := by
            calc
              gamma ≤ P x y := hPlarge
              _ < P x y - Q x y := by linarith
              _ = |Q x y - P x y| := by
                rw [abs_of_nonpos]
                · ring
                · linarith
              _ < gamma := hc
          exact (lt_irrefl gamma this).elim
        exact le_antisymm hQnonpos hQnonneg
    have hc := hclose x y
    rw [hQzero, zero_sub, abs_neg, abs_of_pos hPpos] at hc
    exact (not_lt_of_ge hPlarge hc).elim
  · intro hQpos
    rcases hPgap x y with hPzero | hPlarge
    · have hQzero := hzero x y hPzero
      rw [hQzero] at hQpos
      exact (lt_irrefl 0 hQpos).elim
    · exact hgamma.trans_le hPlarge

/-- Source positive edges cannot disappear under a perturbation strictly below
the source positive-edge margin.  No zero-support guard is needed: the target
may create new edges, but every old positive edge survives. -/
theorem transitionSupportLe_of_sourceGap
    (P Q : Matrix S S ℝ)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (gamma : ℝ)
    (hPgap : HasTransitionGap P gamma)
    (hclose : ∀ x y, |Q x y - P x y| < gamma) :
    TransitionSupportLe P Q := by
  intro x y hPpos
  have hPlarge : gamma ≤ P x y := by
    rcases hPgap x y with hPzero | hPlarge
    · rw [hPzero] at hPpos
      exact (lt_irrefl 0 hPpos).elim
    · exact hPlarge
  by_contra hQnot
  have hQzero : Q x y = 0 :=
    le_antisymm (le_of_not_gt hQnot) (hQ.1 x y)
  have hc := hclose x y
  rw [hQzero, zero_sub, abs_neg, abs_of_pos hPpos] at hc
  exact (not_lt_of_ge hPlarge hc).elim

/-- One-step support inclusion propagates to every finite matrix power. -/
theorem pow_pos_mono_of_transitionSupportLe
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportLe P Q) :
    ∀ n x y, 0 < (P ^ n) x y → 0 < (Q ^ n) x y := by
  intro n
  induction n with
  | zero =>
      intro x y hxy
      simpa [Matrix.one_apply] using hxy
  | succ n ih =>
      intro x y hxy
      rw [pow_succ, Matrix.mul_apply] at hxy ⊢
      have hsumP := Finset.sum_pos_iff_of_nonneg
        (s := (Finset.univ : Finset S))
        (f := fun z => (P ^ n) x z * P z y)
        (fun z _ => mul_nonneg
          (Matrix.pow_apply_nonneg hP.1 n x z) (hP.1 z y))
      rcases hsumP.mp hxy with ⟨z, _, hz⟩
      have hPpow : 0 < (P ^ n) x z := by
        by_contra hn
        have hz0 : (P ^ n) x z = 0 :=
          le_antisymm (le_of_not_gt hn) (Matrix.pow_apply_nonneg hP.1 n x z)
        simp [hz0] at hz
      have hPedge : 0 < P z y := by
        by_contra hn
        have hz0 : P z y = 0 :=
          le_antisymm (le_of_not_gt hn) (hP.1 z y)
        simp [hz0] at hz
      have hQterm : 0 < (Q ^ n) x z * Q z y :=
        mul_pos (ih x z hPpow) (hsupp z y hPedge)
      exact Finset.sum_pos'
        (fun u _ => mul_nonneg
          (Matrix.pow_apply_nonneg hQ.1 n x u) (hQ.1 u y))
        ⟨z, Finset.mem_univ z, hQterm⟩

/-- Reachability is monotone under positive-support inclusion. -/
theorem reachable_mono_of_transitionSupportLe
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportLe P Q)
    {x y : S} :
    Reachable P x y → Reachable Q x y := by
  rintro ⟨n, hn⟩
  exact ⟨n, pow_pos_mono_of_transitionSupportLe P Q hP hQ hsupp n x y hn⟩

/-- Communication is monotone under positive-support inclusion.  Hence adding
positive edges can merge communication classes but cannot split an existing
source communication class. -/
theorem communicates_mono_of_transitionSupportLe
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportLe P Q)
    {x y : S} :
    Communicates P x y → Communicates Q x y := by
  rintro ⟨hxy, hyx⟩
  exact ⟨
    reachable_mono_of_transitionSupportLe P Q hP hQ hsupp hxy,
    reachable_mono_of_transitionSupportLe P Q hP hQ hsupp hyx⟩

/-- If a source recurrent carrier remains closed after adding support, then it
remains recurrent: internal communication cannot be lost. -/
theorem recurrentCarrier_of_source_of_targetClosed
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportLe P Q)
    (A : Set S)
    (hrec : RecurrentCarrier P A)
    (hclosedQ : ClosedCarrier Q A) :
    RecurrentCarrier Q A := by
  refine ⟨hrec.1, ?_, hclosedQ⟩
  intro x hx y hy
  exact communicates_mono_of_transitionSupportLe P Q hP hQ hsupp
    (hrec.2.1 hx hy)

/-- **No-splitting theorem for sub-gap perturbations.**  Under a source
positive-edge margin, every pair of source-communicating states remains
communicating in the target.  New support may merge classes, but the old class
cannot split merely by weakening its existing edges. -/
theorem communicates_mono_of_sourceGap
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (gamma : ℝ)
    (hPgap : HasTransitionGap P gamma)
    (hclose : ∀ x y, |Q x y - P x y| < gamma)
    {x y : S} :
    Communicates P x y → Communicates Q x y := by
  exact communicates_mono_of_transitionSupportLe P Q hP hQ
    (transitionSupportLe_of_sourceGap P Q hQ gamma hPgap hclose)

/-- If a source recurrent carrier ceases to be recurrent under a sub-gap
perturbation, the failure is necessarily loss of closedness, witnessed by a new
positive transition from inside the source carrier to outside it.  The source
value of that transition is exactly zero. -/
theorem sourceRecurrent_loss_implies_new_exit_edge
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (gamma : ℝ)
    (hPgap : HasTransitionGap P gamma)
    (hclose : ∀ x y, |Q x y - P x y| < gamma)
    (A : Set S)
    (hrecP : RecurrentCarrier P A)
    (hnotRecQ : ¬ RecurrentCarrier Q A) :
    ∃ x, x ∈ A ∧ ∃ y, y ∉ A ∧ P x y = 0 ∧ 0 < Q x y := by
  have hsupp : TransitionSupportLe P Q :=
    transitionSupportLe_of_sourceGap P Q hQ gamma hPgap hclose
  have hnotClosedQ : ¬ ClosedCarrier Q A := by
    intro hclosedQ
    exact hnotRecQ
      (recurrentCarrier_of_source_of_targetClosed
        P Q hP hQ hsupp A hrecP hclosedQ)
  by_contra hnoExit
  apply hnotClosedQ
  intro x hx y hQxy
  by_contra hy
  have hPxyZero : P x y = 0 := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hPxy
      exact hy (hrecP.2.2 hx y hPxy)
    · exact hP.1 x y
  exact hnoExit ⟨x, hx, y, hy, hPxyZero, hQxy⟩

/-- Positive-probability reachability is transitive for a finite stochastic
kernel: concatenate the two positive-probability path segments. -/
theorem reachable_trans_of_rowStochastic
    (Q : Matrix S S ℝ)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    {x y z : S} :
    Reachable Q x y → Reachable Q y z → Reachable Q x z := by
  rintro ⟨m, hm⟩ ⟨n, hn⟩
  refine ⟨m + n, ?_⟩
  rw [pow_add, Matrix.mul_apply]
  exact Finset.sum_pos'
    (fun u _ => mul_nonneg
      (Matrix.pow_apply_nonneg hQ.1 m x u)
      (Matrix.pow_apply_nonneg hQ.1 n u z))
    ⟨y, Finset.mem_univ y, mul_pos hm hn⟩

/-- Communication is transitive for a finite stochastic kernel. -/
theorem communicates_trans_of_rowStochastic
    (Q : Matrix S S ℝ)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    {x y z : S} :
    Communicates Q x y → Communicates Q y z → Communicates Q x z := by
  rintro ⟨hxy, hyx⟩ ⟨hyz, hzy⟩
  exact ⟨
    reachable_trans_of_rowStochastic Q hQ hxy hyz,
    reachable_trans_of_rowStochastic Q hQ hzy hyx⟩

/-- If two source recurrent carriers each retain all old positive support and
one target state from each carrier communicates with the other, then every
state in their union communicates with every other state in the union.  This
is the abstract merge mechanism before imposing target closedness. -/
theorem union_internalCommunicates_of_cross
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportLe P Q)
    (A B : Set S)
    (hrecA : RecurrentCarrier P A)
    (hrecB : RecurrentCarrier P B)
    {a b : S} (ha : a ∈ A) (hb : b ∈ B)
    (hcross : Communicates Q a b) :
    ∀ ⦃x⦄, x ∈ A ∪ B → ∀ ⦃y⦄, y ∈ A ∪ B → Communicates Q x y := by
  intro x hx y hy
  rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
  · exact communicates_mono_of_transitionSupportLe P Q hP hQ hsupp
      (hrecA.2.1 hxA hyA)
  · have hxa : Communicates Q x a :=
      communicates_mono_of_transitionSupportLe P Q hP hQ hsupp
        (hrecA.2.1 hxA ha)
    have hby : Communicates Q b y :=
      communicates_mono_of_transitionSupportLe P Q hP hQ hsupp
        (hrecB.2.1 hb hyB)
    exact communicates_trans_of_rowStochastic Q hQ
      (communicates_trans_of_rowStochastic Q hQ hxa hcross) hby
  · have hxb : Communicates Q x b :=
      communicates_mono_of_transitionSupportLe P Q hP hQ hsupp
        (hrecB.2.1 hxB hb)
    have hay : Communicates Q a y :=
      communicates_mono_of_transitionSupportLe P Q hP hQ hsupp
        (hrecA.2.1 ha hyA)
    exact communicates_trans_of_rowStochastic Q hQ
      (communicates_trans_of_rowStochastic Q hQ hxb ⟨hcross.2, hcross.1⟩) hay
  · exact communicates_mono_of_transitionSupportLe P Q hP hQ hsupp
      (hrecB.2.1 hxB hyB)

/-- **Recurrent merge theorem.**  Two source recurrent carriers become one
target recurrent carrier whenever (i) old positive support is retained, (ii)
there is target communication across the two carriers, and (iii) their union
is closed in the target. -/
theorem recurrentCarrier_union_of_cross_of_closed
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportLe P Q)
    (A B : Set S)
    (hrecA : RecurrentCarrier P A)
    (hrecB : RecurrentCarrier P B)
    {a b : S} (ha : a ∈ A) (hb : b ∈ B)
    (hcross : Communicates Q a b)
    (hclosed : ClosedCarrier Q (A ∪ B)) :
    RecurrentCarrier Q (A ∪ B) := by
  refine ⟨?_, ?_, hclosed⟩
  · rcases hrecA.1 with ⟨x, hx⟩
    exact ⟨x, Or.inl hx⟩
  · exact union_internalCommunicates_of_cross
      P Q hP hQ hsupp A B hrecA hrecB ha hb hcross

/-- A positive one-step transition is a reachable path of length one. -/
theorem reachable_of_positive_edge
    (Q : Matrix S S ℝ) {x y : S} (hxy : 0 < Q x y) :
    Reachable Q x y := by
  exact ⟨1, by simpa using hxy⟩

/-- Operational merge bridge: one new positive edge in each direction between
two source recurrent carriers is enough to create target cross-communication,
because all old internal communication survives under support inclusion. -/
theorem communicates_cross_of_two_edges
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportLe P Q)
    (A B : Set S)
    (hrecA : RecurrentCarrier P A)
    (hrecB : RecurrentCarrier P B)
    {a₁ a₂ b₁ b₂ : S}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (hAB : 0 < Q a₁ b₁)
    (hBA : 0 < Q b₂ a₂) :
    Communicates Q a₁ b₁ := by
  refine ⟨reachable_of_positive_edge Q hAB, ?_⟩
  have hb₁b₂ : Reachable Q b₁ b₂ :=
    (communicates_mono_of_transitionSupportLe P Q hP hQ hsupp
      (hrecB.2.1 hb₁ hb₂)).1
  have ha₂a₁ : Reachable Q a₂ a₁ :=
    (communicates_mono_of_transitionSupportLe P Q hP hQ hsupp
      (hrecA.2.1 ha₂ ha₁)).1
  exact reachable_trans_of_rowStochastic Q hQ
    (reachable_trans_of_rowStochastic Q hQ hb₁b₂
      (reachable_of_positive_edge Q hBA)) ha₂a₁

/-- Fully operational recurrent merge criterion: retained source support, one
new cross-edge each way, and target closure of the union imply that the two
source recurrent carriers have merged into one target recurrent carrier. -/
theorem recurrentCarrier_union_of_two_edges_of_closed
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportLe P Q)
    (A B : Set S)
    (hrecA : RecurrentCarrier P A)
    (hrecB : RecurrentCarrier P B)
    {a₁ a₂ b₁ b₂ : S}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (hAB : 0 < Q a₁ b₁)
    (hBA : 0 < Q b₂ a₂)
    (hclosed : ClosedCarrier Q (A ∪ B)) :
    RecurrentCarrier Q (A ∪ B) := by
  exact recurrentCarrier_union_of_cross_of_closed
    P Q hP hQ hsupp A B hrecA hrecB ha₁ hb₁
      (communicates_cross_of_two_edges
        P Q hP hQ hsupp A B hrecA hrecB
          ha₁ ha₂ hb₁ hb₂ hAB hBA)
      hclosed

/-- Equality of one-step positive support propagates to every finite matrix
power for nonnegative finite kernels. -/
theorem pow_pos_iff_of_transitionSupportEq
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportEq P Q) :
    ∀ n x y, 0 < (P ^ n) x y ↔ 0 < (Q ^ n) x y := by
  intro n
  induction n with
  | zero =>
      intro x y
      simp [Matrix.one_apply]
  | succ n ih =>
      intro x y
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      have hsumP := Finset.sum_pos_iff_of_nonneg
        (s := (Finset.univ : Finset S))
        (f := fun z => (P ^ n) x z * P z y)
        (fun z _ => mul_nonneg
          (Matrix.pow_apply_nonneg hP.1 n x z) (hP.1 z y))
      have hsumQ := Finset.sum_pos_iff_of_nonneg
        (s := (Finset.univ : Finset S))
        (f := fun z => (Q ^ n) x z * Q z y)
        (fun z _ => mul_nonneg
          (Matrix.pow_apply_nonneg hQ.1 n x z) (hQ.1 z y))
      rw [hsumP, hsumQ]
      constructor
      · rintro ⟨z, _, hz⟩
        have hPpow : 0 < (P ^ n) x z := by
          by_contra hn
          have hz0 : (P ^ n) x z = 0 :=
            le_antisymm (le_of_not_gt hn) (Matrix.pow_apply_nonneg hP.1 n x z)
          simp [hz0] at hz
        have hPedge : 0 < P z y := by
          by_contra hn
          have hz0 : P z y = 0 :=
            le_antisymm (le_of_not_gt hn) (hP.1 z y)
          simp [hz0] at hz
        exact ⟨z, Finset.mem_univ z,
          mul_pos ((ih x z).1 hPpow) ((hsupp z y).1 hPedge)⟩
      · rintro ⟨z, _, hz⟩
        have hQpow : 0 < (Q ^ n) x z := by
          by_contra hn
          have hz0 : (Q ^ n) x z = 0 :=
            le_antisymm (le_of_not_gt hn) (Matrix.pow_apply_nonneg hQ.1 n x z)
          simp [hz0] at hz
        have hQedge : 0 < Q z y := by
          by_contra hn
          have hz0 : Q z y = 0 :=
            le_antisymm (le_of_not_gt hn) (hQ.1 z y)
          simp [hz0] at hz
        exact ⟨z, Finset.mem_univ z,
          mul_pos ((ih x z).2 hQpow) ((hsupp z y).2 hQedge)⟩

/-- Under support equality, finite-step reachability is identical. -/
theorem reachable_iff_of_transitionSupportEq
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportEq P Q)
    (x y : S) :
    Reachable Q x y ↔ Reachable P x y := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (pow_pos_iff_of_transitionSupportEq P Q hP hQ hsupp n x y).2 hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (pow_pos_iff_of_transitionSupportEq P Q hP hQ hsupp n x y).1 hn⟩

/-- Under support equality, communication is identical. -/
theorem communicates_iff_of_transitionSupportEq
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportEq P Q)
    (x y : S) :
    Communicates Q x y ↔ Communicates P x y := by
  simp only [Communicates]
  constructor
  · rintro ⟨hxy, hyx⟩
    exact ⟨
      (reachable_iff_of_transitionSupportEq P Q hP hQ hsupp x y).1 hxy,
      (reachable_iff_of_transitionSupportEq P Q hP hQ hsupp y x).1 hyx⟩
  · rintro ⟨hxy, hyx⟩
    exact ⟨
      (reachable_iff_of_transitionSupportEq P Q hP hQ hsupp x y).2 hxy,
      (reachable_iff_of_transitionSupportEq P Q hP hQ hsupp y x).2 hyx⟩

/-- Closed carriers are identical when one-step positive support is identical. -/
theorem closedCarrier_iff_of_transitionSupportEq
    (P Q : Matrix S S ℝ)
    (hsupp : TransitionSupportEq P Q)
    (A : Set S) :
    ClosedCarrier Q A ↔ ClosedCarrier P A := by
  constructor
  · intro hclosed x hx y hxy
    exact hclosed hx y ((hsupp x y).1 hxy)
  · intro hclosed x hx y hxy
    exact hclosed hx y ((hsupp x y).2 hxy)

/-- Recurrent carriers are locked when the positive support graph is locked. -/
theorem recurrentCarrier_iff_of_transitionSupportEq
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportEq P Q)
    (A : Set S) :
    RecurrentCarrier Q A ↔ RecurrentCarrier P A := by
  constructor
  · rintro ⟨hne, hcomm, hclosed⟩
    refine ⟨hne, ?_, (closedCarrier_iff_of_transitionSupportEq P Q hsupp A).1 hclosed⟩
    intro x hx y hy
    exact (communicates_iff_of_transitionSupportEq P Q hP hQ hsupp x y).1
      (hcomm hx hy)
  · rintro ⟨hne, hcomm, hclosed⟩
    refine ⟨hne, ?_, (closedCarrier_iff_of_transitionSupportEq P Q hsupp A).2 hclosed⟩
    intro x hx y hy
    exact (communicates_iff_of_transitionSupportEq P Q hP hQ hsupp x y).2
      (hcomm hx hy)

/-- The explicit transition-gap hypotheses imply full recurrent-carrier lock. -/
theorem recurrentCarrier_iff_of_gap
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hPgap : HasTransitionGap P gamma)
    (hQgap : HasTransitionGap Q gamma)
    (hclose : ∀ x y, |Q x y - P x y| < gamma)
    (A : Set S) :
    RecurrentCarrier Q A ↔ RecurrentCarrier P A := by
  exact recurrentCarrier_iff_of_transitionSupportEq P Q hP hQ
    (transitionSupportEq_of_gap P Q gamma hgamma hPgap hQgap hclose) A

/-- One-sided sparse-support version of recurrent-carrier lock. -/
theorem recurrentCarrier_iff_of_sourceGap_zeroGuard
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hPgap : HasTransitionGap P gamma)
    (hzero : PreservesZeroSupport P Q)
    (hclose : ∀ x y, |Q x y - P x y| < gamma)
    (A : Set S) :
    RecurrentCarrier Q A ↔ RecurrentCarrier P A := by
  exact recurrentCarrier_iff_of_transitionSupportEq P Q hP hQ
    (transitionSupportEq_of_sourceGap_zeroGuard
      P Q gamma hgamma hPgap hzero hclose) A

/-- Support-margin lock followed by an exact state gauge: a recurrent carrier
of the source is exactly the relabeled recurrent carrier of the physical
target.  `Qaligned` is only a common-coordinate representative used to state
the small perturbation; its relabeling contributes no extra structural error. -/
theorem recurrentCarrier_image_iff_of_gap_gauge
    [Nonempty S]
    (P Qaligned Ptarget : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Qaligned ∈ Matrix.rowStochastic ℝ S)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hPgap : HasTransitionGap P gamma)
    (hQgap : HasTransitionGap Qaligned gamma)
    (hclose : ∀ x y, |Qaligned x y - P x y| < gamma)
    (e : S ≃ S)
    (hconj : ∀ s t, Qaligned s t = Ptarget (e s) (e t))
    (A : Set S) :
    RecurrentCarrier Ptarget (e '' A) ↔ RecurrentCarrier P A := by
  calc
    RecurrentCarrier Ptarget (e '' A) ↔ RecurrentCarrier Qaligned A :=
      recurrentCarrier_image_iff Qaligned Ptarget e hconj A
    _ ↔ RecurrentCarrier P A :=
      recurrentCarrier_iff_of_gap P Qaligned hP hQ
        gamma hgamma hPgap hQgap hclose A

/-- Operational sparse-support lock followed by exact state gauge. -/
theorem recurrentCarrier_image_iff_of_sourceGap_zeroGuard_gauge
    [Nonempty S]
    (P Qaligned Ptarget : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Qaligned ∈ Matrix.rowStochastic ℝ S)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hPgap : HasTransitionGap P gamma)
    (hzero : PreservesZeroSupport P Qaligned)
    (hclose : ∀ x y, |Qaligned x y - P x y| < gamma)
    (e : S ≃ S)
    (hconj : ∀ s t, Qaligned s t = Ptarget (e s) (e t))
    (A : Set S) :
    RecurrentCarrier Ptarget (e '' A) ↔ RecurrentCarrier P A := by
  calc
    RecurrentCarrier Ptarget (e '' A) ↔ RecurrentCarrier Qaligned A :=
      recurrentCarrier_image_iff Qaligned Ptarget e hconj A
    _ ↔ RecurrentCarrier P A :=
      recurrentCarrier_iff_of_sourceGap_zeroGuard
        P Qaligned hP hQ gamma hgamma hPgap hzero hclose A


/-- **Support-changing bifurcation diagnostic.**  Under a positive source-edge
margin and sub-gap entrywise perturbation, recurrent structure cannot change
unless the target creates at least one genuinely new positive edge at a source
zero.  Thus topology change has an explicit finite witness. -/
theorem recurrentCarrier_change_implies_new_positive_edge
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hPgap : HasTransitionGap P gamma)
    (hclose : ∀ x y, |Q x y - P x y| < gamma)
    (A : Set S)
    (hchange : ¬ (RecurrentCarrier Q A ↔ RecurrentCarrier P A)) :
    ∃ x y, P x y = 0 ∧ 0 < Q x y := by
  by_contra hnew
  have hzero : PreservesZeroSupport P Q := by
    intro x y hPzero
    have hQnonneg : 0 ≤ Q x y := hQ.1 x y
    by_contra hQzero
    have hQpos : 0 < Q x y := lt_of_le_of_ne hQnonneg (Ne.symm hQzero)
    exact hnew ⟨x, y, hPzero, hQpos⟩
  exact hchange
    (recurrentCarrier_iff_of_sourceGap_zeroGuard
      P Q hP hQ gamma hgamma hPgap hzero hclose A)

/-- Gauge-covariant bifurcation diagnostic.  If a physical target recurrent
carrier differs from the relabeled source carrier while the aligned target is
sub-gap close to the source, then the aligned target must have created a new
positive edge on source-zero support.  Exact state relabeling itself can never
be the cause of the bifurcation. -/
theorem recurrentCarrier_gauge_change_implies_new_positive_edge
    [Nonempty S]
    (P Qaligned Ptarget : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Qaligned ∈ Matrix.rowStochastic ℝ S)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hPgap : HasTransitionGap P gamma)
    (hclose : ∀ x y, |Qaligned x y - P x y| < gamma)
    (e : S ≃ S)
    (hconj : ∀ s t, Qaligned s t = Ptarget (e s) (e t))
    (A : Set S)
    (hchange :
      ¬ (RecurrentCarrier Ptarget (e '' A) ↔ RecurrentCarrier P A)) :
    ∃ x y, P x y = 0 ∧ 0 < Qaligned x y := by
  have hnotAligned :
      ¬ (RecurrentCarrier Qaligned A ↔ RecurrentCarrier P A) := by
    intro haligned
    apply hchange
    exact (recurrentCarrier_image_iff Qaligned Ptarget e hconj A).trans haligned
  exact recurrentCarrier_change_implies_new_positive_edge
    P Qaligned hP hQ gamma hgamma hPgap hclose A hnotAligned

end

end UEOT.V3.Compression.RecurrentSupportMargin
