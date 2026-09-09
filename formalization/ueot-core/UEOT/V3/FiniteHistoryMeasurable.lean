import UEOT.V3.FiniteHistory
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# P-PROC-01 measurable finite-history carrier

This module equips the exact growing-history carrier with the canonical
Sigma measurable structure inherited from its finite-dimensional fibers.

The key reusable result is a branchwise criterion: a function out of the
history carrier is measurable once its restriction to every fixed-time
fiber is measurable.  This is the correct measurable analogue of
Z_t = (t,H_t), without imposing a finite-memory assumption.
-/

namespace UEOT.V3.FiniteHistoryMeasurable

open UEOT.V3.FiniteHistory
open MeasurableSpace

universe uX uA uY

variable {X : Type uX} {A : Type uA} {Y : Type uY}
variable [MeasurableSpace X] [MeasurableSpace A]


@[instance_reducible] instance instMeasurableSpaceHistoryFiber (n : ℕ) :
    MeasurableSpace (HistoryFiber X A n) := by
  unfold HistoryFiber
  infer_instance

@[instance_reducible] instance instMeasurableSpaceCarrier :
    MeasurableSpace (Carrier X A) :=
  ⨅ n, (instMeasurableSpaceHistoryFiber (X := X) (A := A) n).map
    (fun h : HistoryFiber X A n => (⟨n, h⟩ : Carrier X A))

theorem measurable_sigmaMk_history (n : ℕ) :
    Measurable
      (fun h : HistoryFiber X A n =>
        (⟨n, h⟩ : Carrier X A)) := by
  apply Measurable.of_le_map
  exact iInf_le _ n

theorem measurable_of_forall_historyFiber
    [MeasurableSpace Y]
    (f : Carrier X A → Y)
    (hf : ∀ n, Measurable (fun h : HistoryFiber X A n => f ⟨n, h⟩)) :
    Measurable f := by
  rw [measurable_iff_comap_le]
  change _ ≤
    ⨅ n, (inferInstance : MeasurableSpace (HistoryFiber X A n)).map
      (fun h : HistoryFiber X A n => (⟨n, h⟩ : Carrier X A))
  refine le_iInf fun n => ?_
  apply MeasurableSpace.comap_le_iff_le_map.1
  change
    MeasurableSpace.comap
        (fun h : HistoryFiber X A n => (⟨n, h⟩ : Carrier X A))
        (MeasurableSpace.comap f (inferInstance : MeasurableSpace Y)) ≤
      (inferInstance : MeasurableSpace (HistoryFiber X A n))
  rw [MeasurableSpace.comap_comp]
  exact (hf n).comap_le

theorem measurable_time :
    Measurable (Carrier.time : Carrier X A → ℕ) := by
  apply measurable_of_forall_historyFiber
  intro n
  simpa [Carrier.time] using
    (measurable_const : Measurable (fun _ : HistoryFiber X A n => n))

theorem measurable_historyFiber_states (n : ℕ) :
    Measurable (fun h : HistoryFiber X A n => h.1) := by
  unfold HistoryFiber
  exact measurable_fst

theorem measurable_historyFiber_actions (n : ℕ) :
    Measurable (fun h : HistoryFiber X A n => h.2) := by
  unfold HistoryFiber
  exact measurable_snd

theorem measurable_current :
    Measurable (Carrier.current : Carrier X A → X) := by
  apply measurable_of_forall_historyFiber
  intro n
  change Measurable (fun h : HistoryFiber X A n => h.1 (Fin.last n))
  unfold HistoryFiber
  exact (measurable_pi_apply (Fin.last n)).comp measurable_fst

theorem measurable_singleton :
    Measurable (Carrier.singleton (A := A) : X → Carrier X A) := by
  have hpayload :
      Measurable
        (fun x : X =>
          (((fun _ : Fin 1 => x), (Fin.elim0 : Fin 0 → A)) :
            HistoryFiber X A 0)) := by
    fun_prop
  change Measurable
    (fun x : X =>
      (⟨0, ((fun _ : Fin 1 => x), (Fin.elim0 : Fin 0 → A))⟩ :
        Carrier X A))
  exact (measurable_sigmaMk_history (X := X) (A := A) 0).comp hpayload


/-- Appending one action and one state to a fixed-time history fiber is
measurable.  This is the local measurable transition map needed to realize the
source augmented state `Z_t = (t,H_t)`. -/
theorem measurable_advance_fixed (n : ℕ) :
    Measurable
      (fun p : (HistoryFiber X A n × A) × X =>
        Carrier.advance
          (⟨n, p.1.1⟩ : Carrier X A) p.1.2 p.2) := by
  have hstates :
      Measurable
        (fun p : (HistoryFiber X A n × A) × X =>
          (Fin.snoc p.1.1.1 p.2 : Fin (n + 2) → X)) := by
    rw [measurable_pi_iff]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using
        (measurable_snd :
          Measurable (fun p : (HistoryFiber X A n × A) × X => p.2))
    · have hh :
          Measurable
            (fun p : (HistoryFiber X A n × A) × X => p.1.1.1) :=
        (measurable_historyFiber_states (X := X) (A := A) n).comp
          (measurable_fst.comp measurable_fst)
      simpa only [Fin.snoc_castSucc, Function.comp_def] using
        (measurable_pi_apply j).comp hh
  have hactions :
      Measurable
        (fun p : (HistoryFiber X A n × A) × X =>
          (Fin.snoc p.1.1.2 p.1.2 : Fin (n + 1) → A)) := by
    rw [measurable_pi_iff]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last, Function.comp_def] using
        (measurable_snd.comp measurable_fst :
          Measurable (fun p : (HistoryFiber X A n × A) × X => p.1.2))
    · have hh :
          Measurable
            (fun p : (HistoryFiber X A n × A) × X => p.1.1.2) :=
        (measurable_historyFiber_actions (X := X) (A := A) n).comp
          (measurable_fst.comp measurable_fst)
      simpa only [Fin.snoc_castSucc, Function.comp_def] using
        (measurable_pi_apply j).comp hh
  have hpayload :
      Measurable
        (fun p : (HistoryFiber X A n × A) × X =>
          ((Fin.snoc p.1.1.1 p.2, Fin.snoc p.1.1.2 p.1.2) :
            HistoryFiber X A (n + 1))) :=
    hstates.prodMk hactions
  change Measurable
    (fun p : (HistoryFiber X A n × A) × X =>
      (⟨n + 1,
        ((Fin.snoc p.1.1.1 p.2, Fin.snoc p.1.1.2 p.1.2) :
          HistoryFiber X A (n + 1))⟩ : Carrier X A))
  exact (measurable_sigmaMk_history (X := X) (A := A) (n + 1)).comp hpayload

end UEOT.V3.FiniteHistoryMeasurable
