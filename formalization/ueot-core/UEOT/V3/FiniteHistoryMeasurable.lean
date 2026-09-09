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
    MeasurableSpace (Carrier X A) := by
  unfold Carrier
  infer_instance

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
      (Sigma.mk n)
  refine le_iInf fun n => ?_
  apply MeasurableSpace.comap_le_iff_le_map.1
  rw [MeasurableSpace.comap_comp]
  exact (hf n).comap_le

theorem measurable_time :
    Measurable (Carrier.time : Carrier X A → ℕ) := by
  apply measurable_of_forall_historyFiber
  intro n
  simpa [Carrier.time] using
    (measurable_const : Measurable (fun _ : HistoryFiber X A n => n))

theorem measurable_current :
    Measurable (Carrier.current : Carrier X A → X) := by
  apply measurable_of_forall_historyFiber
  intro n
  simpa [Carrier.current] using
    (measurable_pi_apply (Fin.last n)).comp
      (measurable_fst :
        Measurable
          (fun h : HistoryFiber X A n => h.1))

theorem measurable_singleton :
    Measurable (Carrier.singleton (A := A) : X → Carrier X A) := by
  have hpayload :
      Measurable
        (fun x : X =>
          (((fun _ : Fin 1 => x), (Fin.elim0 : Fin 0 → A)) :
            HistoryFiber X A 0)) := by
    fun_prop
  simpa [Carrier.singleton] using
    (measurable_sigmaMk_history (X := X) (A := A) 0).comp hpayload

end UEOT.V3.FiniteHistoryMeasurable
