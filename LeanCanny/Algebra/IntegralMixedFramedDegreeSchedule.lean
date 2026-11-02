/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedScalarOnly

/-! # Actual scalar-only framed rows have the fixed birth-degree schedule -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralHistorySampler
open UniformIntegralPowerSchedule
open scoped Classical
variable {S N m : ℕ} {ι : Type}

def Scheduled (F : Sampler S N m ι) : Prop :=
  ∀ i, F.scalarPrefix.degrees i=N*weights S N m i

theorem base_scheduled (S N : ℕ) : Scheduled (base S N) := fun i=>Fin.elim0 i

theorem scalarStep_scheduled [Fintype ι] (F : Sampler S N m ι) (H : Scheduled F)
    (hm : m≤S) (hN : 0<N) (p : Polynomial F.scalarPrefix.carrier) (d : ℕ) :
    Scheduled (scalarStep F hm hN p d) := by
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · change N*birth S N m=N*weights S N (m+1) 0
    rw [head]
  · change F.scalarPrefix.degrees j=N*weights S N (m+1) j.succ
    rw [old]
    exact H j
end LeanCanny.Algebra.IntegralHistorySampler

namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open IntegralMixedHistory IntegralHistorySampler
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem scheduled_step (x : State P S B m ι) (H : Scheduled x.sampler) (hm : m≤S)
    (c : IntegralMixedFullHistoryScript.Command P B) (hc : c.isCritical=false) :
    Scheduled (IntegralMixedFullHistoryScript.step x hm c).sampler := by
  cases c with
  | integer p hp hd => exact scalarStep_scheduled x.sampler H hm (Nat.two_pow_pos B) _ _
  | critical r => simp only [IntegralMixedFullHistoryScript.Command.isCritical,Bool.true_eq_false] at hc
  | cut r k d hs hd => exact scalarStep_scheduled x.sampler H hm (Nat.two_pow_pos B) _ _

theorem scheduled_run (initial : State P S B 0 ι) (H : Scheduled initial.sampler)
    (cs : List (Instruction n B)) (hcs : cs.length≤S+1)
    (hc : ∀ c∈cs,c.command.isCritical=false) : Scheduled (run initial cs hcs).sampler := by
  induction cs with
  | nil => exact H
  | cons c cs ih =>
    exact scheduled_step (reframe (run initial cs (by simp only [List.length_cons] at hcs; omega))
      c.source c.source_cap) (ih (by simp only [List.length_cons] at hcs; omega)
      (fun d hd=>hc d (List.mem_cons_of_mem c hd))) _ c.command (hc c List.mem_cons_self)

end LeanCanny.Algebra.IntegralMixedFramedHistoryScript
