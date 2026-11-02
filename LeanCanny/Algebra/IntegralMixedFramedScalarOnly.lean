/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralHistoryScalarOnly
public import LeanCanny.Algebra.IntegralMixedFramedHistoryScript

/-! # Actual scalar-only framed runs in canonical Fin layout

All integer and cut instructions preserve the bijection between retained
scalar slots and physical variables. The explicit inverse has newest-first
order; it also covers the empty run. Critical-point instructions are excluded
because they add genuine extra physical and multiplier variables.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open IntegralMixedHistory IntegralHistorySampler
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem scalarOnly_step (x : State P S B m ι) (H : ScalarOnly x.sampler) (hm : m≤S)
    (c : IntegralMixedFullHistoryScript.Command P B) (hc : c.isCritical=false) :
    ScalarOnly (IntegralMixedFullHistoryScript.step x hm c).sampler := by
  cases c with
  | integer p hp hd => exact scalarStep_scalarOnly x.sampler H hm (Nat.two_pow_pos B) _ _
  | critical r => simp only [IntegralMixedFullHistoryScript.Command.isCritical, Bool.true_eq_false] at hc
  | cut r k d hs hd => exact scalarStep_scalarOnly x.sampler H hm (Nat.two_pow_pos B) _ _

theorem scalarOnly_run (initial : State P S B 0 ι) (H : ScalarOnly initial.sampler)
    (cs : List (Instruction n B)) (hcs : cs.length≤S+1)
    (hc : ∀ c∈cs, c.command.isCritical=false) : ScalarOnly (run initial cs hcs).sampler := by
  induction cs with
  | nil => exact H
  | cons c cs ih =>
    exact scalarOnly_step (reframe (run initial cs (by simp only [List.length_cons] at hcs; omega))
      c.source c.source_cap) (ih (by simp only [List.length_cons] at hcs; omega)
      (fun d hd => hc d (List.mem_cons_of_mem c hd))) _ c.command (hc c (List.mem_cons_self))

noncomputable def scalarVariables (initial : State P S B 0 ι) (H : ScalarOnly initial.sampler)
    (cs : List (Instruction n B)) (hcs : cs.length≤S+1)
    (hc : ∀ c∈cs, c.command.isCritical=false) : Index ι cs ≃ Fin cs.length :=
  (scalarOnly_run initial H cs hcs hc).equiv.symm

@[simp] theorem scalarVariables_scalar (initial : State P S B 0 ι) (H : ScalarOnly initial.sampler)
    (cs : List (Instruction n B)) (hcs : cs.length≤S+1)
    (hc : ∀ c∈cs, c.command.isCritical=false) (i : Fin cs.length) :
    scalarVariables initial H cs hcs hc ((run initial cs hcs).sampler.scalar i)=i :=
  (scalarOnly_run initial H cs hcs hc).equiv.symm_apply_apply i

theorem scalarVariables_rows (initial : State P S B 0 ι) (H : ScalarOnly initial.sampler)
    (cs : List (Instruction n B)) (hcs : cs.length≤S+1)
    (hc : ∀ c∈cs, c.command.isCritical=false) (i : Fin cs.length) :
    PolynomialSystemReindex.system (scalarVariables initial H cs hcs hc)
      (run initial cs hcs).sampler.rows i=(run initial cs hcs).sampler.scalarPrefix.rows i :=
  (scalarOnly_run initial H cs hcs hc).reindexed_rows i

theorem scalarVariables_roots (initial : State P S B 0 ι) (H : ScalarOnly initial.sampler)
    (cs : List (Instruction n B)) (hcs : cs.length≤S+1)
    (hc : ∀ c∈cs, c.command.isCritical=false) {K : Type*} [CommRing K] (z : Fin cs.length→K) :
    (∀ i, ((run initial cs hcs).sampler.scalarPrefix.rows i).eval₂ (Int.castRingHom K) z=0) ↔
    ∀ j, ((run initial cs hcs).sampler.rows j).eval₂ (Int.castRingHom K)
      (z ∘ scalarVariables initial H cs hcs hc)=0 :=
  (scalarOnly_run initial H cs hcs hc).roots_iff z

end LeanCanny.Algebra.IntegralMixedFramedHistoryScript
