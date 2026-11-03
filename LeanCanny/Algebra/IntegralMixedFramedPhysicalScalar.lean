/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
public import LeanCanny.Algebra.IntegralMixedFramedHistoryFamily
/-! # Actual scalar injections into the full physical carrier

The proof follows the actual source-framed interpreter. It preserves the
full carrier, including critical blocks, and supplies the literal column
map needed by tests on complete full-system samples.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
open IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedFramedHistoryScript (Instruction Index)
open LeanCanny.Encoding IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem step_scalar (x : State P S B m ι) (hm : m≤S) (c : Command P B) :
    (IntegralMixedFullHistoryScript.step x hm c).sampler.scalar=
      Fin.cons (fresh c) (fun i=>old c (x.sampler.scalar i)) := by
  cases c <;> rfl

theorem run_scalar (initial : State P S B 0 (Fin 0))
    (cs : List (Instruction n B)) (hcs : cs.length≤S+1) :
    (IntegralMixedFramedHistoryScript.run initial cs hcs).sampler.scalar=scalarSlot cs := by
  induction cs with
  | nil=>funext i; exact Fin.elim0 i
  | cons c cs ih=>
    change (IntegralMixedFullHistoryScript.step _ _ c.command).sampler.scalar=_
    rw [step_scalar]
    change Fin.cons (α:=fun _ : Fin (cs.length+1)=>NextIndex (Index (Fin 0) cs) c.command) (fresh c.command)
      (fun i=>old c.command ((IntegralMixedFramedHistoryScript.run initial cs _).sampler.scalar i))=_
    rw [ih]
    rfl

theorem run_scalar_number (initial : State P S B 0 (Fin 0))
    (cs : List (Instruction n B)) (hcs : cs.length≤S+1) (i : Fin cs.length) :
    (enumerate cs ((IntegralMixedFramedHistoryScript.run initial cs hcs).sampler.scalar i)).val=
      slotNumber cs i.val := by
  rw [run_scalar]
  exact enumerate_scalar cs i

theorem physical_card (cs : List (Instruction n B)) : Fintype.card (Index (Fin 0) cs)=arity cs :=
  (Fintype.card_congr (enumerate cs)).trans (Fintype.card_fin _)

theorem family_scalar (p : Parameters) (d : IntegralMixedFramedHistoryFamilyBits.Plan p)
    (h : IntegralMixedFramedHistoryFamilyBits.Data p d) (key : List Bool) :
    ((IntegralMixedFramedHistoryFamilyBits.family p d h).state key).sampler.scalar=
      scalarSlot (IntegralMixedFramedHistoryFamilyBits.commands p d key) :=
  run_scalar _ _ _
end LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
