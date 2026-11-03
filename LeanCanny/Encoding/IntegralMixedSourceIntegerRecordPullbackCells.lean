/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordControls
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackUnit
/-! # Caller-root affine queries preserve original code and binary row indices

The original saved key is projected; the row index is read from the new task.
It is never clipped by the old task's smaller metadata cap.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCriticalRuleNatural
open IntegralMixedHistory
noncomputable def height {n : ℕ} (r : CriticalRule n) (i : ℕ) : AffineExpr :=
  if hi : i<n+1 then r.heights ⟨i,hi⟩ else .constant 0
noncomputable def scale {n : ℕ} (r : CriticalRule n) (i : ℕ) : ℤ :=
  if hi : i<n+1 then r.scales ⟨i,hi⟩ else 1

theorem height_heq {n m : ℕ} (r : CriticalRule n) (s : CriticalRule m) (hn : n=m) (hr : HEq r s) (i : ℕ) :
    height r i=height s i := by cases hn; cases eq_of_heq hr; rfl

theorem scale_heq {n m : ℕ} (r : CriticalRule n) (s : CriticalRule m) (hn : n=m) (hr : HEq r s) (i : ℕ) :
    scale r i=scale s i := by cases hn; cases eq_of_heq hr; rfl
end LeanCanny.Algebra.IntegralMixedCriticalRuleNatural

namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullback
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (N : List Bool→ℕ) (project : List Bool→List Bool) (extra : List Bool→ℕ)
local notation "PP" => IntegralMixedFramedRootPullback.parameters P project extra

def saved (q : List Bool) := IntegralMixedFramedRootPullback.key project (IntegralMixedVirtualTaskBits.saved PP q)
def rowQuery (q : List Bool) := pair (saved P project extra q) (BinaryNatCode.encode (get PP .slot8 q))

theorem saved_FP (a : Access P) (hp : project∈FP) (he : BinaryFn extra) : saved P project extra∈FP :=
  mem_FP_comp (IntegralMixedVirtualTaskBits.saved_FP PP (IntegralMixedFramedRootPullback.access P a project hp extra he))
    (IntegralMixedFramedRootPullback.key_FP project hp)

theorem rowQuery_FP (a : Access P) (hp : project∈FP) (he : BinaryFn extra) : rowQuery P project extra∈FP :=
  mem_FP_pair (saved_FP P project extra a hp he)
    (get_binary PP (IntegralMixedFramedRootPullback.access P a project hp extra he) .slot8).bits_mem_FP

noncomputable def word (q : List Bool) :=
  if get PP .slot8 q<IntegralMixedOriginalRuleBodyBits.arity PP q then
    IntegralMixedSourceIntegerRecordAppend.rowSyntax P N (decide (get PP .slot15 q=1)) (rowQuery P project extra q)
  else IntegralMixedAffineCode.encode (.constant 0)

noncomputable def mask (physical : Bool) (q : List Bool) :=
  IntegralMixedSourceIntegerRecordAppend.mask P N physical (saved P project extra q)

theorem mask_FP (a : Access P) (hN : UnaryFn N) (hp : project∈FP) (he : BinaryFn extra) (physical : Bool) :
    mask P N project extra physical∈FP :=
  mem_FP_comp (saved_FP P project extra a hp he) (IntegralMixedSourceIntegerRecordAppend.mask_FP P a N hN physical)

attribute [local irreducible] rowQuery IntegralMixedSourceIntegerRecordAppend.rowSyntax

theorem word_FP (a : Access P) (hN : UnaryFn N) (hp : project∈FP) (he : BinaryFn extra) : word P N project extra∈FP := by
  let aa:=IntegralMixedFramedRootPullback.access P a project hp extra he
  have HC := (get_binary PP aa .slot15).eq (BinaryFn.const 1)
  have HB := (get_binary PP aa .slot8).lt (BinaryFn.ofUnary (IntegralMixedOriginalRuleBodyBits.arity_unary PP aa))
  have HT:=mem_FP_comp (rowQuery_FP P project extra a hp he) (IntegralMixedSourceIntegerRecordAppend.rowSyntax_FP P a N hN true)
  have HF:=mem_FP_comp (rowQuery_FP P project extra a hp he) (IntegralMixedSourceIntegerRecordAppend.rowSyntax_FP P a N hN false)
  apply mem_FP_of_eq (HB.ite_mem_FP (HC.ite_mem_FP HT HF) (constFn_mem_FP (IntegralMixedAffineCode.encode (.constant 0))))
  intro q
  simp only [word,Function.comp_apply]
  split_ifs with hi hx <;> simp_all only [decide_true,decide_false]

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullback
