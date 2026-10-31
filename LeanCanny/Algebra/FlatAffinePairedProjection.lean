/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffinePowerAppendPoint
public import LeanCanny.Algebra.BlockRenameCoefficient

/-! # A coordinate projection from two critical samples to one shared tuple

Retain the left sample, append the right sample's newest block, and retain
the left zero coordinate. The original-point power map commutes with this
projection, so the same index program serves native powered samplers.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffinePairedProjection
open FlatAffineCriticalTower FlatAffineCriticalStage FlatAffineTowerRegularity FlatAffinePowerTower
set_option backward.isDefEq.respectTransparency false

def oldCount (n k : ℕ) : ℕ := (k + 1) * width n
def newCount (n k : ℕ) : ℕ := (k + 2) * width n
abbrev oldPositive (n k : ℕ) : ℕ := oldCount n k + 1
abbrev sourceCount (n k : ℕ) : ℕ := oldPositive n k + oldPositive n k

theorem oldCount_eq (n k : ℕ) : oldCount n k = k * width n + width n := Nat.succ_mul _ _
theorem newCount_eq (n k : ℕ) : newCount n k = oldCount n k + width n := Nat.succ_mul _ _

def slot (n k : ℕ) (right : Bool) : Fin (oldPositive n k) → Fin (sourceCount n k) :=
  BlockRenameCoefficient.shift (oldPositive n k) (sourceCount n k) (if right then oldPositive n k else 0)
    (by cases right <;> simp [sourceCount])

theorem slot_val (n k : ℕ) (right : Bool) (i : Fin (oldPositive n k)) :
    (slot n k right i).val = (if right then oldPositive n k else 0) + i.val := rfl

def projection (n k : ℕ) (i : Fin (newCount n k + 1)) : Fin (sourceCount n k) :=
  if h : i.val < oldCount n k then slot n k false ⟨i.val, by unfold oldPositive; omega⟩ else
    if h' : i.val < newCount n k then
      slot n k true ⟨k * width n + (i.val - oldCount n k), by
        have := oldCount_eq n k
        have := newCount_eq n k
        unfold oldPositive
        omega⟩
    else slot n k false (Fin.last (oldCount n k))

theorem projection_val (n k : ℕ) (i : Fin (newCount n k + 1)) :
    (projection n k i).val = if i.val < oldCount n k then i.val else
      if i.val < newCount n k then oldPositive n k + (k * width n + (i.val - oldCount n k)) else oldCount n k := by
  unfold projection
  split_ifs <;> simp [slot_val]

theorem projection_last (n k : ℕ) : projection n k (Fin.last (newCount n k)) = slot n k false (Fin.last (oldCount n k)) := by
  simp only [projection, Fin.val_last]
  rw [dite_eq_right (by have := newCount_eq n k; omega), dite_eq_right (by omega)]

def oldIndex (n k : ℕ) (i : Fin (oldCount n k)) : Fin (newCount n k + 1) :=
  ⟨i.val, by have := i.isLt; have := newCount_eq n k; omega⟩

theorem projection_old (n k : ℕ) (i : Fin (oldCount n k)) : projection n k (oldIndex n k i) = slot n k false i.castSucc := by
  apply Fin.ext
  have hi : (oldIndex n k i).val = i.val := rfl
  rw [projection_val, hi, ite_eq_left i.isLt, slot_val]
  simp only [Bool.false_eq_true, ↓reduceIte, Fin.val_castSucc, Nat.zero_add]

theorem projection_new (n k : ℕ) (v : Variables n) :
    projection n k (TriangularPolynomialRows.block (width n) (k + 1) (k + 2) (by omega) (blockEquiv n v)).castSucc =
      slot n k true (TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n v)).castSucc := by
  have hv := (blockEquiv n v).isLt
  have hc := newCount_eq n k
  have hi : ((TriangularPolynomialRows.block (width n) (k + 1) (k + 2) (by omega) (blockEquiv n v)).castSucc).val =
      oldCount n k + (blockEquiv n v).val := rfl
  apply Fin.ext
  rw [projection_val, hi, ite_eq_right (by omega), ite_eq_left (by omega), slot_val]
  change oldPositive n k + (k * width n + (oldCount n k + (blockEquiv n v).val - oldCount n k)) =
    oldPositive n k + (k * width n + (blockEquiv n v).val)
  omega

variable {K : Type*}

theorem point_projection (n k : ℕ) (z : Fin (sourceCount n k) → K) :
    (fun i : Fin (newCount n k) => z (projection n k i.castSucc)) =
      appendPoint (k + 1) (fun i : Fin (oldCount n k) => z (slot n k false i.castSucc))
        (fun v : Variables n => z (slot n k true
          (TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n v)).castSucc)) := by
  apply append_point_ext (n := n) (k := k + 1)
  · funext i
    exact (congrArg z (projection_old n k i)).trans
      (congrFun (appendPoint_prefix (k + 1) (fun j : Fin (oldCount n k) => z (slot n k false j.castSucc))
        (fun v : Variables n => z (slot n k true
          (TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n v)).castSucc))) i).symm
  · intro v
    exact (congrArg z (projection_new n k v)).trans
      (appendPoint_new (k + 1) (fun j : Fin (oldCount n k) => z (slot n k false j.castSucc))
        (fun w : Variables n => z (slot n k true
          (TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n w)).castSucc)) v).symm

theorem powerPoint_projection [Monoid K] (n k D : ℕ) (z : Fin (sourceCount n k) → K) :
    powerPoint D (fun i : Fin (newCount n k) => z (projection n k i.castSucc)) =
      appendPoint (k + 1) (powerPoint D (fun i : Fin (oldCount n k) => z (slot n k false i.castSucc)))
        (fun v : Variables n => powerPoint D (fun i : Fin (oldCount n k) => z (slot n k true i.castSucc))
          (TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n v))) := by
  have H := congrArg (powerPoint D) (point_projection n k z)
  have HR : blockPower D (fun v : Variables n => z (slot n k true
      (TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n v)).castSucc)) =
      (fun v : Variables n => powerPoint D (fun i : Fin (oldCount n k) => z (slot n k true i.castSucc))
        (TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n v))) := by
    funext v
    exact (powerPoint_block D (fun i : Fin (oldCount n k) => z (slot n k true i.castSucc)) ⟨k, by omega⟩ v).symm
  exact H.trans ((powerPoint_appendPoint D (fun i : Fin (oldCount n k) => z (slot n k false i.castSucc))
    (fun v : Variables n => z (slot n k true
      (TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n v)).castSucc))).trans
      (congrArg (appendPoint (k + 1) (powerPoint D (fun i : Fin (oldCount n k) => z (slot n k false i.castSucc)))) HR))

end LeanCanny.Algebra.FlatAffinePairedProjection
