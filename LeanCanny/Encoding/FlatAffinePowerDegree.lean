/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerPositive

/-! # Mixed row degrees of actual positive affine power systems

Degrees are D-1 on gradient rows, D on source rows, and one on every height
and dummy row. The native control depends only on the row position and source
size; active flags and signed records need no metadata oracle.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffinePowerTower
open FlatAffineCriticalTower FlatAffineCriticalStage
open scoped Classical
variable {n k : ℕ}

lemma degree_slot (D : ℕ) (i : Index n k) : degrees D i =
    if i.val % width n < n then D - 1 else if i.val % width n = n then D else 1 := by
  obtain ⟨⟨t, v⟩, rfl⟩ := (rowEquiv n k).surjective i
  rw [degrees_row]
  have hs : (rowEquiv n k (t, v)).val % width n = (blockEquiv n v).val := by
    rw [row_index_eq]
    change (t.val * width n + (blockEquiv n v).val) % width n = (blockEquiv n v).val
    rw [Nat.mul_comm t.val (width n), Nat.mul_add_mod, Nat.mod_eq_of_lt (blockEquiv n v).isLt]
  rw [hs]
  cases v with
  | inl j =>
    change D - 1 = if j.val < n then D - 1 else _
    rw [ite_eq_left j.isLt]
  | inr r =>
    refine Fin.cases ?_ (fun r => ?_) r
    · change D = if n + 0 < n then D - 1 else if n + 0 = n then D else 1
      simp
    · change 1 = if n + (r.val + 1) < n then D - 1 else if n + (r.val + 1) = n then D else 1
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]

end LeanCanny.Algebra.FlatAffinePowerTower

namespace LeanCanny.Encoding.FlatAffinePowerPositive
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineRowLayout FlatAffineRowAccess
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def degree (F : Inputs) (u : List Bool) : Fin (FlatAffineFullSourcePositive.count F u) → ℕ :=
  Fin.lastCases 1 (FlatAffinePowerTower.degrees (n := arity F u) (k := F.depth u) (FlatAffinePowerControls.degree F u))

lemma degree_numeric (F : Inputs) (u : List Bool) (i : Fin (FlatAffineFullSourcePositive.count F u)) : degree F u i =
    if i.val < FlatAffineFullSourceTower.count F u then
      if i.val % FlatAffineFullSourceTower.stageWidth F u < arity F u then FlatAffinePowerControls.degree F u - 1
      else if i.val % FlatAffineFullSourceTower.stageWidth F u = arity F u then FlatAffinePowerControls.degree F u else 1
    else 1 := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [degree, Fin.lastCases_last, Fin.val_last, lt_self_iff_false, ite_false]
  · rw [degree, Fin.lastCases_castSucc]
    simp only [Fin.val_castSucc]
    dsimp +instances only [FlatAffineFullSourceTower.count, FlatAffineFullSourceTower.stageWidth, FlatAffineFullSourceTower.arity, FlatAffinePowerTower.Index] at i ⊢
    rw [ite_eq_left i.isLt]
    exact FlatAffinePowerTower.degree_slot _ i

lemma degree_pos (F : Inputs) (u : List Bool) (i : Fin (FlatAffineFullSourcePositive.count F u)) : 0 < degree F u i := by
  have hD : 1 < FlatAffinePowerControls.degree F u := by
    have h := FlatAffinePowerRowReaders.power_ne_zero F u
    unfold FlatAffinePowerRowReaders.power at h
    omega
  rw [degree_numeric]
  split_ifs <;> omega

theorem degree_unary {F : Inputs} (h : F.Access)
    (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (hr : UnaryFn (fun u => (row u).val)) :
    UnaryFn (fun u => degree F u (row u)) := by
  have hi := BinaryFn.ofUnary (slot_unary h hr)
  have hn := BinaryFn.ofUnary (FlatAffineFullSourceTower.arity_unary h)
  have hd := FlatAffinePowerControls.degree_unary h.source
  have he := UnaryFn.ite (hi.eq hn) hd (UnaryFn.const 1)
  have hl := UnaryFn.ite (hi.lt hn) (hd.sub (UnaryFn.const 1)) he
  have H := UnaryFn.ite (FlatAffineRowSourceReaders.old_FP h hr) hl (UnaryFn.const 1)
  exact H.of_eq (fun u => by
    simpa only [FlatAffineRowSourceReaders.old, slot, index] using (degree_numeric F u (row u)).symm)

end LeanCanny.Encoding.FlatAffinePowerPositive
