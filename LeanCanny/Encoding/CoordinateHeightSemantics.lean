/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateHeightRecord

/-! # Exact coordinate level semantics in the actual tower decoder -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateHeightRecord
open LeanCanny.Algebra MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def decode (n k : ℕ) (bits : List Bool) : FlatAffineCriticalTower.Level n k ℤ :=
  let a := fun i : Fin n => FlatAffineFullSourceTower.integer 2 (FlatAffineFullSourceTower.normal bits) i.val
  if hk : 0 < k then
    let l : Fin k := ⟨min (Nat.fromBitsLE (FlatAffineFullSourceTower.left bits)) (k - 1), by omega⟩
    let r : Fin k := ⟨min (Nat.fromBitsLE (FlatAffineFullSourceTower.right bits)) (k - 1), by omega⟩
    if FlatAffineFullSourceTower.tag bits = 1 then .height l a
    else if FlatAffineFullSourceTower.tag bits = 2 then .midpoint l r a
    else .constant (FlatAffineFullSourceTower.integer 2 (FlatAffineFullSourceTower.constant bits) 0)
  else .constant (FlatAffineFullSourceTower.integer 2 (FlatAffineFullSourceTower.constant bits) 0)

lemma level_eq_decode (F : FlatAffineFullSourceTower.Inputs) (u : List Bool) (k : ℕ)
    (j : Fin (FlatAffineFullSourceTower.arity F u)) (hW : F.width u = 2) :
    FlatAffineFullSourceTower.level F u k j = decode (FlatAffineFullSourceTower.arity F u) k
      (F.level (FlatAffineFullSourceTower.levelQuery u k j.val)) := by
  unfold FlatAffineFullSourceTower.level decode
  rw [hW]

lemma decode_setActive (n k : ℕ) (bits : List Bool) (active : Bool) :
    decode n k (pair (active :: (FlatAffineFullSourceTower.flags bits).drop 1) (pairSnd bits)) =
      decode n k bits := by
  unfold decode
  simp only [FlatAffineFullSourceTower.flags, FlatAffineFullSourceTower.tag,
    FlatAffineFullSourceTower.left, FlatAffineFullSourceTower.right, FlatAffineFullSourceTower.normal,
    FlatAffineFullSourceTower.constant, pairFst_pair, pairSnd_pair, List.drop_succ_cons, List.drop_zero]

lemma decode_height (n index k : ℕ) (ancestor : Fin k) :
    decode n k (height n index ancestor.val) =
      .height ancestor (fun i => if i.val = index then 2 else 0) := by
  have hk : 0 < k := Nat.zero_lt_of_lt ancestor.isLt
  have hn : (fun i : Fin n => FlatAffineFullSourceTower.integer 2
      (FlatAffineFullSourceTower.normal (height n index ancestor.val)) i.val) =
      (fun i => if i.val = index then 2 else 0) := by
    funext i
    exact height_normal n index ancestor.val i.val i.isLt
  unfold decode
  dsimp only
  rw [dite_eq_left hk, height_tag, ite_eq_left rfl, hn]
  congr 1
  apply Fin.ext
  simp only [height, FlatAffineFullSourceTower.left, pairSnd_pair, pairFst_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact Nat.min_eq_left (by omega)

lemma decode_midpoint (n index k : ℕ) (left right : Fin k) :
    decode n k (midpoint n index left.val right.val) =
      .midpoint left right (fun i => if i.val = index then 1 else 0) := by
  have hk : 0 < k := Nat.zero_lt_of_lt left.isLt
  have hn : (fun i : Fin n => FlatAffineFullSourceTower.integer 2
      (FlatAffineFullSourceTower.normal (midpoint n index left.val right.val)) i.val) =
      (fun i => if i.val = index then 1 else 0) := by
    funext i
    exact midpoint_normal n index left.val right.val i.val i.isLt
  unfold decode
  dsimp only
  rw [dite_eq_left hk, midpoint_tag, ite_eq_right (by decide : (2 : ℕ) ≠ 1), ite_eq_left rfl, hn]
  congr 1
  · apply Fin.ext
    simp only [midpoint, FlatAffineFullSourceTower.left, pairSnd_pair, pairFst_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact Nat.min_eq_left (by omega)
  · apply Fin.ext
    simp only [midpoint, FlatAffineFullSourceTower.right, pairSnd_pair, pairFst_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact Nat.min_eq_left (by omega)

lemma decode_empty (n k : ℕ) : decode n k [] = .constant 0 := by
  have ht : FlatAffineFullSourceTower.tag [] = 0 := rfl
  unfold decode
  dsimp only
  simp only [ht, ite_eq_right (by decide : (0 : ℕ) ≠ 1), ite_eq_right (by decide : (0 : ℕ) ≠ 2)]
  split_ifs <;> rfl

end LeanCanny.Encoding.CoordinateHeightRecord
