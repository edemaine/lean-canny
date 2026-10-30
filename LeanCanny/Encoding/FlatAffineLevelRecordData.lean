/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateAffinePrefix

/-! # Affine level values are independent of their active flag

Coordinate-prefix builders replace only the first flag. The ancestral stage
indices, normal, constant, and level tag are retained exactly. The level
parser therefore gives the same polynomial when the selected objective changes.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineLevelRecordData
open LeanCanny.Algebra
open FlatAffineFullSourceTower
set_option backward.isDefEq.respectTransparency false

abbrev Data := ℕ × List Bool × List Bool × List Bool × List Bool

def data (r : List Bool) : Data := (tag r, left r, right r, normal r, constant r)

noncomputable def decode (n w k : ℕ) (d : Data) : FlatAffineCriticalTower.Level n k ℤ :=
  let a := fun i : Fin n => integer w d.2.2.2.1 i.val
  if hk : 0 < k then
    let l : Fin k := ⟨min (Nat.fromBitsLE d.2.1) (k - 1), by omega⟩
    let h : Fin k := ⟨min (Nat.fromBitsLE d.2.2.1) (k - 1), by omega⟩
    if d.1 = 1 then .height l a else if d.1 = 2 then .midpoint l h a
      else .constant (integer w d.2.2.2.2 0)
  else .constant (integer w d.2.2.2.2 0)

theorem level_eq_data (F : Inputs) (u : List Bool) (k : ℕ) (j : Fin (arity F u)) :
    level F u k j = decode (arity F u) (F.width u) k (data (F.level (levelQuery u k j.val))) := rfl

theorem prefix_data (P : BoundedFullWriter.Readers) (a b : List Bool → ℕ)
    (levels : List Bool → List Bool) (q : List Bool) :
    data (CoordinateAffinePrefix.levels P a levels q) = data (CoordinateAffinePrefix.levels P b levels q) := by
  simp only [data, CoordinateAffinePrefix.levels, CoordinateAffinePrefix.setFlags,
    tag, flags, left, right, normal, constant, pairFst_pair, pairSnd_pair,
    List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]

end LeanCanny.Encoding.FlatAffineLevelRecordData
