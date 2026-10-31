/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateHeightRecord
public import LeanCanny.Encoding.FlatAffineFrozenLevelRecord

/-! # Frozen levels stabilize as coordinate history grows -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineFrozenLevelRecord
open FlatAffineFullSourceTower
set_option backward.isDefEq.respectTransparency false

theorem flags_freeze (k : ℕ) (r : List Bool) : flags (freeze k r) = if k = 0 then [] else flags r := by
  simp only [freeze, flags, LeanCanny.pairFst_pair]

theorem freeze_freeze (k m : ℕ) (h : k ≤ m) (r : List Bool) : freeze m (freeze k r) = freeze k r := by
  have hl : min (min (Nat.fromBitsLE (left r)) (k - 1)) (m - 1) =
      min (Nat.fromBitsLE (left r)) (k - 1) := by omega
  have hr : min (min (Nat.fromBitsLE (right r)) (k - 1)) (m - 1) =
      min (Nat.fromBitsLE (right r)) (k - 1) := by omega
  conv_lhs => rw [freeze]
  rw [flags_freeze, left_freeze, right_freeze, normal_freeze, constant_freeze, hl, hr]
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte, freeze]
    split_ifs <;> rfl
  · have hm : m ≠ 0 := by omega
    simp only [hm, hk, ↓reduceIte, freeze]

theorem freeze_height (n index ancestor k : ℕ) (hk : ancestor < k) :
    freeze k (CoordinateHeightRecord.height n index ancestor) = CoordinateHeightRecord.height n index ancestor := by
  have hzero : k ≠ 0 := by omega
  simp only [freeze, CoordinateHeightRecord.height, hzero, ↓reduceIte, flags, left, right, normal, constant,
    LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [Nat.min_eq_left (by omega)]
  rfl

theorem freeze_midpoint (n index a b k : ℕ) (ha : a < k) (hb : b < k) :
    freeze k (CoordinateHeightRecord.midpoint n index a b) = CoordinateHeightRecord.midpoint n index a b := by
  have hzero : k ≠ 0 := by omega
  simp only [freeze, CoordinateHeightRecord.midpoint, hzero, ↓reduceIte, flags, left, right, normal, constant,
    LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]

end LeanCanny.Encoding.FlatAffineFrozenLevelRecord
