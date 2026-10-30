/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineLevelRecordData
public import LeanCanny.Algebra.FlatAffineLevelExtension

/-! # Native affine records with frozen ancestral references

Clamp both references at the original stage before copying a level record
into a later stage. At stage zero, force a constant: a height tag ignored by
the original parser must not become active after ancestry is appended.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineFrozenLevelRecord
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower
set_option backward.isDefEq.respectTransparency false

def freeze (k : ℕ) (r : List Bool) : List Bool :=
  pair (if k = 0 then [] else flags r)
    (pair (BinaryNatCode.encode (min (Nat.fromBitsLE (left r)) (k - 1)))
      (pair (BinaryNatCode.encode (min (Nat.fromBitsLE (right r)) (k - 1)))
        (pair (normal r) (constant r))))

theorem freeze_FP {k : List Bool → ℕ} {r : List Bool → List Bool}
    (hk : UnaryFn k) (hr : r ∈ FP) : (fun q => freeze (k q) (r q)) ∈ FP := by
  have hf : (fun q => flags (r q)) ∈ FP := mem_FP_comp hr pairFst_mem_FP
  have hs : (fun q => pairSnd (r q)) ∈ FP := mem_FP_comp hr pairSnd_mem_FP
  have ht : (fun q => pairSnd (pairSnd (r q))) ∈ FP := mem_FP_comp hs pairSnd_mem_FP
  have hu : (fun q => pairSnd (pairSnd (pairSnd (r q)))) ∈ FP := mem_FP_comp ht pairSnd_mem_FP
  have hl : (fun q => left (r q)) ∈ FP := mem_FP_comp hs pairFst_mem_FP
  have hh : (fun q => right (r q)) ∈ FP := mem_FP_comp ht pairFst_mem_FP
  have hn : (fun q => normal (r q)) ∈ FP := mem_FP_comp hu pairFst_mem_FP
  have hc : (fun q => constant (r q)) ∈ FP := mem_FP_comp hu pairSnd_mem_FP
  have hz := (BinaryFn.ofUnary hk).eq (BinaryFn.const 0)
  exact mem_FP_pair (hz.computable.ite_decide (constFn_mem_FP []) hf)
    (mem_FP_pair (BinaryFn.ofUnary (UnaryFn.fromBitsLE_min hl (hk.sub (UnaryFn.const 1)))).bits_mem_FP
      (mem_FP_pair (BinaryFn.ofUnary (UnaryFn.fromBitsLE_min hh (hk.sub (UnaryFn.const 1)))).bits_mem_FP
        (mem_FP_pair hn hc)))

def reader (k : List Bool → ℕ) (r : List Bool → List Bool) (q : List Bool) : List Bool :=
  freeze (k q) (r q)

theorem reader_evaluator {k : List Bool → ℕ} {r : List Bool → List Bool}
    (hk : UnaryFn k) (hr : SpaceFunction r) : SpaceFunction (reader k r) := by
  have H := freeze_FP (hk.comp pairFst_mem_FP) pairSnd_mem_FP
  exact (hr.withInput.postcompose _ H).congr (funext fun q => by
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, reader])

theorem normal_freeze (k : ℕ) (r : List Bool) : normal (freeze k r) = normal r := by
  simp only [freeze, normal, pairSnd_pair, pairFst_pair]

theorem constant_freeze (k : ℕ) (r : List Bool) : constant (freeze k r) = constant r := by
  simp only [freeze, constant, pairSnd_pair]

theorem tag_freeze (k : ℕ) (r : List Bool) :
    tag (freeze k r) = if k = 0 then 0 else tag r := by
  simp only [freeze, tag, flags, pairFst_pair]
  split_ifs <;> rfl

theorem left_freeze (k : ℕ) (r : List Bool) :
    Nat.fromBitsLE (left (freeze k r)) = min (Nat.fromBitsLE (left r)) (k - 1) := by
  simp only [freeze, left, pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem right_freeze (k : ℕ) (r : List Bool) :
    Nat.fromBitsLE (right (freeze k r)) = min (Nat.fromBitsLE (right r)) (k - 1) := by
  simp only [freeze, right, pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem decode_freeze (n w k m : ℕ) (h : k ≤ m) (r : List Bool) :
    FlatAffineLevelRecordData.decode n w m (FlatAffineLevelRecordData.data (freeze k r)) =
      FlatAffineCriticalTower.Level.extend h
        (FlatAffineLevelRecordData.decode n w k (FlatAffineLevelRecordData.data r)) := by
  simp only [FlatAffineLevelRecordData.decode, FlatAffineLevelRecordData.data,
    normal_freeze, constant_freeze, tag_freeze, left_freeze, right_freeze]
  by_cases hk : 0 < k
  · have hm : 0 < m := lt_of_lt_of_le hk h
    have hzero : k ≠ 0 := by omega
    have hl : min (min (Nat.fromBitsLE (left r)) (k - 1)) (m - 1) =
        min (Nat.fromBitsLE (left r)) (k - 1) := by omega
    have hr : min (min (Nat.fromBitsLE (right r)) (k - 1)) (m - 1) =
        min (Nat.fromBitsLE (right r)) (k - 1) := by omega
    simp only [hk, hm, hzero, ↓reduceDIte, ↓reduceIte, hl, hr]
    split_ifs <;> rfl
  · have hz : k = 0 := by omega
    subst k
    simp only [Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte]
    by_cases hm : 0 < m <;> simp [hm, FlatAffineCriticalTower.Level.extend]

end LeanCanny.Encoding.FlatAffineFrozenLevelRecord
