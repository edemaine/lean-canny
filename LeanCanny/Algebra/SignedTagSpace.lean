/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.InfinitesimalSignSpace
public import LeanCanny.Encoding.BinaryDivFP

/-! # FP parity correction of three-way integer sign tags -/

@[expose] public section

namespace LeanCanny.Algebra.SignedTagBits
open Complexity LeanCanny.Encoding
open LeanCanny.Encoding.Brackets

def flip (w : List Bool) : List Bool := if w = [] then [] else if w = [true] then [false, true] else [true]

theorem flip_mem_FP : flip ∈ FP := by
  have ht := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).ite_mem_FP (constFn_mem_FP [false, true]) (constFn_mem_FP [true])
  have h := (stringEq_fppred id_mem_FP (constFn_mem_FP [])).ite_mem_FP (constFn_mem_FP []) ht
  exact mem_FP_of_eq (g := flip) h (fun _ => rfl)

theorem flip_tag (a : ℤ) : flip (InfinitesimalSign.tag a) = InfinitesimalSign.tag (-a) := by
  by_cases hz : a = 0
  · simp [hz, flip, InfinitesimalSign.tag]
  · by_cases hn : a < 0 <;> simp [flip, InfinitesimalSign.tag, hz, hn]
    all_goals omega

def correct (p : List Bool) : List Bool :=
  if BinaryNat.mod (pair (pairFst p) [false, true]) = [] then pairSnd p else flip (pairSnd p)

theorem correct_mem_FP : correct ∈ FP := by
  have hp := mem_FP_comp (mem_FP_pair pairFst_mem_FP (constFn_mem_FP [false, true])) BinaryNat.mod_mem_FP
  have h := (stringEq_fppred hp (constFn_mem_FP [])).ite_mem_FP pairSnd_mem_FP (mem_FP_comp pairSnd_mem_FP flip_mem_FP)
  exact mem_FP_of_eq (g := correct) h (fun _ => by simp only [correct, Function.comp_apply])

theorem correct_pair (n : ℕ) (a : ℤ) :
    correct (pair (BinaryNatCode.encode n) (InfinitesimalSign.tag a)) = InfinitesimalSign.tag ((-1 : ℤ) ^ n * a) := by
  simp only [correct, pairFst_pair, pairSnd_pair, BinaryNat.mod_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, BinaryNat.bits_eq_nil_iff]
  change (if n % 2 = 0 then _ else _) = _
  rw [neg_one_pow_eq_pow_mod_two]
  by_cases he : n % 2 = 0
  · simp [he]
  · have ho : n % 2 = 1 := by have h := Nat.mod_lt n (by decide : 0 < 2); omega
    simp only [ho, Nat.one_ne_zero, ite_false, pow_one, neg_one_mul, flip_tag]

end LeanCanny.Algebra.SignedTagBits
