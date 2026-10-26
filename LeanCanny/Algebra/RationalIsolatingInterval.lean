/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalCutSpace
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Rational isolating intervals for an arbitrary finite real root set

This is an existence theorem, without a bit-size estimate. The payload encoding
agrees with the total rational-cut reader used by the native certificate verifier.
-/

@[expose] public section
namespace LeanCanny.Algebra.RationalCutBits
open LeanCanny.Encoding Brackets
open scoped Classical

def payload (q : ℚ) : List Bool :=
  pair (BinaryNatCode.encode q.num.toNat)
    (pair (BinaryNatCode.encode (-q.num).toNat) (BinaryNatCode.encode (q.den - 1)))

theorem threshold_payload (c : List Bool) (q : ℚ) : threshold (pair c (payload q)) = (q : ℝ) := by
  have hn : numerator (pair c (payload q)) = q.num := by
    simp only [numerator, positive, negative, payload, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Int.toNat_sub_toNat_neg]
  have hd : divisor (pair c (payload q)) = q.den := by
    simp only [divisor, denominatorMinusOne, payload, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel q.den_pos]
  simp only [threshold, hn, hd, Rat.cast_def]

theorem exists_isolating_cuts (s : Finset ℝ) (x : ℝ) (hx : x ∈ s) :
    ∃ a b : ℚ, (a : ℝ) < x ∧ x < (b : ℝ) ∧
      s.filter (fun y => y < (a : ℝ)) = s.filter (fun y => y < x) ∧
      s.filter (fun y => y < (b : ℝ)) = insert x (s.filter (fun y => y < x)) := by
  let L := insert (x - 1) (s.filter (fun y => y < x))
  let U := insert (x + 1) (s.filter (fun y => x < y))
  have hL : L.Nonempty := ⟨x - 1, Finset.mem_insert_self _ _⟩
  have hU : U.Nonempty := ⟨x + 1, Finset.mem_insert_self _ _⟩
  have hl : L.max' hL < x := by
    have hm := L.max'_mem hL
    rcases Finset.mem_insert.mp hm with he | he
    · linarith
    · exact (Finset.mem_filter.mp he).2
  have hu : x < U.min' hU := by
    have hm := U.min'_mem hU
    rcases Finset.mem_insert.mp hm with he | he
    · linarith
    · exact (Finset.mem_filter.mp he).2
  obtain ⟨a, hla, hax⟩ := exists_rat_btwn hl
  obtain ⟨b, hxb, hbu⟩ := exists_rat_btwn hu
  refine ⟨a, b, hax, hxb, ?_, ?_⟩
  · ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hy, hya⟩
      exact ⟨hy, hya.trans hax⟩
    · rintro ⟨hy, hyx⟩
      have hym : y ≤ L.max' hL := L.le_max' y (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hy, hyx⟩))
      exact ⟨hy, hym.trans_lt hla⟩
  · ext y
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hy, hyb⟩
      by_cases he : y = x
      · exact Or.inl he
      · right
        refine ⟨hy, ?_⟩
        by_contra hn
        have hxy : x < y := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm he)
        have hym : U.min' hU ≤ y := U.min'_le y (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hy, hxy⟩))
        linarith
    · rintro (rfl | ⟨hy, hyx⟩)
      · exact ⟨hx, hxb⟩
      · exact ⟨hy, hyx.trans hxb⟩

end LeanCanny.Algebra.RationalCutBits
