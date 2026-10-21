/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ChineseRemainderDigits
public import LeanCanny.Computation.ArithmeticBitSpace
public import LeanCanny.Computation.SpaceFunctionSelect

/-!
# Composing the final CRT magnitude-digit computation

Bit routines for the full product, inverse-weighted sum, and correction rank,
plus a sign routine, suffice for certified magnitude-digit access. Multiplication,
ordered subtraction, and computed-predicate selection implement the centered
reconstruction expression. These operands remain explicit inputs to this generic
composition; `IntegerDigitSpace` supplies them for the indexed CRT system.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntegerModular

theorem natAbs_eq_ite_residue {M : ℕ} [NeZero M] (z : ℤ) (hz : 2 * z.natAbs < M) :
    z.natAbs = if z < 0 then M - (z : ZMod M).val else (z : ZMod M).val := by
  have he := ZMod.valMinAbs_natAbs_eq_min (z : ZMod M)
  rw [valMinAbs_intCast z hz] at he
  have hv := ZMod.val_lt (z : ZMod M)
  by_cases hn : z < 0
  · have hh := (negative_iff_half_lt_val z hz).mp hn
    have hmin : M - (z : ZMod M).val ≤ (z : ZMod M).val := by omega
    simpa only [hn, ↓reduceIte, min_eq_right hmin] using he
  · have hh : (z : ZMod M).val ≤ M / 2 := by
      by_contra h
      exact hn ((negative_iff_half_lt_val z hz).mpr (by omega))
    have hmin : (z : ZMod M).val ≤ M - (z : ZMod M).val := by omega
    simpa only [hn, ↓reduceIte, min_eq_left hmin] using he

end LeanCanny.Algebra.IntegerModular

namespace LeanCanny.Algebra.ChineseRemainder
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation

theorem magnitudeBitEvaluatorOfOperands
    (N : List Bool → ℕ) (F : (c : List Bool) → System (Fin (N c)))
    (r : (c : List Bool) → Fin (N c) → ℕ) (z : List Bool → ℤ)
    (hres : ∀ c i, (r c i : ZMod ((F c).modulus i)) = z c)
    (hmag : ∀ c, 2 * (z c).natAbs < (F c).product)
    {fs fm fq fn : List Bool → List Bool}
    (ES : SpaceFunction fs) (EM : SpaceFunction fm) (EQ : SpaceFunction fq) (EN : SpaceFunction fn)
    (hsum : ∀ c k, (fs (pair c (BinaryNatCode.encode k)))[0]?.getD false = ((F c).integerSum (r c)).testBit k)
    (hproduct : ∀ c k, (fm (pair c (BinaryNatCode.encode k)))[0]?.getD false = (F c).product.testBit k)
    (hrank : ∀ c k, (fq (pair c (BinaryNatCode.encode k)))[0]?.getD false =
      ((F c).integerSum (r c) / (F c).product).testBit k)
    (hnegative : ∀ c, (fn c)[0]?.getD false = decide (z c < 0)) :
    SpaceFunction (ArithmeticBits.bitValue (fun c => (z c).natAbs)) := by
  let s := fun c => (F c).integerSum (r c)
  let m := fun c => (F c).product
  let q := fun c => s c / m c
  let x := fun c => s c - q c * m c
  have EP := ArithmeticBits.productEvaluator EQ EM q m hrank hproduct
  have hprod := ArithmeticBits.bitValue_packet (fun c => q c * m c)
  have EX : SpaceFunction (ArithmeticBits.bitValue x) :=
    ArithmeticBits.subtractEvaluator ES EP s (fun c => q c * m c) hsum hprod
      (fun c => Nat.div_mul_le_self _ _)
  have hx (c : List Bool) : x c = (z c : ZMod (m c)).val := by
    have he := congrArg ZMod.val ((F c).integerSum_cast_product (r c) (z c) (hres c))
    rw [ZMod.val_natCast, Nat.mod_eq_sub_div_mul] at he
    exact he
  have horder (c : List Bool) : x c ≤ m c := by
    let : NeZero (m c) := ⟨(F c).product_pos.ne'⟩
    rw [hx]
    exact (ZMod.val_lt _).le
  have hbits := ArithmeticBits.bitValue_packet x
  have ER := ArithmeticBits.subtractEvaluator EM EX m x hproduct hbits horder
  let E := (EN.precompose pairFst pairFst_mem_FP).select ER EX
  refine E.congr (funext fun p => ?_)
  have hvalue : (z (pairFst p)).natAbs =
      if z (pairFst p) < 0 then m (pairFst p) - x (pairFst p) else x (pairFst p) := by
    let : NeZero (m (pairFst p)) := ⟨(F (pairFst p)).product_pos.ne'⟩
    rw [IntegerModular.natAbs_eq_ite_residue (z (pairFst p)) (hmag (pairFst p)), ← hx]
  simp only [Function.comp_apply, hnegative, decide_eq_true_eq, ArithmeticBits.bitValue]
  simp only [hvalue]
  by_cases hn : z (pairFst p) < 0 <;> simp [hn]

end LeanCanny.Algebra.ChineseRemainder
