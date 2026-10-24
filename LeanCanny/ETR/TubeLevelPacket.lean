/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeParameterBounds
public import LeanCanny.Encoding.FixedWidthQuery

/-! # Rational tube parameters with a variable level

A packet stores the source, a unary block width, and three fixed-width
vectors: positive numerator parts, negative numerator parts, and denominator
predecessors. All coordinates are rational constants except the alpha
coordinate, which is the polynomial variable. Denominators are positive
constants, degree is at most one, and coefficient bounds depend on the
stored width. These definitions are total on malformed packets too.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeProjectionEncoding
open scoped Classical

def widthWord (c : List Bool) : List Bool := pairFst (pairSnd c)
def positiveWord (c : List Bool) : List Bool := pairFst (pairSnd (pairSnd c))
def negativeWord (c : List Bool) : List Bool := pairFst (pairSnd (pairSnd (pairSnd c)))
def denominatorWord (c : List Bool) : List Bool := pairSnd (pairSnd (pairSnd (pairSnd c)))
def width (c : List Bool) : ℕ := (widthWord c).length
noncomputable def arity (c : List Bool) : ℕ := TubeParameter.parameterCount (pairFst c)
noncomputable def alphaIndex (c : List Bool) : ℕ := pointCount (TubeIndexed.arity (pairFst c))
def positive (c : List Bool) (i : ℕ) : ℕ := FixedWidthQuery.coordinate width positiveWord c i
def negative (c : List Bool) (i : ℕ) : ℕ := FixedWidthQuery.coordinate width negativeWord c i
def denominatorNat (c : List Bool) (i : ℕ) : ℕ := FixedWidthQuery.coordinate width denominatorWord c i + 1
def integer (c : List Bool) (i : ℕ) : ℤ := (positive c i : ℤ) - negative c i
noncomputable def numerator (c : List Bool) (i : ℕ) : Polynomial ℤ :=
  if i = alphaIndex c then Polynomial.X else Polynomial.C (integer c i)
noncomputable def denominator (c : List Bool) (i : ℕ) : Polynomial ℤ :=
  if i = alphaIndex c then 1 else Polynomial.C (denominatorNat c i : ℤ)

theorem widthWord_mem_FP : widthWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem positiveWord_mem_FP : positiveWord ∈ FP :=
  mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem negativeWord_mem_FP : negativeWord ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairFst_mem_FP
theorem denominatorWord_mem_FP : denominatorWord ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairSnd_mem_FP

theorem width_unary : UnaryFn width := UnaryFn.length widthWord_mem_FP
theorem arity_unary : UnaryFn arity := TubeParameter.parameterCount_unary.comp pairFst_mem_FP
theorem alphaIndex_unary : UnaryFn alphaIndex :=
  (TubeProjectionQuery.pointCount_unary TubeIndexed.arity_unary).comp pairFst_mem_FP

theorem coordinate_lt (target : List Bool → List Bool) (c : List Bool) (i : ℕ) :
    FixedWidthQuery.coordinate width target c i < 2 ^ width c := by
  exact (Nat.fromBitsLE_lt_pow_length _).trans_le
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))

theorem integer_bound (c : List Bool) (i : ℕ) : (integer c i).natAbs ≤ 2 ^ (width c + 1) := by
  have hp := (coordinate_lt positiveWord c i).le
  have hn := (coordinate_lt negativeWord c i).le
  have h := Int.natAbs_sub_le (positive c i : ℤ) (negative c i : ℤ)
  simp only [Int.natAbs_natCast] at h
  apply h.trans
  calc
    _ ≤ 2 ^ width c + 2 ^ width c := Nat.add_le_add hp hn
    _ = _ := by rw [pow_succ, Nat.mul_two]

theorem denominatorNat_bound (c : List Bool) (i : ℕ) : denominatorNat c i ≤ 2 ^ (width c + 1) := by
  exact (Nat.succ_le_of_lt (coordinate_lt denominatorWord c i)).trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))

theorem numerator_degree (c : List Bool) (i : ℕ) : (numerator c i).natDegree ≤ 1 := by
  unfold numerator
  split_ifs <;> simp

theorem denominator_degree (c : List Bool) (i : ℕ) : (denominator c i).natDegree ≤ 1 := by
  unfold denominator
  split_ifs <;> simp

theorem numerator_coeff (c : List Bool) (i k : ℕ) : ((numerator c i).coeff k).natAbs ≤ 2 ^ (width c + 1) := by
  unfold numerator
  split_ifs
  · rw [Polynomial.coeff_X]
    split_ifs <;> simp [Nat.one_le_two_pow]
  · rw [Polynomial.coeff_C]
    split_ifs
    · exact integer_bound c i
    · exact Nat.zero_le _

theorem denominator_coeff (c : List Bool) (i k : ℕ) : ((denominator c i).coeff k).natAbs ≤ 2 ^ (width c + 1) := by
  unfold denominator
  split_ifs
  · rw [Polynomial.coeff_one]
    split_ifs <;> simp [Nat.one_le_two_pow]
  · rw [Polynomial.coeff_C]
    split_ifs
    · simpa only [Int.natAbs_natCast] using denominatorNat_bound c i
    · exact Nat.zero_le _

noncomputable def bounds : TubeParameter.CoordinateBounds pairFst
    (fun c => numerator (pairFst c)) (fun c => denominator (pairFst c)) where
  degree _ := [true]
  bits c := BinaryNatCode.encode (width (pairFst c) + 1)
  degreeFP := constFn_mem_FP _
  bitsFP := bits_mem_FP ((width_unary.comp pairFst_mem_FP).add (UnaryFn.const 1))
  numerator_degree c i _ := numerator_degree (pairFst c) i
  denominator_degree c i _ := denominator_degree (pairFst c) i
  numerator_coeff c i _ k := by simpa only [MacaulayBits.fromBits_encode] using numerator_coeff (pairFst c) i k
  denominator_coeff c i _ k := by simpa only [MacaulayBits.fromBits_encode] using denominator_coeff (pairFst c) i k

theorem denominator_eval_ne_zero {K : Type*} [Field K] [CharZero K] (c : List Bool) (i : ℕ) (t : K) :
    (denominator c i).eval₂ (Int.castRingHom K) t ≠ 0 := by
  unfold denominator
  split_ifs
  · simp
  · simp only [Polynomial.eval₂_C, Int.coe_castRingHom, Int.cast_natCast]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)

end LeanCanny.ETR.TubeLevelPacket
