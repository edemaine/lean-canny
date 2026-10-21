/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PreprocessedPair

/-! # Degree and separability of a preprocessed primitive pair -/

@[expose] public section

namespace LeanCanny.Algebra.PreprocessedPair
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)

theorem reduced_degree_le (F : Family) (c : List Bool) (hp : F.polynomial c ≠ 0) :
    (reduced F c).natDegree ≤ (F.polynomial c).natDegree := by
  have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  rw [reduced, ScaledSquarefree.polynomial_natDegree _ hp,
    SquarefreePart.part_natDegree _ ((Polynomial.map_ne_zero_iff hi).mpr hp),
    natDegree_map_eq_of_injective hi]
  exact Nat.sub_le _ _

variable (F G : Family) (A : Readers F) (B : Readers G)
variable (hF : ∀ c, F.polynomial c ≠ 0) (hG : ∀ c, G.polynomial c ≠ 0)

theorem parameter_degree (c : List Bool) :
    (parameter F G A B hF hG c).natDegree = (reduced F c).natDegree * (reduced G c).natDegree :=
  PrimitivePair.resultant_natDegree _ _ _
    (ScaledSquarefree.separable_in_field (L := AlgebraicClosure ℚ) _ (hF c))
    (ScaledSquarefree.separable_in_field (L := AlgebraicClosure ℚ) _ (hG c))
    (IsAlgClosed.splits _) (IsAlgClosed.splits _)

theorem parameter_degree_le (c : List Bool) :
    (parameter F G A B hF hG c).natDegree ≤ (F.polynomial c).natDegree * (G.polynomial c).natDegree := by
  rw [parameter_degree]
  exact Nat.mul_le_mul (reduced_degree_le F c (hF c)) (reduced_degree_le G c (hG c))

theorem direction_le (c : List Bool) :
    direction F G A B hF hG c ≤ ((F.polynomial c).natDegree * (G.polynomial c).natDegree) ^ 2 :=
  (direction_spec F G A B hF hG c).1.trans (Nat.pow_le_pow_left
    (Nat.mul_le_mul (reduced_degree_le F c (hF c)) (reduced_degree_le G c (hG c))) 2)

theorem parameter_separable (c : List Bool) :
    ((parameter F G A B hF hG c).map (Int.castRingHom ℚ)).Separable :=
  (PrimitivePair.integer_separable_iff_separating _ _ _
    (ScaledSquarefree.separable_in_field (L := AlgebraicClosure ℚ) _ (hF c))
    (ScaledSquarefree.separable_in_field (L := AlgebraicClosure ℚ) _ (hG c))
    (IsAlgClosed.splits _) (IsAlgClosed.splits _)).mpr (direction_spec F G A B hF hG c).2

theorem parameter_separable_in_field {L : Type*} [Field L] [CharZero L] (c : List Bool) :
    ((parameter F G A B hF hG c).map (Int.castRingHom L)).Separable := by
  have h := (Polynomial.separable_map (Rat.castHom L)).mpr (parameter_separable F G A B hF hG c)
  have hc : (Rat.castHom L).comp (Int.castRingHom ℚ) = Int.castRingHom L := by ext z; simp
  simpa only [Polynomial.map_map, hc] using h

theorem parameter_ne_zero (c : List Bool) : parameter F G A B hF hG c ≠ 0 :=
  (Polynomial.map_ne_zero_iff (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)).mp
    (parameter_separable F G A B hF hG c).ne_zero

theorem degreeEvaluator : SpaceFunction (fun c => BinaryNatCode.encode (parameter F G A B hF hG c).natDegree) := by
  have E := ((SeparableBits.scaledSquarefreeDegreeEvaluator F A hF).pairOutputs
    (SeparableBits.scaledSquarefreeDegreeEvaluator G B hG)).postcompose BinaryNat.mul BinaryNat.mul_mem_FP
  refine E.congr (funext fun c => ?_)
  simp only [Function.comp_apply, BinaryNat.mul_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    parameter_degree, reduced]

end LeanCanny.Algebra.PreprocessedPair
