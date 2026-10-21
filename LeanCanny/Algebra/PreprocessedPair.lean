/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PreprocessedPairReaders
public import LeanCanny.Algebra.PreparedPolynomialContext

/-! # A native primitive-pair construction for arbitrary nonzero integer inputs

Square-free preprocessing, checked degree contexts, separating-direction search,
and coordinate recovery are composed here. Input coefficient readers may take
arbitrary time in polynomial space; the original degree and height controls are FP.
-/

@[expose] public section

namespace LeanCanny.Algebra.PreprocessedPair
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)

variable (F G : Family) (A : Readers F) (B : Readers G)
variable (hF : ∀ c, F.polynomial c ≠ 0) (hG : ∀ c, G.polynomial c ≠ 0)

local notation "S" => source F G
local notation "R" => readers F G A B hF hG

noncomputable def direction (c : List Bool) : ℕ := PrimitivePairBits.selectedDirection S R (prepare F G c)

noncomputable def parameter (c : List Bool) : ℤ[X] :=
  cannyResultant (reduced F c) (reduced G c) (direction F G A B hF hG c)

noncomputable def leftNumerator (c : List Bool) : ℤ[X] :=
  PrimitivePair.leftNumerator (reduced F c) (reduced G c) (direction F G A B hF hG c)
noncomputable def rightNumerator (c : List Bool) : ℤ[X] :=
  PrimitivePair.rightNumerator (reduced F c) (reduced G c) (direction F G A B hF hG c)
noncomputable def denominator (c : List Bool) : ℤ[X] :=
  PrimitivePair.denominator (reduced F c) (reduced G c) (direction F G A B hF hG c)

theorem direction_spec (c : List Bool) :
    direction F G A B hF hG c ≤ ((reduced F c).natDegree * (reduced G c).natDegree) ^ 2 ∧
      Set.InjOn (shear (direction F G A B hF hG c))
        (rootPairs (L := AlgebraicClosure ℚ) ((reduced F c).map (Int.castRingHom (AlgebraicClosure ℚ)))
          ((reduced G c).map (Int.castRingHom (AlgebraicClosure ℚ))) : Set ((AlgebraicClosure ℚ) × (AlgebraicClosure ℚ))) := by
  have h := PrimitivePairBits.selectedDirection_spec S R (prepare F G c)
    (left_separable (L := AlgebraicClosure ℚ) F G hF _) (right_separable (L := AlgebraicClosure ℚ) F G hG _)
    (IsAlgClosed.splits _) (IsAlgClosed.splits _)
  simpa only [left_packet, right_packet, direction] using h

theorem parameterEvaluator : SpaceFunction (PrimitivePairBits.coefficient (parameter F G A B hF hG)) := by
  have E := PrimitivePairBits.selectedResultantEvaluator S R (heights F G A B)
    (left_separable (L := AlgebraicClosure ℚ) F G hF) (right_separable (L := AlgebraicClosure ℚ) F G hG)
    (fun _ => IsAlgClosed.splits _) (fun _ => IsAlgClosed.splits _)
  have P := PrimitivePairBits.withContextEvaluator _ (prepare F G) (prepareEvaluator F G A B hF hG) E
  refine P.congr (funext fun q => ?_)
  simp only [PrimitivePairBits.coefficient, Function.comp_apply, left_packet, right_packet, parameter, direction]

theorem coordinateEvaluators :
    SpaceFunction (PrimitivePairBits.coefficient (leftNumerator F G A B hF hG)) ∧
    SpaceFunction (PrimitivePairBits.coefficient (rightNumerator F G A B hF hG)) ∧
    SpaceFunction (PrimitivePairBits.coefficient (denominator F G A B hF hG)) := by
  have E := PrimitivePairBits.selectedCoordinateEvaluators S R (heights F G A B)
    (left_separable (L := AlgebraicClosure ℚ) F G hF) (right_separable (L := AlgebraicClosure ℚ) F G hG)
    (fun _ => IsAlgClosed.splits _) (fun _ => IsAlgClosed.splits _)
  have P := prepareEvaluator F G A B hF hG
  refine ⟨?_, ?_, ?_⟩
  · have Q := PrimitivePairBits.withContextEvaluator _ (prepare F G) P E.1
    refine Q.congr (funext fun q => ?_)
    simp only [PrimitivePairBits.coefficient, Function.comp_apply, left_packet, right_packet, leftNumerator, direction]
  · have Q := PrimitivePairBits.withContextEvaluator _ (prepare F G) P E.2.1
    refine Q.congr (funext fun q => ?_)
    simp only [PrimitivePairBits.coefficient, Function.comp_apply, left_packet, right_packet, rightNumerator, direction]
  · have Q := PrimitivePairBits.withContextEvaluator _ (prepare F G) P E.2.2
    refine Q.congr (funext fun q => ?_)
    simp only [PrimitivePairBits.coefficient, Function.comp_apply, left_packet, right_packet, denominator, direction]

noncomputable def decode {L : Type*} [Field L] [CharZero L] (c : List Bool) (theta : L) : L × L :=
  PrimitivePair.decodeInteger (reduced F c) (reduced G c) (direction F G A B hF hG c) theta

theorem decode_root {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] (c : List Bool) (theta : L)
    (ht : (parameter F G A B hF hG c).eval₂ (Int.castRingHom L) theta = 0) :
    (F.polynomial c).eval₂ (Int.castRingHom L) (decode F G A B hF hG c theta).1 = 0 ∧
    (G.polynomial c).eval₂ (Int.castRingHom L) (decode F G A B hF hG c theta).2 = 0 ∧
    shear (direction F G A B hF hG c) (decode F G A B hF hG c theta) = theta ∧
    (denominator F G A B hF hG c).eval₂ (Int.castRingHom L) theta ≠ 0 := by
  have hs := PrimitivePairBits.selectedDecode_root S R (prepare F G c) theta
    (left_separable (L := L) F G hF _) (right_separable (L := L) F G hG _)
    (IsAlgClosed.splits _) (IsAlgClosed.splits _)
  rw [left_packet, right_packet] at hs
  have hr := hs ht
  refine ⟨?_, ?_, hr.2.2.1, hr.2.2.2⟩
  · exact (ScaledSquarefree.roots_iff (F.polynomial c) (hF c) _).mp hr.1
  · exact (ScaledSquarefree.roots_iff (G.polynomial c) (hG c) _).mp hr.2.1

end LeanCanny.Algebra.PreprocessedPair
