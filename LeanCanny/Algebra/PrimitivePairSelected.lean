/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairSearch
public import LeanCanny.Algebra.PrimitivePairSpace
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Feeding a space-computed direction into primitive-pair coefficients

The chosen direction is computed into a prepared context. FP metadata selectors
then suffice for the existing coefficient routines. No polynomial-time bound on
direction selection is needed.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrimitivePairBits
open LeanCanny.Encoding LeanCanny.Computation
open RationalSubstitution.IntegerBits (context selectedDegree mValue)

def preparedQuery (z : List Bool) : List Bool :=
  pair (pair (pair (context (pairFst z)) (pairSnd z)) (selectedDegree (pairFst z)))
    (pairSnd (pairFst z))

theorem preparedQuery_FP : preparedQuery ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP RationalSubstitution.IntegerBits.context_mem_FP
  have hk := mem_FP_comp pairFst_mem_FP RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  have hm := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair hc pairSnd_mem_FP) hk) hm

theorem withDirectionEvaluator (p : List Bool → Polynomial ℤ) (direction : List Bool → ℕ)
    (D : SpaceFunction (fun c => BinaryNatCode.encode (direction c)))
    (E : SpaceFunction (coefficient p)) :
    SpaceFunction (coefficient (fun c => p (pair c (BinaryNatCode.encode (direction c))))) := by
  have Q := ((D.precompose context RationalSubstitution.IntegerBits.context_mem_FP).withInput).postcompose
    preparedQuery preparedQuery_FP
  have R := Q.chain E
  refine R.congr (funext fun q => ?_)
  simp only [Function.comp_apply, preparedQuery, coefficient, context, selectedDegree, mValue,
    pairFst_pair, pairSnd_pair]

theorem resultantWithDirectionEvaluator (S : Source) (A : Readers S) (direction : List Bool → ℕ)
    (D : SpaceFunction (fun c => BinaryNatCode.encode (direction c))) :
    SpaceFunction (coefficient (fun c => cannyResultant (S.left c) (S.right c) (direction c))) := by
  have E := withDirectionEvaluator _ direction D (resultantEvaluator S.candidates (A.candidates S))
  refine E.congr (funext fun q => ?_)
  simp only [coefficient, Source.candidates, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem leftNumeratorWithDirectionEvaluator (S : Source) (A : Readers S) (direction : List Bool → ℕ)
    (D : SpaceFunction (fun c => BinaryNatCode.encode (direction c))) :
    SpaceFunction (coefficient (fun c => PrimitivePair.leftNumerator (S.left c) (S.right c) (direction c))) := by
  have E := withDirectionEvaluator _ direction D (leftNumeratorEvaluator S.candidates (A.candidates S))
  refine E.congr (funext fun q => ?_)
  simp only [coefficient, Source.candidates, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem rightNumeratorWithDirectionEvaluator (S : Source) (A : Readers S) (direction : List Bool → ℕ)
    (D : SpaceFunction (fun c => BinaryNatCode.encode (direction c))) :
    SpaceFunction (coefficient (fun c => PrimitivePair.rightNumerator (S.left c) (S.right c) (direction c))) := by
  have E := withDirectionEvaluator _ direction D (rightNumeratorEvaluator S.candidates (A.candidates S))
  refine E.congr (funext fun q => ?_)
  simp only [coefficient, Source.candidates, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem denominatorWithDirectionEvaluator (S : Source) (A : Readers S) (direction : List Bool → ℕ)
    (D : SpaceFunction (fun c => BinaryNatCode.encode (direction c))) :
    SpaceFunction (coefficient (fun c => PrimitivePair.denominator (S.left c) (S.right c) (direction c))) := by
  have E := withDirectionEvaluator _ direction D (denominatorEvaluator S.candidates (A.candidates S))
  refine E.congr (funext fun q => ?_)
  simp only [coefficient, Source.candidates, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem selectedResultantEvaluator {L : Type*} [Field L] [CharZero L]
    (S : Source) (A : Readers S) (H : Heights S)
    (hp : ∀ c, ((S.left c).map (Int.castRingHom L)).Separable)
    (hq : ∀ c, ((S.right c).map (Int.castRingHom L)).Separable)
    (hsp : ∀ c, ((S.left c).map (Int.castRingHom L)).Splits)
    (hsq : ∀ c, ((S.right c).map (Int.castRingHom L)).Splits) :
    SpaceFunction (coefficient (fun c => cannyResultant (S.left c) (S.right c) (selectedDirection S A c))) :=
  resultantWithDirectionEvaluator S A _ (selectedDirectionEvaluator S A H hp hq hsp hsq)

theorem selectedCoordinateEvaluators {L : Type*} [Field L] [CharZero L]
    (S : Source) (A : Readers S) (H : Heights S)
    (hp : ∀ c, ((S.left c).map (Int.castRingHom L)).Separable)
    (hq : ∀ c, ((S.right c).map (Int.castRingHom L)).Separable)
    (hsp : ∀ c, ((S.left c).map (Int.castRingHom L)).Splits)
    (hsq : ∀ c, ((S.right c).map (Int.castRingHom L)).Splits) :
    SpaceFunction (coefficient (fun c => PrimitivePair.leftNumerator (S.left c) (S.right c) (selectedDirection S A c))) ∧
    SpaceFunction (coefficient (fun c => PrimitivePair.rightNumerator (S.left c) (S.right c) (selectedDirection S A c))) ∧
    SpaceFunction (coefficient (fun c => PrimitivePair.denominator (S.left c) (S.right c) (selectedDirection S A c))) := by
  have D := selectedDirectionEvaluator S A H hp hq hsp hsq
  exact ⟨leftNumeratorWithDirectionEvaluator S A _ D,
    rightNumeratorWithDirectionEvaluator S A _ D, denominatorWithDirectionEvaluator S A _ D⟩

theorem selectedDecode_root {L : Type*} [Field L] [CharZero L]
    (S : Source) (A : Readers S) (c : List Bool) (theta : L)
    (hp : ((S.left c).map (Int.castRingHom L)).Separable)
    (hq : ((S.right c).map (Int.castRingHom L)).Separable)
    (hsp : ((S.left c).map (Int.castRingHom L)).Splits)
    (hsq : ((S.right c).map (Int.castRingHom L)).Splits)
    (ht : (cannyResultant (S.left c) (S.right c) (selectedDirection S A c)).eval₂ (Int.castRingHom L) theta = 0) :
    (S.left c).eval₂ (Int.castRingHom L)
      (PrimitivePair.decodeInteger (S.left c) (S.right c) (selectedDirection S A c) theta).1 = 0 ∧
    (S.right c).eval₂ (Int.castRingHom L)
      (PrimitivePair.decodeInteger (S.left c) (S.right c) (selectedDirection S A c) theta).2 = 0 ∧
    shear (selectedDirection S A c)
      (PrimitivePair.decodeInteger (S.left c) (S.right c) (selectedDirection S A c) theta) = theta ∧
    (PrimitivePair.denominator (S.left c) (S.right c) (selectedDirection S A c)).eval₂ (Int.castRingHom L) theta ≠ 0 := by
  have hcast : Function.Injective (Int.castRingHom L) := Int.cast_injective
  exact PrimitivePair.decodeInteger_root _ _ _ theta
    ((Polynomial.map_ne_zero_iff hcast).mp hp.ne_zero) hq hsq
    (selectedDirection_spec S A c hp hq hsp hsq).2 ht

end LeanCanny.Algebra.PrimitivePairBits
