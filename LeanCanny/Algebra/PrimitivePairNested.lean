/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairSpace
public import LeanCanny.Algebra.PrimitivePairInteger

/-! # A computed resultant can be the next primitive-pair input

An exact product-degree identity supplies the new FP metadata. The first
resultant's complete native evaluator becomes the next left coefficient child;
no polynomial-time coefficient hypothesis or child execution clock is needed.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrimitivePairBits
open LeanCanny.Encoding LeanCanny.Computation
attribute [local irreducible] BinaryNat.mul

noncomputable def Source.next (S : Source) : Source where
  left c := cannyResultant (S.left c) (S.right c) (S.direction c)
  right := S.right
  direction := S.direction

noncomputable def Readers.next (S : Source) (A : Readers S)
    (hdegree : ∀ c, (cannyResultant (S.left c) (S.right c) (S.direction c)).natDegree =
      (S.left c).natDegree * (S.right c).natDegree) : Readers S.next where
  leftDegree c := BinaryNat.mul (LeanCanny.pair (A.leftDegree c) (A.rightDegree c))
  rightDegree := A.rightDegree
  direction := A.direction
  leftDegreeFP := by
    have he := mem_FP_comp (mem_FP_pair A.leftDegreeFP A.rightDegreeFP) BinaryNat.mul_mem_FP
    exact mem_FP_of_eq he (fun _ => rfl)
  rightDegreeFP := A.rightDegreeFP
  directionFP := A.directionFP
  leftDegree_eq c := by
    change BinaryNat.mul (LeanCanny.pair (A.leftDegree c) (A.rightDegree c)) =
      BinaryNatCode.encode (cannyResultant (S.left c) (S.right c) (S.direction c)).natDegree
    rw [BinaryNat.mul_pair, A.leftDegree_eq, A.rightDegree_eq, hdegree]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rightDegree_eq := A.rightDegree_eq
  direction_eq := A.direction_eq
  leftEvaluator := resultantEvaluator S A
  rightEvaluator := A.rightEvaluator

theorem nestedResultantEvaluator (S : Source) (A : Readers S)
    (hdegree : ∀ c, (cannyResultant (S.left c) (S.right c) (S.direction c)).natDegree =
      (S.left c).natDegree * (S.right c).natDegree) :
    SpaceFunction (coefficient (fun c => cannyResultant
      (cannyResultant (S.left c) (S.right c) (S.direction c)) (S.right c) (S.direction c))) :=
  resultantEvaluator S.next (A.next S hdegree)

end LeanCanny.Algebra.PrimitivePairBits
