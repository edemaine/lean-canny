/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyResultantRecursiveStage
public import LeanCanny.Algebra.SylvesterPolynomialTaskDegrees

/-! # Degree growth in original-coefficient requests

An active shifted-left request adds at most the supplied left order to the
requested output degree. An active constant-right request has index at most
the supplied right order. Their binary word lengths grow additively.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyResultantBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation
open SylvesterPolynomialBits.RecursiveStage (coefficientDegree)

variable {F : Family} {leftOrder rightOrder : List Bool → ℕ} (a : Access F leftOrder rightOrder)

attribute [local irreducible] BinaryNat.normalize BinaryNat.sub BinaryNat.add
  SylvesterPolynomialBits.RecursiveStage.leftInput SylvesterPolynomialBits.RecursiveStage.rightInput

theorem request_active (p : List Bool) (h : request a p = true) : active a p = true := by
  cases ha : active a p <;> simp_all only [request, ite_true, ite_false, Bool.false_eq_true]

theorem leftQuery_degree_code (p : List Bool) :
    pairSnd (leftQuery a p) = BinaryNatCode.encode
      (Nat.fromBitsLE (ShiftCoefficientBits.leftIndex (leftInput a p)) + coefficientDegree p) := by
  simp only [leftQuery, Function.comp_apply, ShiftCoefficientBits.coefficientInput, pairSnd_pair,
    ShiftCoefficientBits.sumIndex, BinaryNat.add_pair, BinaryNatCode.encode]
  rw [show Nat.fromBitsLE (ShiftCoefficientBits.rightIndex (leftInput a p)) = coefficientDegree p from
    SylvesterPolynomialBits.RecursiveStage.leftInput_degree a.modular.bits p]

theorem rightQuery_degree_code (p : List Bool) :
    pairSnd (rightQuery p) = BinaryNatCode.encode
      (Nat.fromBitsLE (ShiftCoefficientBits.leftIndex (rightInput p))) := by
  simp only [rightQuery, Function.comp_apply, Access.constantInput, pairSnd_pair,
    ShiftCoefficientBits.leftIndex, rightInput, SylvesterPolynomialBits.RecursiveStage.rightInput,
    PolynomialMoment.vectorInput, SylvesterBits.coefficientInput, pairFst_pair, BinaryNat.sub_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem leftQuery_degree_le (p : List Bool) (ha : active a p = true) (hs : selectRight a p = false) :
    Nat.fromBitsLE (pairSnd (leftQuery a p)) ≤ leftOrder (pairFst (pairFst p)) + coefficientDegree p := by
  have hi := SylvesterPolynomialBits.RecursiveStage.leftInput_index_le a.modular.bits p ha hs
  change Nat.fromBitsLE (ShiftCoefficientBits.leftIndex (leftInput a p)) ≤
    Nat.fromBitsLE (a.leftDegree (pairFst (pairFst p))) at hi
  rw [a.leftDegree_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits] at hi
  rw [leftQuery_degree_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact Nat.add_le_add_right hi _

theorem rightQuery_degree_le (p : List Bool) (ha : active a p = true) (hs : selectRight a p = true) :
    Nat.fromBitsLE (pairSnd (rightQuery p)) ≤ rightOrder (pairFst (pairFst p)) := by
  have hi := SylvesterPolynomialBits.RecursiveStage.rightInput_index_le a.modular.bits p ha hs
  change Nat.fromBitsLE (ShiftCoefficientBits.leftIndex (rightInput p)) ≤
    Nat.fromBitsLE (a.rightDegree (pairFst (pairFst p))) at hi
  rw [a.rightDegree_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits] at hi
  simpa only [rightQuery_degree_code, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi

private theorem sum_size_le (x y : ℕ) : (x + y).size ≤ x.size + y.size + 1 := by
  simpa only [BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.size_eq_bits_len] using
    BinaryNat.add_length_le (BinaryNatCode.encode x) (BinaryNatCode.encode y)

theorem leftQuery_degree_length_le (p : List Bool) (ha : active a p = true) (hs : selectRight a p = false) :
    (pairSnd (leftQuery a p)).length ≤ (leftOrder (pairFst (pairFst p))).size + (coefficientDegree p).size + 1 := by
  rw [leftQuery_degree_code, BinaryNatCode.length_encode]
  have hi := SylvesterPolynomialBits.RecursiveStage.leftInput_index_le a.modular.bits p ha hs
  change Nat.fromBitsLE (ShiftCoefficientBits.leftIndex (leftInput a p)) ≤
    Nat.fromBitsLE (a.leftDegree (pairFst (pairFst p))) at hi
  rw [a.leftDegree_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits] at hi
  exact (sum_size_le _ _).trans (by have h := Nat.size_le_size hi; omega)

theorem rightQuery_degree_length_le (p : List Bool) (ha : active a p = true) (hs : selectRight a p = true) :
    (pairSnd (rightQuery p)).length ≤ (rightOrder (pairFst (pairFst p))).size := by
  rw [rightQuery_degree_code, BinaryNatCode.length_encode]
  have hi := rightQuery_degree_le a p ha hs
  simpa only [rightQuery_degree_code, BinaryNatCode.encode, Nat.fromBitsLE_bits] using Nat.size_le_size hi

end LeanCanny.Algebra.CannyResultantBits.RecursiveStage
