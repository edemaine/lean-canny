/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberWeightedMoments

/-! # Native integer coefficients of the weighted fiber Gram pencil

The constant coefficient is the negative weighted moment; the linear
coefficient is the selected Gram entry. Higher coefficients are zero,
including for malformed or padded degree words. A binary count in the
context specifies the matrix dimension, so every control remains native FP.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberPencilEntries
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleFiberWeightedMoments
open scoped Classical

def gramQuery (q : List Bool) : List Bool := pair (original (pairFst q)) (pairSnd q)
theorem gramQuery_FP : gramQuery ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP original_FP) pairSnd_mem_FP

noncomputable def gram (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) : ℤ := BoundedCriticalSampleFiberBasisGram.entry P F (gramQuery q)

def negateCode (z : List Bool) : List Bool := pair (pairSnd z) (pairFst z)
theorem negateCode_FP : negateCode ∈ FP := mem_FP_pair pairSnd_mem_FP pairFst_mem_FP
theorem negateCode_packet (z : ℤ) : negateCode (SignStatisticBits.integerCode z) = SignStatisticBits.integerCode (-z) := by
  simp only [negateCode, SignStatisticBits.integerCode, pairFst_pair, pairSnd_pair, neg_neg]

noncomputable def coefficient (P : Readers) (F : BoundedAlgebraicSlice.Family) (z : List Bool) : ℤ :=
  if Nat.fromBitsLE (pairSnd z) = 0 then -entry P F (pairFst z)
  else if Nat.fromBitsLE (pairSnd z) = 1 then gram P F (pairFst z) else 0

theorem evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun z => SignStatisticBits.integerCode (coefficient P F z)) := by
  have E := (BoundedCriticalSampleFiberWeightedMoments.evaluator h A ha).precompose pairFst pairFst_mem_FP
  have N := E.postcompose negateCode negateCode_FP
  have G := (BoundedCriticalSampleFiberBasisGram.entry_evaluator h A ha).precompose (gramQuery ∘ pairFst)
    (mem_FP_comp pairFst_mem_FP gramQuery_FP)
  have h0 := ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)).flag_mem_FP
  have h1 := ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 1)).flag_mem_FP
  have H := SpaceFunction.branch _ h0 N (SpaceFunction.branch _ h1 G
    (SpaceFunction.ofFP _ (constFn_mem_FP (SignStatisticBits.integerCode 0))))
  apply H.congr
  funext z
  simp only [Function.comp_apply, negateCode_packet, coefficient, decide_eq_true_eq]
  split_ifs <;> rfl

abbrev dimension (b : List Bool) : ℕ := Nat.fromBitsLE (count b)
theorem dimension_binary : BinaryFn dimension := BinaryFn.fromBits count_FP

noncomputable def matrix (P : Readers) (F : BoundedAlgebraicSlice.Family) (b : List Bool) :
    Matrix (Fin (dimension b)) (Fin (dimension b)) ℤ[X] := fun i j =>
  C (gram P F (pair b (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) * X -
    C (entry P F (pair b (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))))

theorem coefficient_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (b : List Bool) (i j : Fin (dimension b)) (k : ℕ) :
    coefficient P F (pair (pair b (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
      (BinaryNatCode.encode k)) = (matrix P F b i j).coeff k := by
  simp only [coefficient, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, matrix,
    coeff_sub, coeff_C_mul, coeff_X, coeff_C]
  by_cases h0 : k = 0
  · simp only [h0, one_ne_zero, ite_false, ite_true, mul_zero, zero_sub]
  · by_cases h1 : k = 1
    · simp only [h1, one_ne_zero, ite_false, ite_true, mul_one, sub_zero]
    · simp only [h0, h1, Ne.symm h1, ite_false, mul_zero, sub_zero]

theorem entry_degree (P : Readers) (F : BoundedAlgebraicSlice.Family) (b : List Bool) (i j : Fin (dimension b)) : (matrix P F b i j).natDegree ≤ 1 := by
  unfold matrix
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_mul_le.trans (by simpa only [natDegree_C, zero_add] using (natDegree_X_le (R := ℤ)))
  · simp only [natDegree_C, Nat.zero_le]

end LeanCanny.Encoding.BoundedCriticalSampleFiberPencilEntries
