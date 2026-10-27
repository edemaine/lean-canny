/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberFeatureMoments
public import LeanCanny.Encoding.BoundedAlgebraicFiberPencilBounds
public import LeanCanny.Algebra.SignedIntegerArithmeticFP

/-! # Native integer entries of a pointwise signature probe

Contexts are `pair hashContext (pair signedPoint featureIndex)`. The constant
entry is hG-H; the linear entry is the derivative-weighted moment, or G for
the denominator probe. Every reader is native and total on arbitrary words.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberProbeEntries
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open scoped Classical

def hashContext (z : List Bool) : List Bool := pairFst z
def pointCode (z : List Bool) : List Bool := pairFst (pairSnd z)
def featureCode (z : List Bool) : List Bool := pairSnd (pairSnd z)
theorem hashContext_FP : hashContext ∈ FP := pairFst_mem_FP
theorem pointCode_FP : pointCode ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem featureCode_FP : featureCode ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
def pointValue (z : List Bool) : ℤ := SignedIntegerArithmetic.value (pointCode z)

def context (b : List Bool) (h : ℤ) (d : ℕ) : List Bool :=
  pair b (pair (SignStatisticBits.integerCode h) (BinaryNatCode.encode d))
theorem pointValue_packet (b : List Bool) (h : ℤ) (d : ℕ) : pointValue (context b h d) = h := by
  simp only [pointValue, pointCode, context, pairFst_pair, pairSnd_pair, SignedIntegerArithmetic.value_packet]

def entryQuery (e : List Bool) : List Bool := pair (hashContext (pairFst e)) (pairSnd e)
theorem entryQuery_FP : entryQuery ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP hashContext_FP) pairSnd_mem_FP

def featureQuery (e : List Bool) : List Bool := pair
  (BoundedAlgebraicFiberWeightedMoments.original (hashContext (pairFst e)))
  (pair (pairFst (pairSnd e)) (pair (pairSnd (pairSnd e)) (featureCode (pairFst e))))
theorem featureQuery_FP : featureQuery ∈ FP := by
  have ho := mem_FP_comp (mem_FP_comp pairFst_mem_FP hashContext_FP) BoundedAlgebraicFiberWeightedMoments.original_FP
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hj := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hd := mem_FP_comp pairFst_mem_FP featureCode_FP
  exact mem_FP_pair ho (mem_FP_pair hi (mem_FP_pair hj hd))

noncomputable def gram (P : Readers) (F : BoundedAlgebraicSlice.Family) (e : List Bool) : ℤ := BoundedAlgebraicFiberPencilEntries.gram P F (entryQuery e)
noncomputable def weighted (P : Readers) (F : BoundedAlgebraicSlice.Family) (e : List Bool) : ℤ := BoundedAlgebraicFiberWeightedMoments.entry P F (entryQuery e)
noncomputable def constant (P : Readers) (F : BoundedAlgebraicSlice.Family) (e : List Bool) : ℤ := pointValue (pairFst e) * gram P F e - weighted P F e
noncomputable def linear (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (e : List Bool) : ℤ :=
  if unit then gram P F e else BoundedAlgebraicFiberFeatureMoments.moment P F (featureQuery e)

theorem gram_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun e => SignStatisticBits.integerCode (gram P F e)) := by
  have E := (BoundedAlgebraicFiberBasisGram.entry_evaluator h A ha).precompose
    (BoundedAlgebraicFiberPencilEntries.gramQuery ∘ entryQuery) (mem_FP_comp entryQuery_FP BoundedAlgebraicFiberPencilEntries.gramQuery_FP)
  exact E.congr (funext fun _ => by simp only [gram, BoundedAlgebraicFiberPencilEntries.gram, Function.comp_apply])

theorem constant_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun e => SignStatisticBits.integerCode (constant P F e)) := by
  have hp := mem_FP_comp pairFst_mem_FP pointCode_FP
  have R := SpaceFunction.ofFP (SignedIntegerArithmetic.canonical ∘ pointCode ∘ pairFst)
    (mem_FP_comp hp SignedIntegerArithmetic.canonical_FP)
  have X : SpaceFunction (fun e => SignStatisticBits.integerCode (pointValue (pairFst e))) :=
    R.congr (funext fun _ => by simp only [Function.comp_apply, SignedIntegerArithmetic.canonical_eq, pointValue])
  have W0 := (BoundedAlgebraicFiberWeightedMoments.evaluator h A ha).precompose entryQuery entryQuery_FP
  have W : SpaceFunction (fun e => SignStatisticBits.integerCode (weighted P F e)) := W0
  have M0 := (X.pairOutputs (gram_evaluator h A ha)).postcompose IntegerSumBits.multiply IntegerSumBits.multiply_mem_FP
  have M : SpaceFunction (fun e => SignStatisticBits.integerCode (pointValue (pairFst e) * gram P F e)) :=
    M0.congr (funext fun _ => by simp only [Function.comp_apply, IntegerSumBits.multiply_codes])
  have H := (M.pairOutputs W).postcompose SignedIntegerArithmetic.subtract SignedIntegerArithmetic.subtract_FP
  exact H.congr (funext fun _ => by simp only [Function.comp_apply, SignedIntegerArithmetic.subtract_packet, constant])

theorem linear_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (unit : Bool) :
    SpaceFunction (fun e => SignStatisticBits.integerCode (linear P F unit e)) := by
  cases unit with
  | false => exact (BoundedAlgebraicFiberFeatureMoments.evaluator h A ha).precompose featureQuery featureQuery_FP
  | true => exact gram_evaluator h A ha

noncomputable def coefficient (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (z : List Bool) : ℤ :=
  if Nat.fromBitsLE (pairSnd z) = 0 then constant P F (pairFst z)
  else if Nat.fromBitsLE (pairSnd z) = 1 then linear P F unit (pairFst z) else 0

attribute [local irreducible] constant linear coefficient

theorem evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (unit : Bool) :
    SpaceFunction (fun z => SignStatisticBits.integerCode (coefficient P F unit z)) := by
  have C := (constant_evaluator h A ha).precompose pairFst pairFst_mem_FP
  have L := (linear_evaluator h A ha unit).precompose pairFst pairFst_mem_FP
  have h0 := ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)).flag_mem_FP
  have h1 := ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 1)).flag_mem_FP
  have H := SpaceFunction.branch _ h0 C (SpaceFunction.branch _ h1 L
    (SpaceFunction.ofFP _ (constFn_mem_FP (SignStatisticBits.integerCode 0))))
  apply H.congr
  funext z
  simp only [coefficient, Function.comp_apply, decide_eq_true_eq]
  split_ifs <;> rfl

abbrev dimension (z : List Bool) : ℕ := BoundedAlgebraicFiberPencilEntries.dimension (hashContext z)
theorem dimension_binary : BinaryFn dimension := BoundedAlgebraicFiberPencilEntries.dimension_binary.comp hashContext_FP

noncomputable def matrix (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (z : List Bool) :
    Matrix (Fin (dimension z)) (Fin (dimension z)) ℤ[X] := fun i j =>
  C (constant P F (pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) +
    C (linear P F unit (pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) * X

theorem coefficient_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (z : List Bool) (i j : Fin (dimension z)) (k : ℕ) :
    coefficient P F unit (pair (pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) (BinaryNatCode.encode k)) =
      (matrix P F unit z i j).coeff k := by
  simp only [coefficient, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    matrix, coeff_add, coeff_C, coeff_C_mul, coeff_X]
  by_cases h0 : k = 0
  · simp only [h0, one_ne_zero, ite_false, ite_true, mul_zero, add_zero]
  · by_cases h1 : k = 1
    · simp only [h1, one_ne_zero, ite_false, ite_true, mul_one, zero_add]
    · simp only [h0, h1, Ne.symm h1, ite_false, mul_zero, add_zero]

theorem entry_degree (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (z : List Bool) (i j : Fin (dimension z)) :
    (matrix P F unit z i j).natDegree ≤ 1 := by
  unfold matrix
  apply (natDegree_add_le _ _).trans
  apply max_le
  · simp only [natDegree_C, Nat.zero_le]
  · exact natDegree_mul_le.trans (by simpa only [natDegree_C, zero_add] using (natDegree_X_le (R := ℤ)))

end LeanCanny.Encoding.BoundedAlgebraicFiberProbeEntries
