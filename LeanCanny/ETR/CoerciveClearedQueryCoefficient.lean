/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveClearedQuerySpace
public import LeanCanny.ETR.CoerciveInfinitesimalReadout

/-! # Actual final bivariate query residues from native fixed-coordinate readers -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveClearedQueryCoefficient
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra MatrixPower
open CoerciveSourceSampling CoerciveSymbolicSampling CoerciveInfinitesimalFamily
open CoerciveCoordinateEncoding (radix radixCode)
open CoerciveClearedQuerySpace (substitution)
open Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det Macaulay.fullMatrix
set_option allowUnsafeReducibility true in
attribute [local reducible] CoercivePreparationControls.family
attribute [local irreducible] CoercivePreparationControls.referenceExponent CoerciveSymbolicBounds.queryDegree

def input (p : List Bool) := pairFst (pairFst p)
def row (p : List Bool) := pairFst (pairSnd (pairFst p))
def rootDegree (p : List Bool) := pairFst (pairSnd (pairSnd (pairFst p)))
def alphaDegree (p : List Bool) := pairSnd (pairSnd (pairSnd (pairFst p)))

theorem input_FP : input ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem row_FP : row ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem rootDegree_FP : rootDegree ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairFst_mem_FP
theorem alphaDegree_FP : alphaDegree ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairSnd_mem_FP

noncomputable def prepare (p : List Bool) : List Bool :=
  pair (pair (pair (input p) (row p))
    (BinaryNat.add (pair (alphaDegree p) (BinaryNat.mul (pair (radixCode (input p)) (rootDegree p)))))) (pairSnd p)

theorem prepare_FP : prepare ∈ FP := by
  have hb := mem_FP_comp input_FP CoerciveCoordinateEncoding.radixCode_FP
  have hm := mem_FP_comp (mem_FP_pair hb rootDegree_FP) BinaryNat.mul_mem_FP
  have hd := mem_FP_comp (mem_FP_pair alphaDegree_FP hm) BinaryNat.add_mem_FP
  exact mem_FP_of_eq (mem_FP_pair (mem_FP_pair (mem_FP_pair input_FP row_FP) hd) pairSnd_mem_FP) (fun _ => rfl)

noncomputable def Valid (p : List Bool) : Prop := Nat.fromBitsLE (alphaDegree p) < radix (input p)

theorem valid_fppred : FPPred Valid := by
  have h := BinaryNat.lt_fppred alphaDegree_FP (mem_FP_comp input_FP CoerciveCoordinateEncoding.radixCode_FP)
  exact h.of_iff (fun p => by simp only [Valid, Function.comp_apply, radixCode, BinaryNatCode.encode, Nat.fromBitsLE_bits])

noncomputable def coefficient (_R : CoerciveCoordinateEncoding.Readers) (p : List Bool) : List Bool :=
  if Valid p then substitution.value (prepare p) else []

theorem evaluator (R : CoerciveCoordinateEncoding.Readers) : SpaceFunction (coefficient R) := by
  have E := SpaceFunction.branch (fun p => decide (Valid p)) valid_fppred.flag_mem_FP
    ((CoerciveClearedQuerySpace.encodedEvaluator R).precompose prepare prepare_FP)
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  exact E.congr (funext fun p => by simp only [coefficient, decide_eq_true_eq, Function.comp_apply])

theorem value_packet (R : CoerciveCoordinateEncoding.Readers) (bits : List Bool) (i j k m : ℕ) (hm : 0 < m) :
    coefficient R (pair (pair bits (pair (BinaryNatCode.encode i)
      (pair (BinaryNatCode.encode j) (BinaryNatCode.encode k)))) (BinaryNatCode.encode (m - 1))) =
      DyadicBits.integerResidue (((clearedQuery bits (queryIndex bits i)).coeff j).coeff k) m := by
  let q := clearedQuery bits (queryIndex bits i)
  have hinner (l : ℕ) : (q.coeff l).natDegree < radix bits :=
    (CoerciveSymbolicBounds.cleared_inner_degree bits _ l).trans_lt (Nat.lt_succ_self _)
  by_cases hk : k < radix bits
  · simp only [coefficient, Valid, input, alphaDegree, row, rootDegree, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, hk, ite_true, prepare, radixCode,
      BinaryNat.add_pair, BinaryNat.mul_pair]
    change substitution.value
      (pair (pair (pair bits i.bits) (k + radix bits * j).bits) (m - 1).bits) = _
    simp only [RationalSubstitution.IntegerBits.Family.value, RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue, pairFst_pair, pairSnd_pair, Nat.fromBitsLE_bits,
      Nat.sub_add_cancel (show 1 ≤ m by omega)]
    rw [CoerciveClearedQuerySpace.substitution_polynomial]
    simp only [pairFst_pair, pairSnd_pair, Nat.fromBitsLE_bits]
    rw [pairFst_pair]
    change RationalSubstitution.IntegerBits.coefficientResidue
      ((PolynomialKronecker.encode (radix bits) q).coeff (k + radix bits * j)) m = _
    rw [PolynomialKronecker.coefficient (radix bits) q hinner k j hk]
    rfl
  · have hz : (q.coeff j).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt ((hinner j).trans_le (by omega))
    simp only [coefficient, Valid, input, alphaDegree, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, hk, ite_false]
    rw [hz]
    simp only [DyadicBits.integerResidue, Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

noncomputable def readers (R : CoerciveCoordinateEncoding.Readers) (H : DyadicPolynomialBits.Access rootFamily)
    (hH : SpaceFunction H.coefficient) : CoerciveInfinitesimalFamily.Readers where
  root := H
  root_space := hH
  coefficient := coefficient R
  coefficient_space := evaluator R
  coefficient_eq := value_packet R

end LeanCanny.ETR.CoerciveClearedQueryCoefficient
