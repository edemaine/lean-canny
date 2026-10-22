/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicPairMinorSpace
public import LeanCanny.Algebra.ModularResidueSpace

/-! # Complete native bivariate primitive-pair coordinate readers -/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicPairRecoveryBits
open Polynomial SymbolicScaledSquarefree
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open LeanCanny.Encoding.Brackets
open SymbolicScaledQuotientBits (original modulus alpha target original_FP modulus_FP alpha_FP target_FP)
open scoped Classical
attribute [local irreducible] BinaryNat.sub BinaryNat.mod BinaryNat.succ

def shiftQuery (r : ℕ) (q : List Bool) : List Bool :=
  pair (pair (pair (original q) (alpha q)) (modulus q)) (pair (BinaryNatCode.encode r) (BinaryNat.normalize (target q)))
lemma shiftQuery_FP (r : ℕ) : shiftQuery r ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_pair original_FP alpha_FP) modulus_FP)
    (mem_FP_pair (constFn_mem_FP _) (mem_FP_comp target_FP BinaryNat.normalize_mem_FP))

def constantQuery (r : ℕ) (q : List Bool) : List Bool :=
  pair (pairFst q) (pair (alpha q) (BinaryNatCode.encode r))
lemma constantQuery_FP (r : ℕ) : constantQuery r ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair alpha_FP (constFn_mem_FP _))

section Readers
variable (F : Family) (B : List Bool → ℕ)
variable (hP : ∀ c k, ((F.left c).coeff k).natDegree ≤ B c)
variable (hQ : ∀ c k, ((F.right c).coeff k).natDegree ≤ B c)
variable (hm : BinaryFn F.leftOrder) (hn : BinaryFn F.rightOrder) (hc : BinaryFn F.direction) (hB : BinaryFn B)
variable (P : SpaceFunction (SymbolicFixedTableEntryBits.coefficient F.left))
variable (Q : SpaceFunction (SymbolicFixedTableEntryBits.coefficient F.right))

include hm hn hc P in
lemma Family.shiftCoefficientEvaluator (r : ℕ) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient (fun c => (shiftFamily (F.left c) (F.direction c)).coeff r)) := by
  have ha := F.access_controls hm hn hc
  have E := ShiftCoefficientBits.certifiedWithCoefficient F.access.shiftAccess ha.direction
    (P.precompose SymbolicFixedTableEntryBits.sliceCoefficientQuery SymbolicFixedTableEntryBits.sliceCoefficientQuery_FP)
    F.sliced.shiftSource F.access.shift_represents
  refine (E.precompose (shiftQuery r) (shiftQuery_FP r)).congr (funext fun q => ?_)
  change F.sliced.shiftSource.value (shiftQuery r q) = _
  change SymbolicFixedTableEntryBits.integerResidue
    ((((shiftFamily (F.sliced.shiftSource.polynomial (ShiftCoefficientBits.original (shiftQuery r q)))
      (F.sliced.shiftSource.direction (ShiftCoefficientBits.original (shiftQuery r q)))).coeff
        (ShiftCoefficientBits.iValue (shiftQuery r q))).coeff (ShiftCoefficientBits.jValue (shiftQuery r q))))
    (ShiftCoefficientBits.mValue (shiftQuery r q)) = _
  simp only [shiftQuery, CannyResultantBits.Family.shiftSource, SymbolicFixedTableEntryBits.Family.sliced,
    ShiftCoefficientBits.original, ShiftCoefficientBits.iValue, ShiftCoefficientBits.jValue,
    ShiftCoefficientBits.leftIndex, ShiftCoefficientBits.rightIndex, ShiftCoefficientBits.mValue,
    ShiftCoefficientBits.modulusMinusOne, pairFst_pair, pairSnd_pair,
    BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    ← SymbolicFixedTable.shift_slice, SymbolicFixedTableEntryBits.coefficient]
  rfl

include Q in
lemma Family.constantCoefficientEvaluator (r : ℕ) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient (fun c => C ((F.right c).coeff r))) := by
  have hzero := (BinaryNat.lt_fppred target_FP (constFn_mem_FP [true])).of_iff
    (fun q => by change Nat.fromBitsLE (target q) < 1 ↔ Nat.fromBitsLE (target q) = 0; omega)
  have E := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (target q) = 0)) hzero.flag_mem_FP
    (Q.precompose (constantQuery r) (constantQuery_FP r)) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine E.congr (funext fun q => ?_)
  by_cases ht : Nat.fromBitsLE (pairSnd (pairSnd q)) = 0
  · simp only [Function.comp_apply, SymbolicFixedTableEntryBits.coefficient, constantQuery, target,
      ht, decide_true, ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, coeff_C]
    rfl
  · simp only [Function.comp_apply, SymbolicFixedTableEntryBits.coefficient, constantQuery, target,
      ht, decide_false, Bool.false_eq_true, ite_false, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, coeff_C, coeff_zero,
      SymbolicFixedTableEntryBits.integerResidue, residueBits, Int.cast_zero, ZMod.val_zero]
    rfl

include B hP hQ hm hn hc hB P Q in
lemma Family.coordinateCoefficientEvaluator (r : ℕ) (hr : r ≤ 1) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient (fun c => SymbolicPairRecovery.coordinateCoefficient
      (F.left c) (F.right c) (F.direction c) (F.leftOrder c) (F.rightOrder c) r)) := by
  have hM := mem_FP_comp (f := original) (g := fun c => BinaryNatCode.encode (F.leftOrder c)) original_FP hm.bits_mem_FP
  have hN := mem_FP_comp (f := original) (g := fun c => BinaryNatCode.encode (F.rightOrder c)) original_FP hn.bits_mem_FP
  have hml : FPPred (fun q => F.leftOrder (original q) = 1) := (stringEq_fppred hM (constFn_mem_FP [true])).of_iff
    (fun q => by simp only [Function.comp_apply]; change BinaryNatCode.encode _ = BinaryNatCode.encode 1 ↔ _; exact BinaryNatCode.encode_injective.eq_iff)
  have hnl : FPPred (fun q => F.rightOrder (original q) = 1) := (stringEq_fppred hN (constFn_mem_FP [true])).of_iff
    (fun q => by simp only [Function.comp_apply]; change BinaryNatCode.encode _ = BinaryNatCode.encode 1 ↔ _; exact BinaryNatCode.encode_injective.eq_iff)
  have EI := SpaceFunction.branch (fun q => decide (F.leftOrder (original q) = 1)) hml.flag_mem_FP
    (F.shiftCoefficientEvaluator hm hn hc P r) (F.subresultantEvaluator r hr B hP hQ hm hn hc hB P Q)
  have E := SpaceFunction.branch (fun q => decide (F.rightOrder (original q) = 1)) hnl.flag_mem_FP
    (F.constantCoefficientEvaluator Q r) EI
  refine E.congr (funext fun q => ?_)
  by_cases hq : F.rightOrder (pairFst (pairFst q)) = 1 <;>
    by_cases hp : F.leftOrder (pairFst (pairFst q)) = 1
  all_goals
    simp only [Family.subresultantValue, SymbolicFixedTableEntryBits.coefficient,
      SymbolicPairRecovery.coordinateCoefficient, original, hq, hp, decide_true, decide_false,
      Bool.false_eq_true, ite_true, ite_false]

end Readers
end LeanCanny.Algebra.SymbolicPairRecoveryBits
