/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicPairRecoverySpace
public import LeanCanny.Algebra.SymbolicFixedTableCoordinates

/-! # Complete streamed symbolic primitive-pair numerators and denominators -/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicPairRecoveryBits
open Polynomial SymbolicScaledSquarefree
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open SymbolicScaledQuotientBits (original modulus alpha target original_FP modulus_FP alpha_FP target_FP)
open scoped Classical
attribute [local irreducible] BinaryNat.sub BinaryNat.mod BinaryNat.succ

noncomputable def Family.recovery (F : Family) (r : ℕ) (c : List Bool) : Polynomial (Polynomial ℤ) :=
  SymbolicPairRecovery.coordinateCoefficient (F.left c) (F.right c) (F.direction c) (F.leftOrder c) (F.rightOrder c) r

noncomputable def Family.denominator (F : Family) := F.recovery 1
noncomputable def Family.numerator (F : Family) (right : Bool) (c : List Bool) : Polynomial (Polynomial ℤ) :=
  if right then -F.recovery 0 c else X * F.denominator c + C (F.direction c : Polynomial ℤ) * F.recovery 0 c

noncomputable def Family.coordinate (F : Family) (right : Bool) (c : List Bool) : SymbolicBalancedCoordinate.Coordinate :=
  ⟨F.numerator right c, F.denominator c⟩

lemma Family.coordinate_eq (F : Family) (c : List Bool) (right : Bool)
    (hm : F.leftOrder c = (F.left c).natDegree) (hn : F.rightOrder c = (F.right c).natDegree) :
    F.coordinate right c = SymbolicFixedTable.pairCoordinate right (F.left c) (F.right c) (F.direction c) := by
  cases right <;> simp only [Family.coordinate, Family.numerator, Family.denominator, Family.recovery,
    hm, hn, SymbolicPairRecovery.coordinateCoefficient_eq, coordinateCoefficient_zero,
    coordinateCoefficient_one, SymbolicFixedTable.pairCoordinate, Bool.false_eq_true, ite_false, ite_true,
    PrimitivePair.leftNumerator, PrimitivePair.rightNumerator, PrimitivePair.denominator]

def previousQuery (q : List Bool) : List Bool :=
  pair (pairFst q) (pair (alpha q) (BinaryNat.sub (pair (target q) [true])))
lemma previousQuery_FP : previousQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair alpha_FP
    (mem_FP_comp (mem_FP_pair target_FP (constFn_mem_FP _)) BinaryNat.sub_mem_FP))

section Readers
variable (F : Family) (B : List Bool → ℕ)
variable (hP : ∀ c k, ((F.left c).coeff k).natDegree ≤ B c)
variable (hQ : ∀ c k, ((F.right c).coeff k).natDegree ≤ B c)
variable (hm : BinaryFn F.leftOrder) (hn : BinaryFn F.rightOrder) (hc : BinaryFn F.direction) (hB : BinaryFn B)
variable (P : SpaceFunction (SymbolicFixedTableEntryBits.coefficient F.left))
variable (Q : SpaceFunction (SymbolicFixedTableEntryBits.coefficient F.right))

include B hP hQ hm hn hc hB P Q in
lemma Family.denominatorEvaluator : SpaceFunction (SymbolicFixedTableEntryBits.coefficient F.denominator) :=
  F.coordinateCoefficientEvaluator B hP hQ hm hn hc hB P Q 1 le_rfl

include B hP hQ hm hn hc hB P Q in
lemma Family.recoveryEvaluator : SpaceFunction (SymbolicFixedTableEntryBits.coefficient (F.recovery 0)) :=
  F.coordinateCoefficientEvaluator B hP hQ hm hn hc hB P Q 0 (by decide)

include hc in
lemma Family.directionEvaluator : SpaceFunction (fun q => residueBits
    ((F.direction (original q) : ℕ) : ZMod (Nat.fromBitsLE (modulus q) + 1))) := by
  let f := fun q => BinaryNat.mod (pair (BinaryNatCode.encode (F.direction (original q))) (BinaryNat.succ (modulus q)))
  have hd := mem_FP_comp (f := original) (g := fun c => BinaryNatCode.encode (F.direction c)) original_FP hc.bits_mem_FP
  have hmod := mem_FP_comp (f := modulus) (g := BinaryNat.succ) modulus_FP BinaryNat.succ_mem_FP
  have H := mem_FP_comp (mem_FP_pair hd hmod) BinaryNat.mod_mem_FP
  refine (SpaceFunction.ofFP f H).congr (funext fun q => ?_)
  simp only [f, BinaryNat.mod_pair, BinaryNat.succ_eq_bits, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, residueBits, ZMod.val_natCast]

include B hP hQ hm hn hc hB P Q in
lemma Family.rightNumeratorEvaluator :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient (F.numerator true)) := by
  have N := F.recoveryEvaluator B hP hQ hm hn hc hB P Q
  have H := ModularResidueSpace.negEvaluator modulus
    (fun q => ((((F.recovery 0 (original q)).coeff (Nat.fromBitsLE (target q))).coeff
      (Nat.fromBitsLE (alpha q)) : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1))) modulus_FP N
  refine H.congr (funext fun q => ?_)
  simp only [Family.numerator, ite_true, SymbolicFixedTableEntryBits.coefficient,
    coeff_neg, SymbolicFixedTableEntryBits.integerResidue, Int.cast_neg]
  rfl

include B hP hQ hm hn hc hB P Q in
lemma Family.leftNumeratorEvaluator :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient (F.numerator false)) := by
  have D := F.denominatorEvaluator B hP hQ hm hn hc hB P Q
  have N := F.recoveryEvaluator B hP hQ hm hn hc hB P Q
  have DP : SpaceFunction (fun q => SymbolicFixedTableEntryBits.integerResidue
      (((F.denominator (original q)).coeff (Nat.fromBitsLE (target q) - 1)).coeff
        (Nat.fromBitsLE (alpha q))) (Nat.fromBitsLE (modulus q) + 1)) := by
    refine (D.precompose previousQuery previousQuery_FP).congr (funext fun q => ?_)
    simp only [Function.comp_apply, SymbolicFixedTableEntryBits.coefficient, previousQuery,
      original, modulus, alpha, target, pairFst_pair, pairSnd_pair, BinaryNat.sub_pair,
      fromBits_one, Nat.fromBitsLE_bits]
  have Z : SpaceFunction (fun q => residueBits (0 : ZMod (Nat.fromBitsLE (modulus q) + 1))) := by
    refine (SpaceFunction.ofFP (fun _ : List Bool => []) (constFn_mem_FP [])).congr (funext fun q => ?_)
    simp [residueBits, BinaryNatCode.encode]
  have hp : FPPred (fun q => 1 ≤ Nat.fromBitsLE (target q)) := (BinaryNat.le_fppred (constFn_mem_FP [true]) target_FP).of_iff
    (fun q => by simp only [fromBits_one])
  have SD := ModularResidueSpace.branchEvaluator modulus _ _
    (fun q => 1 ≤ Nat.fromBitsLE (target q)) hp DP Z
  have CN := ModularResidueSpace.mulEvaluator modulus _ _ modulus_FP (F.directionEvaluator hc) N
  have H := ModularResidueSpace.addEvaluator modulus _ _ modulus_FP SD CN
  refine H.congr (funext fun q => ?_)
  simp only [SymbolicFixedTableEntryBits.coefficient, Family.numerator, Bool.false_eq_true, ite_false,
    coeff_add, coeff_C_mul, SymbolicFixedTableEntryBits.integerResidue]
  have hX := coeff_X_pow_mul' (F.denominator (original q)) 1 (Nat.fromBitsLE (target q))
  simp only [pow_one] at hX
  simp only [original, modulus, alpha, target] at hX ⊢
  rw [hX]
  by_cases h : 1 ≤ Nat.fromBitsLE (pairSnd (pairSnd q))
  all_goals
    simp only [h, ite_true, ite_false, coeff_zero, Int.cast_add, Int.cast_zero,
      coeff_natCast_mul, Int.cast_mul, Int.cast_natCast]
    split_ifs <;> rfl

include B hP hQ hm hn hc hB P Q in
lemma Family.numeratorEvaluator (right : Bool) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient (F.numerator right)) := by
  cases right
  · exact F.leftNumeratorEvaluator B hP hQ hm hn hc hB P Q
  · exact F.rightNumeratorEvaluator B hP hQ hm hn hc hB P Q

end Readers
end LeanCanny.Algebra.SymbolicPairRecoveryBits
