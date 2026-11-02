/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PowerIntegerPolynomial
public import LeanCanny.Algebra.ModularResidueSpace
public import LeanCanny.Computation.PolyTimeBinaryArithmetic
public import LeanCanny.Algebra.IntegralMixedIntegerFamilyOriginalSource

/-! # Native coefficient access to signed power leaves

Modular exponentiation charges the binary exponent and the caller's exact
modulus, including modulus one and composite moduli. No expanded literal
word, integer coefficient oracle or degree oracle is required.
-/
@[expose] public section
namespace LeanCanny.Algebra.PowerIntegerPolynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree mValue)
open scoped Classical

private theorem natural_evaluator {a : List Bool→ℕ} (ha : BinaryFn a) :
    SpaceFunction (fun q=>residueBits (a q : ZMod (mValue q))) := by
  have HM:=(BinaryFn.fromBits pairSnd_mem_FP).add (BinaryFn.const 1)
  have E:=SpaceFunction.ofFP _ (ha.mod HM).bits_mem_FP
  exact E.congr (funext fun q=>by simp only [residueBits,ZMod.val_natCast])

theorem power_evaluator {exponent : List Bool→ℕ} (he : BinaryFn exponent) :
    SpaceFunction (fun q=>residueBits (((2 : ℤ)^exponent (context q) : ℤ) : ZMod (mValue q))) := by
  have H:=(BinaryFn.const 2).powModSucc (he.comp RationalSubstitution.IntegerBits.context_mem_FP)
    (BinaryFn.fromBits pairSnd_mem_FP)
  have E:=SpaceFunction.ofFP _ H.bits_mem_FP
  refine E.congr (funext fun q=>?_)
  have HC : (((2 : ℤ)^exponent (context q) : ℤ) : ZMod (mValue q))=
      (((2 : ℕ)^exponent (context q) : ℕ) : ZMod (mValue q)) := by
    simp only [Int.cast_pow,Nat.cast_pow,Int.cast_ofNat,Nat.cast_ofNat]
  rw [HC]
  simp only [residueBits,ZMod.val_natCast,Function.comp_apply]

theorem coefficient_evaluator {negative : List Bool→Prop} {exponent : List Bool→ℕ}
    (hn : FPPred negative) (he : BinaryFn exponent) :
    SpaceFunction (PrimitivePairBits.coefficient (fun q=>polynomial (negative q) (exponent q))) := by
  have EP:=power_evaluator he
  have EN:=ModularResidueSpace.negEvaluator pairSnd _ pairSnd_mem_FP EP
  have ES:=ModularResidueSpace.branchEvaluator pairSnd _ _
    (fun q=>negative (context q)) (hn.comp RationalSubstitution.IntegerBits.context_mem_FP) EP EN
  have EZ:=natural_evaluator (BinaryFn.const 0)
  have EO:=natural_evaluator (BinaryFn.const 1)
  have HK:=BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  have E0:=ModularResidueSpace.branchEvaluator pairSnd _ _
    (fun q=>Nat.fromBitsLE (selectedDegree q)=0) (HK.eq (BinaryFn.const 0)) ES EZ
  have E1:=ModularResidueSpace.branchEvaluator pairSnd _ _
    (fun q=>Nat.fromBitsLE (selectedDegree q)=1) (HK.eq (BinaryFn.const 1)) EO E0
  refine E1.congr (funext fun q=>?_)
  unfold PrimitivePairBits.coefficient RationalSubstitution.IntegerBits.coefficientResidue
  rw [coefficient]
  by_cases H1 : Nat.fromBitsLE (selectedDegree q)=1
  · simp only [H1,ite_true,Int.cast_one,Nat.cast_one]
  by_cases H0 : Nat.fromBitsLE (selectedDegree q)=0
  · by_cases HS : negative (context q) <;> simp [H0,HS,value]
  · simp only [H1,H0,ite_false,Int.cast_zero,Nat.cast_zero]

theorem access {negative : List Bool→Prop} {exponent : List Bool→ℕ}
    (hn : FPPred negative) (he : BinaryFn exponent) :
    IntegerPolynomialRootQueriesBits.Access (source negative exponent) where
  coefficient:=coefficient_evaluator hn he
  degree:=BinaryFn.const 1
  mass:=he.add (BinaryFn.const 1)

theorem original (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    {negative : List Bool→Prop} {exponent : List Bool→ℕ} (hn : FPPred negative) (he : BinaryFn exponent) :
    IntegralMixedIntegerFamilyBits.Original P (fun q=>polynomial (negative q) (exponent q)) :=
  IntegralMixedIntegerFamilyBits.original_of_source P a _ (source negative exponent) (access hn he) id id_mem_FP (fun _=>rfl)

end LeanCanny.Algebra.PowerIntegerPolynomial
