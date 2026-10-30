/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialFamilyProductSpace

/-! # Native products of two arbitrary integer polynomial readers -/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialBinaryProductBits
open LeanCanny.Encoding LeanCanny.Computation
open RationalSubstitution.IntegerBits (context)
open scoped Classical
set_option maxHeartbeats 300000

noncomputable def factor (p q : List Bool → Polynomial ℤ) (z : List Bool) : Polynomial ℤ :=
  if Nat.fromBitsLE (pairSnd z) = 0 then p (pairFst z) else q (pairFst z)

theorem factorEvaluator (p q : List Bool → Polynomial ℤ)
    (P : SpaceFunction (PrimitivePairBits.coefficient p)) (Q : SpaceFunction (PrimitivePairBits.coefficient q)) :
    SpaceFunction (PrimitivePairBits.coefficient (factor p q)) := by
  have L := PolynomialFamilyProductBits.reindexEvaluator P pairFst pairFst_mem_FP
  have R := PolynomialFamilyProductBits.reindexEvaluator Q pairFst pairFst_mem_FP
  have hi := BinaryFn.fromBits (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP)
  have H := SpaceFunction.branch (fun z => decide (Nat.fromBitsLE (pairSnd (context z)) = 0))
    (hi.eq (BinaryFn.const 0)).flag_mem_FP L R
  refine H.congr (funext fun z => ?_)
  simp only [decide_eq_true_eq, Function.comp_apply, PrimitivePairBits.coefficient, factor]
  split_ifs <;> rfl

theorem product_eq (p q : List Bool → Polynomial ℤ) (r : List Bool) :
    PolynomialFamilyProductBits.polynomial (factor p q) (fun _ => 2) r = p r * q r := by
  simp [PolynomialFamilyProductBits.polynomial, Finset.prod_range_succ, factor,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem evaluator (p q : List Bool → Polynomial ℤ)
    (P : SpaceFunction (PrimitivePairBits.coefficient p)) (Q : SpaceFunction (PrimitivePairBits.coefficient q)) :
    SpaceFunction (PrimitivePairBits.coefficient (fun r => p r * q r)) := by
  have H := PolynomialFamilyProductBits.evaluator _ _ (BinaryFn.const 2) (factorEvaluator p q P Q)
  have he : PolynomialFamilyProductBits.polynomial (factor p q) (fun _ => 2) = (fun r => p r * q r) := funext (product_eq p q)
  exact he ▸ H

end LeanCanny.Algebra.PolynomialBinaryProductBits
