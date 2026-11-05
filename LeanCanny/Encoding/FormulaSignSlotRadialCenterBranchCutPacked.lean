/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutReader
/-! # Closed packed coefficients of the literal formal-center branch cut -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutPacked
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open RationalSubstitution.IntegerBits (context)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def order (r : List Bool) := Nat.fromBitsLE (pairSnd r)
noncomputable def count (r : List Bool) := FormulaSignSlotRadialCenterPrincipalFamily.degree (pairFst r) - order r + 3
noncomputable def factor (r : List Bool) : Polynomial ℤ :=
  if Nat.fromBitsLE (pairSnd r) < 2 then FormulaSignSlotRadialCenterBranchCutReader.leading (pairFst (pairFst r))
  else FormulaSignSlotRadialCenterBranchCutReader.minor (pairFst r)
noncomputable def product := PolynomialFamilyProductBits.polynomial factor count
noncomputable def encoded (c : List Bool) (k : ℕ) := FixedWidthKronecker.encode
  (FormulaSignSlotRadialCenterPrincipalFamily.arity c)
  (FormulaSignSlotRadialCenterBranchCutFamily.width c)
  (FormulaSignSlotRadialCenterBranchCutFamily.polynomial c k)
noncomputable def polynomial (r : List Bool) := encoded (pairFst r) (order r)

theorem count_binary : BinaryFn count := by
  have HD : BinaryFn (fun r => FormulaSignSlotRadialCenterPrincipalFamily.degree (pairFst r)) :=
    FormulaSignSlotRadialCenterPrincipalFamily.degree_binary.comp pairFst_mem_FP
  exact (HD.sub (BinaryFn.fromBits pairSnd_mem_FP)).add (BinaryFn.const 3)
private theorem factor_evaluator : SpaceFunction (PrimitivePairBits.coefficient factor) := by
  have L := PolynomialFamilyProductBits.reindexEvaluator
    FormulaSignSlotRadialCenterBranchCutReader.leading_evaluator (fun r => pairFst (pairFst r))
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have R := PolynomialFamilyProductBits.reindexEvaluator
    FormulaSignSlotRadialCenterBranchCutReader.minor_evaluator pairFst pairFst_mem_FP
  have HI : BinaryFn (fun q => Nat.fromBitsLE (pairSnd (context q))) :=
    BinaryFn.fromBits (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP)
  have E := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (pairSnd (context q)) < 2))
    (HI.lt (BinaryFn.const 2)).flag_mem_FP L R
  exact E.congr (funext fun q => by
    simp only [Function.comp_apply, PrimitivePairBits.coefficient, factor, decide_eq_true_eq]
    split_ifs <;> rfl)
theorem product_evaluator : SpaceFunction (PrimitivePairBits.coefficient product) :=
  PolynomialFamilyProductBits.evaluator factor count count_binary factor_evaluator

private theorem product_eq (r : List Bool) : product r =
    FormulaSignSlotRadialCenterBranchCutReader.leading (pairFst r) ^ 2 *
      FormulaSignSlotRadialCenterBranchCutReader.minor r ^
        (FormulaSignSlotRadialCenterPrincipalFamily.degree (pairFst r) - order r + 1) := by
  unfold product PolynomialFamilyProductBits.polynomial count
  rw [show FormulaSignSlotRadialCenterPrincipalFamily.degree (pairFst r) - order r + 3 =
    2 + (FormulaSignSlotRadialCenterPrincipalFamily.degree (pairFst r) - order r + 1) by omega,
    Finset.prod_range_add]
  congr 1
  · simp [Finset.prod_range_succ, factor, BinaryNatCode.encode, Nat.fromBitsLE_bits, pow_two]
  · have H (i : ℕ) : ¬2 + i < 2 := by omega
    simp only [factor, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      H, ite_false, Finset.prod_const, Finset.card_range]

private theorem polynomial_eq (r : List Bool) : polynomial r =
    if FormulaSignSlotRadialCenterPrincipalFamily.degree (pairFst r) = 0 then
      FormulaSignSlotRadialCenterBranchCutReader.leading (pairFst r)
    else if order r < FormulaSignSlotRadialCenterPrincipalFamily.degree (pairFst r) then product r else 0 := by
  unfold polynomial encoded FormulaSignSlotRadialCenterBranchCutFamily.polynomial
  split_ifs with HZ HK
  · rw [FormulaSignSlotRadialCenterBranchCutReader.leading_eq, HZ]
  · rw [map_mul, map_pow, map_pow, product_eq,
      FormulaSignSlotRadialCenterBranchCutReader.leading_eq]
    rw [FormulaSignSlotRadialCenterBranchCutReader.minor_eq r HK]
    rfl
  · rw [map_zero]

theorem evaluator : SpaceFunction (PrimitivePairBits.coefficient polynomial) := by
  have L := PolynomialFamilyProductBits.reindexEvaluator
    FormulaSignSlotRadialCenterBranchCutReader.leading_evaluator pairFst pairFst_mem_FP
  have HD : BinaryFn (fun q => FormulaSignSlotRadialCenterPrincipalFamily.degree (pairFst (context q))) :=
    FormulaSignSlotRadialCenterPrincipalFamily.degree_binary.comp
    (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP)
  have HK : BinaryFn (fun q => order (context q)) :=
    (BinaryFn.fromBits pairSnd_mem_FP).comp RationalSubstitution.IntegerBits.context_mem_FP
  have EI := SpaceFunction.branch (fun q => decide (order (context q) <
      FormulaSignSlotRadialCenterPrincipalFamily.degree (pairFst (context q))))
    (HK.lt HD).flag_mem_FP product_evaluator (SpaceFunction.ofFP _ (constFn_mem_FP []))
  have E := SpaceFunction.branch (fun q => decide
      (FormulaSignSlotRadialCenterPrincipalFamily.degree (pairFst (context q)) = 0))
    (HD.eq (BinaryFn.const 0)).flag_mem_FP L EI
  refine E.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq, Function.comp_apply, PrimitivePairBits.coefficient]
  rw [polynomial_eq]
  split_ifs <;> rfl

end LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutPacked
