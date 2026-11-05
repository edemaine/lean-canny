/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGridLayout
public import LeanCanny.Encoding.FormulaSignSlotRadialGridSliceSource
public import LeanCanny.Encoding.IntegralFramedBankPolynomialEmbedding
/-! # An actual native grid-anchor feature on the literal joint tuple

All indices belong to the descriptor datum. The source, native coefficient
access, and target/radius/center columns are constructed internally.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointGridSource
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open FormulaSignSlotRadialJointGridLayout
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem degree_fit (z : List Bool) :
    FormulaSignSlotRadialGridSliceSource.source.degree (sliceContext z) <
      2^FormulaSignSlotRadialGridSliceSource.source.width (sliceContext z) :=
  FormulaSignSlotRadialEliminantPacked.result_fit (radial z)

noncomputable def source : IntegralFramedBankPolynomialModel.Source :=
  IntegralFramedBankPolynomialEmbedding.source FormulaSignSlotRadialGridSliceSource.source
    sliceContext dimension embedding degree_fit
noncomputable def access : IntegralFramedBankPolynomialModel.Access source :=
  IntegralFramedBankPolynomialEmbedding.access FormulaSignSlotRadialGridSliceSource.source
    sliceContext dimension embedding degree_fit FormulaSignSlotRadialGridSliceSource.access
    sliceContext_FP dimension_unary injective columnCode columnCode_FP columnCode_packet

theorem polynomial_eq (z : List Bool) : source.polynomial z = polynomial z := rfl

noncomputable def center (z : List Bool) (v : ℕ → ℝ)
    (i : Fin (FormulaSignSlotCenteredRadialGraph.d (pairFst (radial z)))) : ℝ := v (4*i.val)

theorem selected_evaluation (z : List Bool) (v : ℕ → ℝ) (D : ℕ)
    (H : FormulaSignSlotRadialCenterSelection.Guards (radial z) (center z v)
      (Nat.fromBitsLE (tauWord z)) D) :
    (source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i => v i.val) =
      (FormulaSignSlotRadialParameterEliminant.coordinate (pairFst (radial z)) (center z v)
        (FormulaSignSlotRadialEliminantInput.coordinate (radial z))).eval₂
          (Polynomial.evalRingHom (v (FormulaSignSlotRadialJointLayout.radiusVariable (header z))))
          (v (FormulaSignSlotRadialJointLayout.column 2 (selected z))) := by
  change (polynomial z).eval₂ (Int.castRingHom ℝ) (fun i : Fin (FormulaSignSlotRadialJointLayout.dimension (header z)) => v i.val) = _
  rw [polynomial, MvPolynomial.eval₂_rename]
  have HE : (fun i : Fin (FormulaSignSlotRadialJointLayout.dimension (header z)) => v i.val) ∘ embedding z =
      Fin.cons (v (FormulaSignSlotRadialJointLayout.column 2 (selected z)))
        (Fin.cons (v (FormulaSignSlotRadialJointLayout.radiusVariable (header z))) (center z v)) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · simp only [Function.comp_apply,embedding,column,Fin.val_zero,ite_true,Fin.cons_zero]
    · simp only [Function.comp_apply,embedding,column,Fin.val_zero,Fin.val_succ,
        show ¬(0+1=0) from by omega,ite_false,ite_true,Fin.cons_succ,Fin.cons_zero]
    · have H0 : k.val+1+1≠0 := by omega
      have H1 : k.val+1+1≠1 := by omega
      simp only [Function.comp_apply,embedding,column,Fin.val_succ,H0,H1,ite_false,Fin.cons_succ,
        FormulaSignSlotRadialJointLayout.column,center]
      congr 1
  rw [HE]
  exact FormulaSignSlotRadialGridSliceEvaluation.selected (radial z) (center z v)
    (Nat.fromBitsLE (tauWord z)) D H _ _

end LeanCanny.Encoding.FormulaSignSlotRadialJointGridSource
