/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientGuards
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantDerivative
public import LeanCanny.Algebra.ModularResidueSpace
public import LeanCanny.Algebra.ModularScalarFP
/-! # Original-only modular access to the actual formal tilted gradient rows -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientNative
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower MvPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialFormalInput.polynomial
  FormulaSignSlotRadialFormalInput.equation

noncomputable def residue (modulus : List Bool → List Bool) (a : List Bool → ℤ) (q : List Bool) :=
  residueBits (a q : ZMod (Nat.fromBitsLE (modulus q) + 1))

private theorem zero_space (modulus : List Bool → List Bool) : SpaceFunction (residue modulus (fun _ => 0)) := by
  apply (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])).congr
  funext q
  simp [residue, residueBits, BinaryNatCode.encode]

private theorem branch_space (modulus : List Bool → List Bool) (P : List Bool → Prop)
    (hP : FPPred P) (a b : List Bool → ℤ)
    (EA : SpaceFunction (residue modulus a)) (EB : SpaceFunction (residue modulus b)) :
    SpaceFunction (residue modulus (fun q => if P q then a q else b q)) := by
  have H := ModularResidueSpace.branchEvaluator modulus
    (fun q => (a q : ZMod (Nat.fromBitsLE (modulus q) + 1)))
    (fun q => (b q : ZMod (Nat.fromBitsLE (modulus q) + 1))) P hP EA EB
  apply H.congr
  funext q
  by_cases h : P q <;> simp only [residue, h, ite_true, ite_false]

private theorem add_space (modulus : List Bool → List Bool) (hm : modulus ∈ FP) (a b : List Bool → ℤ)
    (EA : SpaceFunction (residue modulus a)) (EB : SpaceFunction (residue modulus b)) :
    SpaceFunction (residue modulus (fun q => a q + b q)) := by
  have H := ModularResidueSpace.addEvaluator modulus
    (fun q => (a q : ZMod (Nat.fromBitsLE (modulus q) + 1)))
    (fun q => (b q : ZMod (Nat.fromBitsLE (modulus q) + 1))) hm EA EB
  apply H.congr
  funext q
  simp only [residue, Int.cast_add]

private theorem sub_space (modulus : List Bool → List Bool) (hm : modulus ∈ FP) (a b : List Bool → ℤ)
    (EA : SpaceFunction (residue modulus a)) (EB : SpaceFunction (residue modulus b)) :
    SpaceFunction (residue modulus (fun q => a q - b q)) := by
  have EN := ModularResidueSpace.negEvaluator modulus
    (fun q => (b q : ZMod (Nat.fromBitsLE (modulus q) + 1))) hm EB
  have H := add_space modulus hm a (fun q => -b q) EA (EN.congr (funext fun q => by simp only [residue, Int.cast_neg]))
  exact H.congr (funext fun q => by simp only [sub_eq_add_neg])

noncomputable def gradientValue (read : List Bool → List Bool) (W : List Bool → ℕ)
    (target head epsilon targetParameter modulus : List Bool → List Bool)
    (j : (q : List Bool) → Fin (FormulaSignSlotRadialFormalInput.spatial (read q))) (q : List Bool) :=
  residue modulus (fun q => FormulaSignSlotRadialEliminantCoefficientModel.gradient (read q) (j q)
    (homogeneousExponent read W target head q) (Nat.fromBitsLE (epsilon q)) (Nat.fromBitsLE (targetParameter q))
    (FormulaSignSlotRadialEliminantCoefficientQuery.radius (read q) (sourceExponent read W target q))
    (FormulaSignSlotRadialEliminantCoefficientQuery.center (read q) (sourceExponent read W target q))) q

theorem gradient_evaluator (read : List Bool → List Bool) (hr : read ∈ FP)
    (W : List Bool → ℕ) (hW : UnaryFn W)
    (target head epsilon targetParameter modulus : List Bool → List Bool)
    (ht : target ∈ FP) (hh : head ∈ FP) (he : epsilon ∈ FP) (hT : targetParameter ∈ FP) (hm : modulus ∈ FP)
    (j : (q : List Bool) → Fin (FormulaSignSlotRadialFormalInput.spatial (read q)))
    (hj : UnaryFn (fun q => (j q).val)) :
    SpaceFunction (gradientValue read W target head epsilon targetParameter modulus j) := by
  let X := sourceExponent read W target
  let E := homogeneousExponent read W target head
  let R := fun q => FormulaSignSlotRadialEliminantCoefficientQuery.radius (read q) (X q)
  let V := fun q => FormulaSignSlotRadialEliminantCoefficientQuery.center (read q) (X q)
  let dense := fun q => FormulaSignSlotRadialEliminantCoefficientModel.dense (read q) (j q) (E q).some (R q) (V q)
  have Hfit : ∀ q, (j q).val < FormulaSignSlotRadialFormalInput.dimension (read q) := by
    intro q
    exact (j q).isLt.trans_le (Nat.le_add_right _ _)
  have ED0 := FormulaSignSlotRadialEliminantDerivative.evaluator read hr W (fun q => (j q).val) hW hj
    Hfit target modulus ht hm
  have ED : SpaceFunction (residue modulus dense) := by
    apply ED0.congr
    funext q
    change residueBits ((((pderiv (FormulaSignSlotRadialFormalInput.spatialIndex (read q) (j q))
      ((FormulaSignSlotRadialFormalInput.polynomial (read q)) ^ 2)).coeff (X q)) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus q) + 1)) = _
    have HD := FormulaSignSlotRadialEliminantCoefficientQuery.dense (read q) (j q) (X q)
    have HS : (E q).some = FormulaSignSlotRadialEliminantCoefficientQuery.spatial (read q) (X q) := by
      simp only [E, X, homogeneousExponent, FormulaSignSlotRadialEliminantCoefficientQuery.homogeneous,
        Finsupp.some_optionElim]
    change _ = residueBits ((FormulaSignSlotRadialEliminantCoefficientModel.dense (read q) (j q)
      (E q).some (R q) (V q)) : ZMod (Nat.fromBitsLE (modulus q) + 1))
    rw [HS]
    exact congrArg (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (modulus q) + 1))) HD.symm
  have HParams : FPPred (fun q => R q = 0 ∧ V q = 0) := parameters_zero_FP read hr W hW target ht
  have HZero : FPPred (fun q => (E q).some = 0) := by
    apply (spatial_zero_FP read hr W hW target ht).of_iff
    intro q
    simp only [E, homogeneousExponent, FormulaSignSlotRadialEliminantCoefficientQuery.homogeneous,
      Finsupp.some_optionElim]
  have HHom : FPPred (fun q => Finsupp.weight (WeightedHomogenization.weights
      (fun _ : Fin (FormulaSignSlotRadialFormalInput.spatial (read q)) => 1)) (E q) = 2 * degreeBudget (read q) + 1) :=
    homogeneous_FP read hr W hW target head ht hh
  have HMono : FPPred (fun q => Finsupp.single (some (j q)) (2 * degreeBudget (read q) + 1) = E q) :=
    monomial_FP read hr W hW target head ht hh (fun q => 2 * degreeBudget (read q) + 1)
      (BinaryFn.ofUnary (((UnaryFn.const 2).mul (degreeBudget_unary.comp hr)).add (UnaryFn.const 1))) j hj
  have HMargin : FPPred (fun q => j q = marginIndex (read q)) := by
    apply (FPPred.eq hj (FormulaSignSlotSource.dimension_unary.comp hr)).of_iff
    intro q
    change (j q).val = (marginIndex (read q)).val ↔ _
    exact Fin.val_inj
  have H00 := ((BinaryFn.fromBits he).eq (BinaryFn.const 0)).and ((BinaryFn.fromBits hT).eq (BinaryFn.const 0))
  have H10 := ((BinaryFn.fromBits he).eq (BinaryFn.const 1)).and ((BinaryFn.fromBits hT).eq (BinaryFn.const 0))
  have H20 := ((BinaryFn.fromBits he).eq (BinaryFn.const 2)).and ((BinaryFn.fromBits hT).eq (BinaryFn.const 0))
  have E0 := zero_space modulus
  have HMod : BinaryFn (fun q => Nat.fromBitsLE (modulus q) + 1) := (BinaryFn.fromBits hm).add (BinaryFn.const 1)
  have E1 : SpaceFunction (residue modulus (fun _ => 1)) := by
    apply (SpaceFunction.ofFP _ (ModularScalarFP.natCast HMod (fun _ => 1) (BinaryFn.const 1))).congr
    funext q
    simp only [residue, Int.cast_one, Nat.cast_one]
  have EN : SpaceFunction (residue modulus (fun q => ((2 * degreeBudget (read q) + 2 : ℕ) : ℤ))) := by
    apply (SpaceFunction.ofFP _ (ModularScalarFP.natCast HMod (fun q => 2 * degreeBudget (read q) + 2)
      (BinaryFn.ofUnary (((UnaryFn.const 2).mul (degreeBudget_unary.comp hr)).add (UnaryFn.const 2))))).congr
    funext q
    simp only [residue, Int.cast_natCast]
  have EA := branch_space modulus _ H00 dense (fun _ => 0) ED E0
  have EB := branch_space modulus _ HParams (fun _ => 1) (fun _ => 0) E1 E0
  have EB := branch_space modulus _ H10 _ (fun _ => 0) EB E0
  have EB := branch_space modulus _ HZero _ (fun _ => 0) EB E0
  have EB := branch_space modulus _ HMargin _ (fun _ => 0) EB E0
  have EG := sub_space modulus hm _ _ EA EB
  have EG := branch_space modulus _ HHom _ (fun _ => 0) EG E0
  have EC := branch_space modulus _ HParams _ (fun _ => 0) EN E0
  have EC := branch_space modulus _ H20 _ (fun _ => 0) EC E0
  have EC := branch_space modulus _ HMono _ (fun _ => 0) EC E0
  have HF := add_space modulus hm _ _ EG EC
  apply HF.congr
  funext q
  simp only [gradientValue, residue, FormulaSignSlotRadialEliminantCoefficientModel.gradient,
    FormulaSignSlotRadialEliminantCoefficientModel.kernel, X, E, R, V, dense]
  congr

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientNative
