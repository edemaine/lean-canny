/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalSource
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientCatalogue
/-! # Original bounds for every bounded principal family choice

Declared target degrees vary through the original finite box. Uniform
integer degree and mass bounds are proved before center specialization.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalBounds
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation PrincipalSubresultant
open FormulaSignSlotRadialJointCoefficientCatalogue (base degree)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def degreeBound (c : List Bool) := (2*degree c+1)*degree c
noncomputable def widthBound (c : List Bool) := (degreeBound c+degree c).size
noncomputable def arity (c : List Bool) := FormulaSignSlotRadialJointLayout.centerCount c+1
noncomputable def inputMass (c : List Bool) := arity c*widthBound c+FormulaSignSlotRadialEliminantFormalMass.budget (base c)
noncomputable def derivativeMass (c : List Bool) := (degree c).size+inputMass c+(degree c+1).size
noncomputable def massBound (c : List Bool) := arity c*widthBound c+parameterMassBound (2*degree c) (derivativeMass c)

theorem degreeBound_binary : BinaryFn degreeBound :=
  (((BinaryFn.const 2).mul FormulaSignSlotRadialJointCoefficientCatalogue.degree_binary).add (BinaryFn.const 1)).mul
    FormulaSignSlotRadialJointCoefficientCatalogue.degree_binary
theorem widthBound_unary : UnaryFn widthBound :=
  (UnaryFn.length (degreeBound_binary.add FormulaSignSlotRadialJointCoefficientCatalogue.degree_binary).bits_mem_FP).of_eq
    (fun _ => BinaryNatCode.length_encode _)
theorem arity_unary : UnaryFn arity := FormulaSignSlotRadialJointLayout.centerCount_unary.add (UnaryFn.const 1)
theorem inputMass_binary : BinaryFn inputMass :=
  (BinaryFn.ofUnary (arity_unary.mul widthBound_unary)).add
    (FormulaSignSlotRadialEliminantFormalMass.budget_binary.comp FormulaSignSlotRadialJointCoefficientCatalogue.base_FP)
theorem derivativeMass_binary : BinaryFn derivativeMass :=
  (FormulaSignSlotRadialJointCoefficientCatalogue.degree_binary.size.add inputMass_binary).add
    ((FormulaSignSlotRadialJointCoefficientCatalogue.degree_binary.add (BinaryFn.const 1)).size)
theorem massBound_binary : BinaryFn massBound := by
  have H := (BinaryFn.const 2).mul FormulaSignSlotRadialJointCoefficientCatalogue.degree_binary
  exact (BinaryFn.ofUnary (arity_unary.mul widthBound_unary)).add
    (((H.size.mul H).add (H.mul derivativeMass_binary)).add derivativeMass_binary)

private theorem mass_mono {a b H K : ℕ} (hab : a≤b) (hHK : H≤K) : parameterMassBound a H≤parameterMassBound b K := by
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul (Nat.size_le_size hab) hab)
    (Nat.mul_le_mul hab hHK)) hHK

theorem input_eq (c C : List Bool)
    (HR : pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original C)=FormulaSignSlotRadialJointLayout.source true c) :
    FormulaSignSlotRadialCenterPrincipalFamily.inputBound C=degree c := by
  apply FormulaSignSlotRadialEliminantRootProfiles.degree_eq
  simpa only [base,pairFst_pair] using HR
theorem arity_eq (c C : List Bool)
    (HR : pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original C)=FormulaSignSlotRadialJointLayout.source true c) :
    FormulaSignSlotRadialCenterPrincipalFamily.arity C=arity c :=
  congrArg (fun z => FormulaSignSlotCenteredRadialGraph.d z+1) HR

theorem degree_le (c C : List Bool)
    (HR : pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original C)=FormulaSignSlotRadialJointLayout.source true c)
    (HD : FormulaSignSlotRadialCenterPrincipalFamily.degree C≤degree c) :
    FormulaSignSlotRadialCenterPrincipalFamily.degreeBound C≤degreeBound c := by
  unfold FormulaSignSlotRadialCenterPrincipalFamily.degreeBound degreeBound
  apply Nat.mul_le_mul _ (input_eq c C HR).le
  omega
theorem width_le (c C : List Bool)
    (HR : pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original C)=FormulaSignSlotRadialJointLayout.source true c)
    (HD : FormulaSignSlotRadialCenterPrincipalFamily.degree C≤degree c) :
    FormulaSignSlotRadialCenterPrincipalFamily.width C≤widthBound c :=
  Nat.size_le_size (Nat.add_le_add (degree_le c C HR HD) (input_eq c C HR).le)

theorem inputMass_le (c C : List Bool)
    (HR : pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original C)=FormulaSignSlotRadialJointLayout.source true c)
    (HD : FormulaSignSlotRadialCenterPrincipalFamily.degree C≤degree c) :
    FormulaSignSlotRadialCenterPrincipalMass.inputMass C ≤ inputMass c := by
  have HM : FormulaSignSlotRadialEliminantFormalMass.budget (FormulaSignSlotRadialCenterPrincipalFamily.original C)=
      FormulaSignSlotRadialEliminantFormalMass.budget (base c) := by
    apply FormulaSignSlotRadialEliminantRootProfiles.mass_eq
    simpa only [base,pairFst_pair] using HR
  unfold FormulaSignSlotRadialCenterPrincipalMass.inputMass inputMass
  rw [arity_eq c C HR,HM]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (width_le c C HR HD)) _
theorem derivativeMass_le (c C : List Bool)
    (HR : pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original C)=FormulaSignSlotRadialJointLayout.source true c)
    (HD : FormulaSignSlotRadialCenterPrincipalFamily.degree C≤degree c) :
    FormulaSignSlotRadialCenterPrincipalMass.derivativeMass C≤derivativeMass c :=
  Nat.add_le_add (Nat.add_le_add (Nat.size_le_size HD) (inputMass_le c C HR HD))
    (Nat.size_le_size (Nat.add_le_add_right HD 1))
theorem mass_le (c C : List Bool)
    (HR : pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original C)=FormulaSignSlotRadialJointLayout.source true c)
    (HD : FormulaSignSlotRadialCenterPrincipalFamily.degree C≤degree c) :
    FormulaSignSlotRadialCenterPrincipalMass.budget C≤massBound c := by
  unfold FormulaSignSlotRadialCenterPrincipalMass.budget massBound
  apply Nat.add_le_add _ (mass_mono (Nat.mul_le_mul_left 2 HD) (derivativeMass_le c C HR HD))
  rw [arity_eq c C HR]
  exact Nat.mul_le_mul_left _ (width_le c C HR HD)

end LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalBounds
