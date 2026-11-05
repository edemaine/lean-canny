/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialExternalPreludeNative
public import LeanCanny.Algebra.IntegralMixedFramedChargedSlackSource
/-! # Actual sphere and regular integer sources for an external own point

Both characteristic polynomials use the SAME certified coordinate algebra.
Their numeric controls read the original spatial source and shared radius.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialExternalSlackSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry
open IntegralCriticalHistoryTask
open FormulaSignSlotRadialExternalPreludeNative
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def N (key : List Bool) := FormulaSignSlotRadialExternalPrelude.number (pairFst key)
noncomputable def R (key : List Bool) := FormulaSignSlotRadialExternalPrelude.radius (pairFst key)
noncomputable def charge (key : List Bool) :=
  (CanonicalAuxiliaryCandidateCover.equation (FormulaSignSlotRadialExternalPrelude.original (pairFst key))).toData.size
noncomputable def d (key : List Bool) := BoundedZeroSource.powerDegree (charge key)
noncomputable def Lam (key : List Bool) := BoundedRegularSource.regularizationExponent
  (N key) (charge key) (charge key) (R key)
noncomputable def K (key : List Bool) := BoundedZeroSource.penaltyExponent (N key) (charge key) (R key)
noncomputable def beta (key : List Bool) := BoundedZeroSource.perturbationExponent
  (N key) (charge key) (charge key) (R key)

theorem N_unary : UnaryFn N := FormulaSignSlotRadialExternalContext.number_unary.comp pairFst_mem_FP
theorem R_binary : BinaryFn R := FormulaSignSlotRadialExternalPrelude.radius_binary.comp pairFst_mem_FP
theorem charge_unary : UnaryFn charge :=
  (AuxiliaryCandidateRegularLift.allowance_unary CanonicalAuxiliaryCandidateCover.equation_FP).comp
    (mem_FP_comp (f := pairFst) (g := FormulaSignSlotRadialExternalContext.original)
      pairFst_mem_FP FormulaSignSlotRadialExternalContext.original_FP)
theorem d_binary : BinaryFn d := BoundedZeroControls.powerDegree_binary (BinaryFn.ofUnary charge_unary)
theorem Lam_binary : BinaryFn Lam := BoundedRegularControls.regularizationExponent_binary
  N_unary (BinaryFn.ofUnary charge_unary) (BinaryFn.ofUnary charge_unary) R_binary
theorem K_binary : BinaryFn K := BoundedZeroControls.penaltyExponent_binary
  N_unary (BinaryFn.ofUnary charge_unary) R_binary
theorem beta_binary : BinaryFn beta := BoundedZeroControls.perturbationExponent_binary
  N_unary (BinaryFn.ofUnary charge_unary) (BinaryFn.ofUnary charge_unary) R_binary
theorem d_pos (key : List Bool) : 0<d key := Nat.zero_lt_of_lt (BoundedRegularSource.powerDegree_gt_one (charge key))

noncomputable def sphereSource := IntegralMixedFramedChargedSlackSource.sphereSource
  certifiedParameters certifiedPlan certifiedData (fun _=>1) (fun _=>1) seed certifiedInputs N R
noncomputable def regularSource := IntegralMixedFramedChargedSlackSource.regularSource
  certifiedParameters certifiedPlan certifiedData (fun _=>1) (fun _=>1) seed certifiedInputs N d R Lam K

theorem sphere_nonzero (key : List Bool) : sphereSource.polynomial key≠0 :=
  IntegralMixedFramedChargedSlackSource.sphere_nonzero _ _ _ _ _ _ _ _ _ key
theorem regular_nonzero (key : List Bool) : regularSource.polynomial key≠0 :=
  IntegralMixedFramedChargedSlackSource.regular_nonzero _ _ _ _ _ _ _ _ _ _ _ _ key (d_pos key)

noncomputable def key (ctx : List Bool) := IntegralMixedFramedHistoryFamilyBits.keyAt ctx
  (FormulaSignSlotRadialExternalPrelude.count ctx) []
theorem key_FP : key ∈ FP := mem_FP_pair id_mem_FP (mem_FP_pair
  (BinaryFn.ofUnary FormulaSignSlotRadialExternalPrelude.count_unary).bits_mem_FP (constFn_mem_FP []))
theorem key_root (ctx : List Bool) : pairFst (key ctx)=ctx := pairFst_pair _ _
theorem key_prefix (ctx : List Bool) : IntegralMixedFramedHistoryFamilyBits.prefixLength certifiedParameters (key ctx)=
    FormulaSignSlotRadialExternalPrelude.count ctx :=
  IntegralMixedFramedHistoryFamilyBits.keyAt_prefix certifiedParameters ctx _ [] (by
    change FormulaSignSlotRadialExternalPrelude.count ctx≤FormulaSignSlotRadialExternalPrelude.count ctx+2+1
    omega)
theorem birth (ctx : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family certifiedParameters certifiedPlan certifiedData).birth (key ctx)=
      FormulaSignSlotRadialExternalPrelude.count ctx :=
  (IntegralMixedFramedHistoryFamilyBits.family_birth _ _ _ _).trans (key_prefix ctx)
theorem active (ctx : List Bool) : IntegralMixedFramedClearedMatrixBits.Active certifiedParameters (key ctx) := by
  unfold IntegralMixedFramedClearedMatrixBits.Active
  rw [key_prefix,key_root]
  change FormulaSignSlotRadialExternalPrelude.count ctx<FormulaSignSlotRadialExternalPrelude.count ctx+2
  omega
theorem N_at (ctx : List Bool) : N (key ctx)=FormulaSignSlotRadialExternalPrelude.number ctx :=
  congrArg FormulaSignSlotRadialExternalPrelude.number (key_root ctx)
theorem R_at (ctx : List Bool) : R (key ctx)=FormulaSignSlotRadialExternalPrelude.radius ctx :=
  congrArg FormulaSignSlotRadialExternalPrelude.radius (key_root ctx)

end LeanCanny.Encoding.FormulaSignSlotRadialExternalSlackSource
