/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialExternalSlackSource
public import LeanCanny.Algebra.IntegralMixedFramedChargedSlackSpace
/-! # Closed native access to the external marked slack sources -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialExternalSlackAccess
open LeanCanny.Algebra LeanCanny.Computation
open FormulaSignSlotRadialExternalPreludeNative FormulaSignSlotRadialExternalSlackSource

theorem sphere_access : IntegerPolynomialRootQueriesBits.Access sphereSource :=
  IntegralMixedFramedChargedSlackSource.sphereAccess certifiedParameters certifiedAccess certifiedPlan certifiedData
    (fun _ => 1) (fun _ => 1) seed certifiedInputs (BinaryFn.const 1) (BinaryFn.const 1) seed_binary
    certifiedCallerControls certifiedCallerBounds N_unary R_binary

theorem regular_access : IntegerPolynomialRootQueriesBits.Access regularSource :=
  IntegralMixedFramedChargedSlackSource.regularAccess certifiedParameters certifiedAccess certifiedPlan certifiedData
    (fun _ => 1) (fun _ => 1) seed certifiedInputs (BinaryFn.const 1) (BinaryFn.const 1) seed_binary
    certifiedCallerControls certifiedCallerBounds N_unary d_binary R_binary Lam_binary K_binary d_pos

end LeanCanny.Encoding.FormulaSignSlotRadialExternalSlackAccess
