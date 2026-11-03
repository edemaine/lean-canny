/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordCaller
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardProfile
/-! # Actual original marked-record costs for physical correlation coefficients

The query-key, birth and exponent-word readers are ordinary packet metadata.
All algebraic coefficients, leading scalars and modulus planning come from
the actual original term/radius/record backend; none is supplied as an oracle.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCriticalGuard
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)
local notation "P" => certifiedParameters hn ht ha hR
local notation "D" => certifiedPlan hn ht ha hR
local notation "H" => certifiedData hn ht ha hR

noncomputable def tables := (certifiedControls hn ht ha hR).normalization.tables
noncomputable def polynomial (key : List Bool→List Bool) (stage : List Bool→ℕ) :=
  IntegralMixedFramedCriticalGuardBits.polynomial P D H (tables hn ht ha hR) key stage

theorem coefficient_evaluator (key : List Bool→List Bool) (stage W : List Bool→ℕ)
    (target modulus : List Bool→List Bool) (hk : key∈FP) (hj : UnaryFn stage)
    (hW : UnaryFn W) (htarget : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (IntegralMixedFramedCriticalGuardBits.count P (tables hn ht ha hR) key)
      W (polynomial hn ht ha hR key stage) target modulus) :=
  IntegralMixedFramedCriticalGuardBits.coefficient_evaluator P (certifiedAccess hn ht ha hR) D H
    (callerData hn ht ha hR) (callerControls hn ht ha hR) (callerBounds hn ht ha hR)
    (tables hn ht ha hR) (certifiedControls hn ht ha hR).normalization.native
    key stage W target modulus hk hj hW htarget hm

theorem polynomial_mass (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool) :
    MvMass.mass (polynomial hn ht ha hR key stage q)≤2^IntegralMixedFramedCriticalGuardBits.mass P
      (fun _=>3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) key q :=
  IntegralMixedFramedCriticalGuardBits.polynomial_mass P D H (tables hn ht ha hR) key stage
    (fun _=>3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (certifiedInputs hn ht ha hR) q
end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCriticalGuard
