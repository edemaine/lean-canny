/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualSpatialTransport
/-! # Finite exponent-mask snapshots for actual cleared-grid tasks -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralClearedCoefficientBits
open LeanCanny.Encoding
set_option backward.isDefEq.respectTransparency false

theorem mask_packet (S : Source) (q : List Bool) (k : ℕ) :
    ClearedCoordinateExponentBits.mask (maskLayout S) (pair q (BinaryNatCode.encode k)) ↔
      ∀ i < S.free q, FixedWidthPolynomial.entry (S.sourceWidth q) k (S.offset q + i) =
        FixedWidthPolynomial.entry (S.targetWidth q) (S.target q) i := by
  unfold ClearedCoordinateExponentBits.mask maskLayout
  simp only [pairFst_pair]
  constructor <;> intro H i hi
  all_goals
    have HS : S.offset q + i < S.arity q := by have := S.fit q; omega
    specialize H i hi
    simpa only [FixedWidthQuery.entry, HS, hi, ite_true, FixedWidthQuery.coordinate_eq_entry,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using H
end LeanCanny.Algebra.IntegralClearedCoefficientBits

namespace LeanCanny.Algebra.IntegralCriticalActualMaskSnapshot
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

noncomputable def maskAt (A : IntegralHistoryCriticalBits.Family) (e k : ℕ) : Prop :=
  let S := IntegralCriticalActualScalarModels.eulerAt A
  ∀ i < S.free [], FixedWidthPolynomial.entry (S.sourceWidth []) k (S.offset [] + i) =
    FixedWidthPolynomial.entry (S.targetWidth []) e i

noncomputable instance (A : IntegralHistoryCriticalBits.Family) (e k : ℕ) : Decidable (maskAt A e k) :=
  Classical.propDecidable _

theorem mask_snapshot (F : Scripts) (q : List Bool) (k : ℕ) :
    ClearedCoordinateExponentBits.mask
      (IntegralClearedCoefficientBits.maskLayout
        (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F)))
      (pair q (BinaryNatCode.encode k)) ↔
    maskAt (IntegralCriticalTotalCreatingBits.atFamily F q) (IntegralCriticalHistoryTask.get F.toParameters .target q) k := by
  rw [IntegralClearedCoefficientBits.mask_packet]
  rfl

theorem maskAt_congr (A B : IntegralHistoryCriticalBits.Family) (e k e' k' : ℕ)
    (hA : A = B) (he : e = e') (hk : k = k') : maskAt A e k ↔ maskAt B e' k' := by
  subst B; subst e'; subst k'
  rfl

end LeanCanny.Algebra.IntegralCriticalActualMaskSnapshot
