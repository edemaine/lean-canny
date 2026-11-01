/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualDerivativeTransport
/-! # Original and derivative branches of actual monomial coefficients -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualMonomialCoefficient
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits IntegralCriticalActualCoefficientModel
open IntegralCriticalActualFactorModel IntegralCriticalActualLowMatrixModel IntegralCriticalActualMonomialSnapshot
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

noncomputable def coefficient (F : Scripts) (q : List Bool) :=
  if IntegralCriticalHistoryTask.get F.toParameters .expression q = 1 then derivative F q else original F q

theorem factorAt_cases (A : IntegralHistoryCriticalBits.Family) (x j k m : ℕ) (hm : m ≠ 0) (r t : ℕ) :
    factorAt A x j k m hm 0 r t = if x = 1 then derivativeAt A j k m hm r t else originalAt A k m hm r t := by
  by_cases h : x = 1
  · subst x
    rw [ite_eq_left rfl]
    rfl
  · rw [ite_eq_right h]
    unfold factorAt factorMatrix monomialAt IntegralMonomialTermBits.factor originalAt
    dsimp only
    simp only [ite_true, ite_eq_right h]
    rfl

theorem coefficient_eq (F : Scripts) (q : List Bool) : coefficient F q =
    factorEntry F q 0 (IntegralCriticalHistoryTask.get F.toParameters .row q % rank F q)
      (IntegralCriticalHistoryTask.get F.toParameters .col q % rank F q) := by
  rw [factor_snapshot, factorAt_cases]
  rfl

theorem monomial_eq_coefficient (F : Scripts) (q : List Bool)
    (h : IntegralCriticalHistoryTask.get F.toParameters .slot8 q = 0) : monomial F q = coefficient F q := by
  unfold monomial
  rw [h]
  exact (coefficient_eq F q).symm

theorem coefficient_leaf (F : Scripts) (h : IntegralCriticalFlatActualSources.Controls F) (q : List Bool)
    (r t : Fin ((IntegralCriticalFlatActualLow.source F).rank q)) :
    (IntegralCriticalFlatActualLow.access F h).coefficient
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))) =
      factorEntry F q 0 r.val t.val := by
  rw [(IntegralCriticalFlatActualLow.access F h).coefficient_eq q r t]
  exact (entryBits_fin (factorMatrix (IntegralCriticalFlatActualLow.source F) q 0) r t).symm

end LeanCanny.Algebra.IntegralCriticalActualMonomialCoefficient
