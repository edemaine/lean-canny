/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualGradientSnapshot
/-! # Natural queried entries of the actual creating lower polynomials -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualLowerEntry
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily

noncomputable def lowerEntryAt (A : IntegralHistoryCriticalBits.Family) (j e r t m : ℕ) (hm : m ≠ 0) :=
  IntegralCriticalActualScalarModels.lowerAt (IntegralCriticalActualGradientSnapshot.queried A e r t m hm) j

theorem lower_snapshot (F : Scripts) (q : List Bool) :
    IntegralCriticalActualScalarModels.lower F q =
      lowerEntryAt (IntegralCriticalTotalCreatingBits.atFamily F q)
        (IntegralCriticalHistoryTask.get F.toParameters .derivative q)
        (IntegralCriticalHistoryTask.get F.toParameters .target q)
        (IntegralCriticalHistoryTask.get F.toParameters .row q) (IntegralCriticalHistoryTask.get F.toParameters .col q)
        (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) := rfl

theorem lowerEntryAt_congr (A B : IntegralHistoryCriticalBits.Family)
    (j e r t m j' e' r' t' m' : ℕ) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hA : A = B) (hj : j = j') (he : e = e') (hr : r = r') (ht : t = t') (hmod : m = m') :
    lowerEntryAt A j e r t m hm = lowerEntryAt B j' e' r' t' m' hm' := by
  subst B; subst j'; subst e'; subst r'; subst t'; subst m'
  rfl

theorem lower_transport (F : Scripts) (child q : List Bool) (j e r t : ℕ)
    (hroot : root child = root q)
    (hbirth : IntegralCriticalHistoryTask.birth F.toParameters child = IntegralCriticalHistoryTask.birth F.toParameters q)
    (hmod : IntegralCriticalHistoryTask.modulus F.toParameters child = IntegralCriticalHistoryTask.modulus F.toParameters q)
    (hj : IntegralCriticalHistoryTask.get F.toParameters .derivative child = j)
    (he : IntegralCriticalHistoryTask.get F.toParameters .target child = e)
    (hr : IntegralCriticalHistoryTask.get F.toParameters .row child = r)
    (ht : IntegralCriticalHistoryTask.get F.toParameters .col child = t) :
    IntegralCriticalActualScalarModels.lower F child =
      lowerEntryAt (IntegralCriticalTotalCreatingBits.atFamily F q) j e r t
        (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) := by
  rw [lower_snapshot]
  exact lowerEntryAt_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (IntegralCriticalTotalCreatingBits.atFamily_invariance F child q hroot hbirth) hj he hr ht hmod

end LeanCanny.Algebra.IntegralCriticalActualLowerEntry
