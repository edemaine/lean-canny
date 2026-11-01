/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalCompanionInvariant
/-! # Canonical coefficient targets for flat creating commands -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralHistoryCriticalBits
open LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

theorem coefficientEntry_mod (F : Family) (k r t modulus : ℕ) :
    coefficientEntry F k (r % (source F).rank []) (t % (source F).rank []) modulus =
      coefficientEntry F k r t modulus := by
  unfold coefficientEntry
  dsimp only
  simp only [Nat.mod_mod]
end LeanCanny.Algebra.IntegralHistoryCriticalBits

namespace LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalFlatHeightBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] coefficient leading leadingInteger IntegralHistoryCriticalBits.coefficientEntry

theorem coefficientAt_creating (F : Scripts) (q : List Bool) (h : valid F q) (k r t : ℕ) :
    coefficientAt F q k r t = residueBits (IntegralHistoryCriticalBits.coefficientEntry
      (creatingFamily F q h) k r t (IntegralCriticalHistoryTask.modulus F.toParameters q)) := by
  unfold coefficientAt
  rw [coefficient_creating F q h]
  have HR : oldRank F q = (IntegralHistoryCriticalBits.source (creatingFamily F q h)).rank [] := by
    change _ = FixedWidthPolynomial.count ((creatingFamily F q h).birth []) ((creatingFamily F q h).width [])
    rw [creating_birth]
    rfl
  dsimp only
  rw [HR, IntegralHistoryCriticalBits.coefficientEntry_mod]

theorem coefficientAt_invariance (F : Scripts) (q c : List Bool) (hq : valid F q) (hc : valid F c)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c)
    (k r t : ℕ) : coefficientAt F q k r t = coefficientAt F c k r t := by
  rw [coefficientAt_creating F q hq, coefficientAt_creating F c hc,
    creator_invariance F q c hq hc hr hb, hm]

noncomputable def coefficientValue (F : Scripts) (q : List Bool) : List Bool :=
  coefficientAt F q (IntegralCriticalHistoryTask.get F.toParameters .coefficient q)
    (IntegralCriticalHistoryTask.get F.toParameters .row q) (IntegralCriticalHistoryTask.get F.toParameters .col q)

theorem coefficientValue_invalid (F : Scripts) (q : List Bool) (h : ¬ valid F q) : coefficientValue F q = [] :=
  coefficientAt_invalid F q h _ _ _
end LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
