/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalCompanionInvariant
public import LeanCanny.Algebra.IntegralCriticalFlatCoefficient
/-! # Concrete canonical sources indexed only by root, birth, and modulus

Output matrix ranks and spatial targets are selected after constructing
these sources. Task phase, row, column, and auxiliary query fields do not
participate in their actual polynomial or old algebra.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalCreatingRetargetBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits
set_option backward.isDefEq.respectTransparency false

noncomputable def family (F : Scripts) (q : List Bool) (h : IntegralCriticalTotalCompanionBits.valid F q) : IntegralHistoryCriticalBits.Family :=
  { IntegralCriticalFlatHeightBits.creatingFamily F q h with
    modulus := fun _ => IntegralCriticalHistoryTask.modulus F.toParameters q
    modulus_ne_zero := fun _ => IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q }

theorem family_invariance (F : Scripts) (q c : List Bool)
    (hq : IntegralCriticalTotalCompanionBits.valid F q) (hc : IntegralCriticalTotalCompanionBits.valid F c)
    (hr : IntegralCriticalTotalCompanionBits.root q = IntegralCriticalTotalCompanionBits.root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c) :
    family F q hq = family F c hc := by
  unfold family
  rw [creator_invariance F q c hq hc hr hb]
  simp only [hm]

noncomputable def source (F : Scripts) (q : List Bool) (h : IntegralCriticalTotalCompanionBits.valid F q) :=
  IntegralHistoryCriticalBits.source (family F q h)
noncomputable def euler (F : Scripts) (q : List Bool) (h : IntegralCriticalTotalCompanionBits.valid F q) := (source F q h).toEuler
noncomputable def relative (F : Scripts) (q : List Bool) (h : IntegralCriticalTotalCompanionBits.valid F q) :=
  IntegralClearedCriticalBits.relativeSource (source F q h)
noncomputable def reduction (F : Scripts) (q : List Bool) (h : IntegralCriticalTotalCompanionBits.valid F q) :=
  IntegralPurePowerActionBits.reductionSource (relative F q h)
noncomputable def action (F : Scripts) (q : List Bool) (h : IntegralCriticalTotalCompanionBits.valid F q) :=
  IntegralReductionActionBits.actionSource (reduction F q h)

theorem source_invariance (F : Scripts) (q c : List Bool)
    (hq : IntegralCriticalTotalCompanionBits.valid F q) (hc : IntegralCriticalTotalCompanionBits.valid F c)
    (hr : IntegralCriticalTotalCompanionBits.root q = IntegralCriticalTotalCompanionBits.root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c) :
    source F q hq = source F c hc := congrArg IntegralHistoryCriticalBits.source (family_invariance F q c hq hc hr hb hm)

theorem euler_invariance (F : Scripts) (q c : List Bool)
    (hq : IntegralCriticalTotalCompanionBits.valid F q) (hc : IntegralCriticalTotalCompanionBits.valid F c)
    (hr : IntegralCriticalTotalCompanionBits.root q = IntegralCriticalTotalCompanionBits.root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c) :
    euler F q hq = euler F c hc := congrArg IntegralClearedCriticalBits.Source.toEuler (source_invariance F q c hq hc hr hb hm)

theorem relative_invariance (F : Scripts) (q c : List Bool)
    (hq : IntegralCriticalTotalCompanionBits.valid F q) (hc : IntegralCriticalTotalCompanionBits.valid F c)
    (hr : IntegralCriticalTotalCompanionBits.root q = IntegralCriticalTotalCompanionBits.root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c) :
    relative F q hq = relative F c hc := congrArg IntegralClearedCriticalBits.relativeSource (source_invariance F q c hq hc hr hb hm)

theorem reduction_invariance (F : Scripts) (q c : List Bool)
    (hq : IntegralCriticalTotalCompanionBits.valid F q) (hc : IntegralCriticalTotalCompanionBits.valid F c)
    (hr : IntegralCriticalTotalCompanionBits.root q = IntegralCriticalTotalCompanionBits.root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c) :
    reduction F q hq = reduction F c hc := congrArg IntegralPurePowerActionBits.reductionSource (relative_invariance F q c hq hc hr hb hm)

theorem action_invariance (F : Scripts) (q c : List Bool)
    (hq : IntegralCriticalTotalCompanionBits.valid F q) (hc : IntegralCriticalTotalCompanionBits.valid F c)
    (hr : IntegralCriticalTotalCompanionBits.root q = IntegralCriticalTotalCompanionBits.root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c) :
    action F q hq = action F c hc := congrArg IntegralReductionActionBits.actionSource (reduction_invariance F q c hq hc hr hb hm)
end LeanCanny.Algebra.IntegralCriticalCreatingRetargetBits
