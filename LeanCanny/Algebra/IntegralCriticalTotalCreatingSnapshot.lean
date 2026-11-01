/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalCreatingSource
public import LeanCanny.Algebra.IntegralCriticalQuerySnapshot
public import LeanCanny.Algebra.IntegralCriticalFlatActualSources
/-! # Concrete source snapshots with separate output query fields -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalSnapshotBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalTotalCompanionBits
set_option backward.isDefEq.respectTransparency false

noncomputable def queryAt (A : IntegralHistoryCriticalBits.Family) (k target r t m : ℕ) (hm : m ≠ 0) : IntegralHistoryCriticalBits.Family :=
  IntegralCriticalScriptQueryBits.family (fun _ => A) {
    coefficientIndex _ := k
    target _ := target
    row _ := ⟨r % count (A.birth []) (A.width []), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    col _ := ⟨t % count (A.birth []) (A.width []), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    modulus _ := m
    modulus_ne_zero _ := hm }

theorem queryAt_congr (A B : IntegralHistoryCriticalBits.Family) (k target r t m k' target' r' t' m' : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hA : A = B) (hk : k = k') (htarget : target = target')
    (hr : r = r') (ht : t = t') (hmod : m = m') :
    queryAt A k target r t m hm = queryAt B k' target' r' t' m' hm' := by
  subst B; subst k'; subst target'; subst r'; subst t'; subst m'
  rfl

noncomputable def family (F : Scripts) (q : List Bool) :=
  queryAt (IntegralCriticalTotalCreatingBits.atFamily F q)
    (IntegralCriticalHistoryTask.get F.toParameters .coefficient q) (IntegralCriticalHistoryTask.get F.toParameters .target q)
    (IntegralCriticalHistoryTask.get F.toParameters .row q) (IntegralCriticalHistoryTask.get F.toParameters .col q)
    (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q)

noncomputable def source (F : Scripts) (q : List Bool) := IntegralHistoryCriticalBits.source (family F q)
noncomputable def euler (F : Scripts) (q : List Bool) := (source F q).toEuler
noncomputable def relative (F : Scripts) (q : List Bool) := IntegralClearedCriticalBits.relativeSource (source F q)
noncomputable def reduction (F : Scripts) (q : List Bool) := IntegralPurePowerActionBits.reductionSource (relative F q)
noncomputable def action (F : Scripts) (q : List Bool) := IntegralReductionActionBits.actionSource (reduction F q)

attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily

theorem source_value (F : Scripts) (q : List Bool) : (IntegralCriticalTotalCreatingBits.source F).value q = (source F q).value [] := rfl

theorem action_value (F : Scripts) (q : List Bool) : (IntegralCriticalFlatActualSources.characteristic F).value q = (action F q).value [] := rfl

theorem reduction_matrix (F : Scripts) (q : List Bool) : (IntegralCriticalFlatActualSources.reduction F).matrix q = (reduction F q).matrix [] := rfl

theorem action_matrix (F : Scripts) (q : List Bool) : (IntegralCriticalFlatActualSources.characteristic F).matrix q = (action F q).matrix [] := rfl

theorem power_matrix (F : Scripts) (q : List Bool) : (IntegralCriticalFlatActualSources.characteristic F).powerMatrix q = (action F q).powerMatrix [] := rfl

theorem family_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c)
    (hk : IntegralCriticalHistoryTask.get F.toParameters .coefficient q = IntegralCriticalHistoryTask.get F.toParameters .coefficient c)
    (htarget : IntegralCriticalHistoryTask.get F.toParameters .target q = IntegralCriticalHistoryTask.get F.toParameters .target c)
    (hrow : IntegralCriticalHistoryTask.get F.toParameters .row q = IntegralCriticalHistoryTask.get F.toParameters .row c)
    (hcol : IntegralCriticalHistoryTask.get F.toParameters .col q = IntegralCriticalHistoryTask.get F.toParameters .col c) : family F q = family F c :=
  queryAt_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (IntegralCriticalTotalCreatingBits.atFamily_invariance F q c hr hb) hk htarget hrow hcol hm

theorem action_value_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c)
    (hk : IntegralCriticalHistoryTask.get F.toParameters .coefficient q = IntegralCriticalHistoryTask.get F.toParameters .coefficient c)
    (htarget : IntegralCriticalHistoryTask.get F.toParameters .target q = IntegralCriticalHistoryTask.get F.toParameters .target c)
    (hrow : IntegralCriticalHistoryTask.get F.toParameters .row q = IntegralCriticalHistoryTask.get F.toParameters .row c)
    (hcol : IntegralCriticalHistoryTask.get F.toParameters .col q = IntegralCriticalHistoryTask.get F.toParameters .col c) :
    (IntegralCriticalFlatActualSources.characteristic F).value q = (IntegralCriticalFlatActualSources.characteristic F).value c := by
  rw [action_value, action_value]
  exact congrArg (fun A => (IntegralCriticalQuerySnapshotBits.canonicalAction A).value [])
    (family_invariance F q c hr hb hm hk htarget hrow hcol)
theorem family_next (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase) (q : List Bool) :
    family F (IntegralCriticalFlatEulerBits.next F.toParameters phase q) = family F q :=
  family_invariance F _ q
    (IntegralCriticalFlatEulerBits.next_root _ _ _) (IntegralCriticalFlatEulerBits.next_birth _ _ _)
    (IntegralCriticalFlatEulerBits.next_modulus _ _ _) (IntegralCriticalFlatEulerBits.next_get _ _ _ _)
    (IntegralCriticalFlatEulerBits.next_get _ _ _ _) (IntegralCriticalFlatEulerBits.next_get _ _ _ _)
    (IntegralCriticalFlatEulerBits.next_get _ _ _ _)

theorem source_next_value (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase) (q : List Bool) :
    (IntegralCriticalTotalCreatingBits.source F).value (IntegralCriticalFlatEulerBits.next F.toParameters phase q) =
      (IntegralCriticalTotalCreatingBits.source F).value q := by
  rw [source_value, source_value]
  exact congrArg (fun A => (IntegralHistoryCriticalBits.source A).value []) (family_next F phase q)

theorem action_next_value (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase) (q : List Bool) :
    (IntegralCriticalFlatActualSources.characteristic F).value (IntegralCriticalFlatEulerBits.next F.toParameters phase q) =
      (IntegralCriticalFlatActualSources.characteristic F).value q :=
  action_value_invariance F _ q
    (IntegralCriticalFlatEulerBits.next_root _ _ _) (IntegralCriticalFlatEulerBits.next_birth _ _ _)
    (IntegralCriticalFlatEulerBits.next_modulus _ _ _) (IntegralCriticalFlatEulerBits.next_get _ _ _ _)
    (IntegralCriticalFlatEulerBits.next_get _ _ _ _) (IntegralCriticalFlatEulerBits.next_get _ _ _ _)
    (IntegralCriticalFlatEulerBits.next_get _ _ _ _)

end LeanCanny.Algebra.IntegralCriticalTotalSnapshotBits
