/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedScalarQueries
/-! # Concrete constant-query snapshots of the virtual generating algebra

These snapshots freeze the actual saved mixed-prefix word and its nilpotent
algebra. Output indices remain explicit natural arguments, so later transport
uses only field readbacks and never an assumed source-equality oracle.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualSnapshotBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
set_option backward.isDefEq.respectTransparency false

def constantQueries (j k e r t m : ℕ) (hm : m ≠ 0) : Queries where
  coordinate _ := j
  coefficientIndex _ := k
  target _ := e
  row _ := r
  col _ := t
  modulus _ := m
  modulus_ne_zero _ := hm

noncomputable def sourceAt (F : Family) (key : List Bool) (j k e r t m : ℕ) (hm : m ≠ 0) :
    IntegralClearedCriticalBits.Source :=
  IntegralMixedVirtualSweepSource.source (pull F (fun _ => key))
    (indices (pull F (fun _ => key)) (constantQueries j k e r t m hm))

theorem sourceAt_modulus (F : Family) (key : List Bool) (j k e r t m n : ℕ)
    (hm : m ≠ 0) (hn : n ≠ 0) (he : m = n) :
    sourceAt F key j k e r t m hm = sourceAt F key j k e r t n hn := by
  subst n
  rfl

noncomputable def family (P : Parameters) (F : Family) (q : List Bool) :=
  sourceAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .coefficient q)
    (get P .target q) (get P .row q) (get P .col q) (modulus P q) (modulus_ne_zero P q)

noncomputable abbrev eulerAt (P : Parameters) (F : Family) (q : List Bool) := (family P F q).toEuler

theorem value_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    (IntegralMixedVirtualTaskBits.source P F).value q = (family P F q).value [] := rfl

theorem family_invariance (P : Parameters) (F : Family) (q c : List Bool)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hx : get P .slot15 c = get P .slot15 q) (hj : get P .slot13 c = get P .slot13 q)
    (hk : get P .coefficient c = get P .coefficient q) (he : get P .target c = get P .target q)
    (hi : get P .row c = get P .row q) (ht : get P .col c = get P .col q) (hm : modulus P c = modulus P q) :
    family P F c = family P F q := by
  unfold family
  rw [IntegralMixedVirtualTaskBits.saved_invariance P q c hr hb hx, hj, hk, he, hi, ht]
  apply sourceAt_modulus
  exact hm

theorem family_next (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    family P F (IntegralCriticalFlatEulerBits.next P p q) = family P F q := by
  apply family_invariance
  · exact IntegralCriticalFlatEulerBits.next_root P p q
  · exact IntegralCriticalFlatEulerBits.next_birth P p q
  · exact IntegralCriticalFlatEulerBits.next_get P p q .slot15
  · exact IntegralCriticalFlatEulerBits.next_get P p q .slot13
  · exact IntegralCriticalFlatEulerBits.next_get P p q .coefficient
  · exact IntegralCriticalFlatEulerBits.next_get P p q .target
  · exact IntegralCriticalFlatEulerBits.next_get P p q .row
  · exact IntegralCriticalFlatEulerBits.next_get P p q .col
  · exact IntegralCriticalFlatEulerBits.next_modulus P p q

noncomputable def selectedAt (P : Parameters) (F : Family) (q : List Bool) (j : ℕ) (c : List Bool) :
    Fin ((eulerAt P F q).free c) :=
  ⟨j % (eulerAt P F q).free c, Nat.mod_lt _ ((eulerAt P F q).free_pos c)⟩
noncomputable def lower (P : Parameters) (F : Family) (q : List Bool) :=
  (eulerAt P F q).lowerValue (selectedAt P F q (get P .derivative q)) []
noncomputable def objective (P : Parameters) (F : Family) (q : List Bool) := (eulerAt P F q).objectiveValue []
noncomputable def sum (P : Parameters) (F : Family) (q : List Bool) := (eulerAt P F q).sumValue []
noncomputable def frozenLower (P : Parameters) (F : Family) (q : List Bool) := (eulerAt P F q).toGradient.toFrozen.lowerValue []
noncomputable def frozenConstant (P : Parameters) (F : Family) (q : List Bool) := (eulerAt P F q).toGradient.toFrozen.constantValue []
noncomputable def frozenSum (P : Parameters) (F : Family) (q : List Bool) := (eulerAt P F q).toGradient.toFrozen.sumValue []
noncomputable def frozenTerm (P : Parameters) (F : Family) (q : List Bool) :=
  IntegralFrozenPowerBits.termProgram (eulerAt P F q).toGradient.toFrozen (pair [] (BinaryNatCode.encode (get P .slot8 q)))

theorem lower_eq (P : Parameters) (F : Family) (q : List Bool) : lower P F q =
    (IntegralMixedVirtualTaskBits.arithmetic P F).lowerValue
      (IntegralCriticalFlatEulerRowsBits.selected P (IntegralMixedVirtualTaskBits.arithmetic P F)) q := rfl
theorem objective_eq (P : Parameters) (F : Family) (q : List Bool) : objective P F q =
    (IntegralMixedVirtualTaskBits.arithmetic P F).objectiveValue q := rfl
theorem sum_eq (P : Parameters) (F : Family) (q : List Bool) : sum P F q =
    (IntegralMixedVirtualTaskBits.arithmetic P F).sumValue q := rfl
theorem frozenLower_eq (P : Parameters) (F : Family) (q : List Bool) : frozenLower P F q =
    (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient.toFrozen.lowerValue q := rfl
theorem frozenConstant_eq (P : Parameters) (F : Family) (q : List Bool) : frozenConstant P F q =
    (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient.toFrozen.constantValue q := rfl
theorem frozenSum_eq (P : Parameters) (F : Family) (q : List Bool) : frozenSum P F q =
    (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient.toFrozen.sumValue q := rfl

theorem objective_next (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    objective P F (IntegralCriticalFlatEulerBits.next P p q) = objective P F q := by
  unfold objective eulerAt
  rw [family_next]
theorem sum_next (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    sum P F (IntegralCriticalFlatEulerBits.next P p q) = sum P F q := by
  unfold sum eulerAt
  rw [family_next]
theorem frozenLower_next (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    frozenLower P F (IntegralCriticalFlatEulerBits.next P p q) = frozenLower P F q := by
  unfold frozenLower eulerAt
  rw [family_next]
theorem frozenConstant_next (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    frozenConstant P F (IntegralCriticalFlatEulerBits.next P p q) = frozenConstant P F q := by
  unfold frozenConstant eulerAt
  rw [family_next]
theorem frozenSum_next (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    frozenSum P F (IntegralCriticalFlatEulerBits.next P p q) = frozenSum P F q := by
  unfold frozenSum eulerAt
  rw [family_next]
end LeanCanny.Algebra.IntegralMixedVirtualSnapshotBits
