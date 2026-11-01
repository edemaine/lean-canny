/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationModel
/-! # Normalization factor requests outside their finite matrix return zero -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.modulus

theorem factorValue_outside (P : Parameters) (F : Family) (q : List Bool)
    (ha : ¬ (get P .row q < factorSize P F q ∧ get P .col q < factorSize P F q)) :
    factorValue P F q = [] := by
  unfold factorValue
  rw [power_snapshot]
  unfold IntegralCriticalTotalSnapshotBits.integerEntry
  split_ifs with hr ht
  · exact False.elim (ha ⟨hr, ht⟩)
  · exact integerZeroBits (modulus P q)
  · exact integerZeroBits (modulus P q)

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
namespace LeanCanny.Algebra.IntegralMixedNormalizationDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedNormalizationTopBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] factorValue

theorem model_factor (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 5)
    (hp : isPhase .productEntry q) :
    (machine P a F h hd height hb).model q = factorValue P F q := by
  by_cases ha : get P .row q < factorSize P F q ∧ get P .col q < factorSize P F q
  · exact model_selected_index P a F h hd height hb q ⟨5, by decide⟩
      ((selected5_iff P F q).mpr ⟨⟨hv, hr, hp⟩, ha⟩)
  · have HS : (nodeAt P a F h hd height hb ⟨5, by decide⟩).machine.selected q = false := by
      change selected5 P F q = false
      cases hs : selected5 P F q with
      | false => rfl
      | true => exact False.elim (ha ((selected5_iff P F q).mp hs).2)
    have HP : phase q = (nodeAt P a F h hd height hb ⟨5, by decide⟩).code := hp
    rw [model_at_index P a F h hd height hb q ⟨5, by decide⟩ HP, HS, ite_eq_right (by decide)]
    rw [fallback_not14 P a F h hd q (by change phase q = 5 at hp; omega)]
    exact (factorValue_outside P F q ha).symm

end LeanCanny.Algebra.IntegralMixedNormalizationDispatcherBits
