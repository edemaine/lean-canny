/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscContextUpperModel
public import LeanCanny.Algebra.IntegralMixedPscContextAction
/-! # One native dispatcher for actual PSC determinant arithmetic -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscContextUpperDispatcher
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedPscUpperBits (entryValue momentValue factorValue characteristicValue
  entry_outside factor_outside characteristic_outside moment_snapshot)
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedPscContextUpperBits
open scoped Classical

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  (IntegralMixedPscContextActionBits.machine P a F h).choose ((stage1 P a F h).choose
    ((stage2 P a F h).choose ((stage3 P a F h).choose ((stage4 P a F h).choose zero))))

private theorem choose_model (M N : Machine) (q : List Bool) :
    (M.choose N).model q = bif M.selected q then M.model q else N.model q := by
  cases hm : M.selected q <;> simp only [Machine.choose, hm] <;> rfl

private theorem model0 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedPscContextActionBits.machine P a F h).model = IntegralMixedPscActionBits.value P F := rfl
private theorem model1 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage1 P a F h).model = entryValue P F := rfl
private theorem model2 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage2 P a F h).model = momentValue P F := rfl
private theorem model3 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage3 P a F h).model = factorValue P F := rfl
private theorem model4 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage4 P a F h).model = characteristicValue P F := rfl

private theorem selected0 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedPscContextActionBits.machine P a F h).selected = selected P F .originalCoefficient := rfl
private theorem selected1 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage1 P a F h).selected = fun q => decide (Selected1 P F q) := rfl
private theorem selected2 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage2 P a F h).selected = selected P F .clearedHeight := rfl
private theorem selected3 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage3 P a F h).selected = selected3 P F := rfl
private theorem selected4 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage4 P a F h).selected = fun q => decide (Selected4 P F q) := rfl

attribute [local irreducible] IntegralMixedPscContextActionBits.machine stage1 stage2 stage3 stage4

theorem machine_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    (machine P a F h).model q = IntegralMixedPscContextUpperModel.value P F q := by
  simp only [machine, choose_model, model0, model1, model2, model3, model4,
    selected0, selected1, selected2, selected3, selected4, Bool.cond_eq_ite]
  rfl

private theorem right_selected (M N : Machine) (q : List Bool) (hn : N.selected q = true) :
    (M.choose N).selected q = true := by
  change (M.selected q || N.selected q) = true
  rw [hn, Bool.or_true]

theorem machine_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    (machine P a F h).selected q = true := by
  unfold machine
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  rfl

theorem canonical (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a F h).model q := by
  rw [machine_model]
  exact IntegralMixedPscContextUpperModel.canonical P F q

end LeanCanny.Algebra.IntegralMixedPscContextUpperDispatcher
