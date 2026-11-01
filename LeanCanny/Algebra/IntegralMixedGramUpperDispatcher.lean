/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramUpperModel
/-! # One native dispatcher for actual Gram determinant arithmetic -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramUpperDispatcher
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedGramUpperBits
open scoped Classical

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  (IntegralMixedGramBlockEntryNative.machine P a F h).choose ((stage21 P a F h).choose
    ((stage22 P a F h).choose ((stage23 P a F h).choose ((stage24 P a F h).choose zero))))

private theorem choose_model (M N : Machine) (q : List Bool) :
    (M.choose N).model q = bif M.selected q then M.model q else N.model q := by
  cases hm : M.selected q <;> simp only [Machine.choose, hm] <;> rfl

private theorem model19 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedGramBlockEntryNative.machine P a F h).model = IntegralMixedGramBlockEntryNative.value P F := rfl
private theorem model21 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage21 P a F h).model = entryValue P F := rfl
private theorem model22 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage22 P a F h).model = momentValue P F := rfl
private theorem model23 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage23 P a F h).model = IntegralMixedGramMatrixModel.factorValue P F := rfl
private theorem model24 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage24 P a F h).model = characteristicValue P F := rfl

private theorem selected19 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedGramBlockEntryNative.machine P a F h).selected = selected P .actionEntry := rfl
private theorem selected21 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage21 P a F h).selected = fun q => decide (Selected21 P F q) := rfl
private theorem selected22 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage22 P a F h).selected = selected P .momentPower := rfl
private theorem selected23 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage23 P a F h).selected = selectedFinite P .relativeFactor (factorSize P F) := rfl
private theorem selected24 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (stage24 P a F h).selected = selectedFinite P .relativePower (fun q => (characteristic P F).rank q) := rfl

attribute [local irreducible] IntegralMixedGramBlockEntryNative.machine stage21 stage22 stage23 stage24

theorem machine_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    (machine P a F h).model q = IntegralMixedGramUpperModel.value P F q := by
  simp only [machine, choose_model, model19, model21, model22, model23, model24,
    selected19, selected21, selected22, selected23, selected24, Bool.cond_eq_ite]
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
  exact IntegralMixedGramUpperModel.canonical P F q

end LeanCanny.Algebra.IntegralMixedGramUpperDispatcher
