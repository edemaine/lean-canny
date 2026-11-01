/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueRowModel
public import LeanCanny.Algebra.IntegralMixedFullRowBranch

/-! # One native dispatcher for actual value rows and negative Gram entries -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueRowDispatcher
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  (IntegralMixedFullRowBranch.machine P a F h).choose
    ((IntegralMixedValueHomogeneousBranch.machine P a F h).choose
      ((IntegralMixedValueReciprocalBranch.machine P a F h).choose
        ((IntegralMixedValueMacaulayBranch.machine P a F h).choose
          ((IntegralMixedValueGramProductNative.machine P a F h).choose
            ((IntegralMixedValueGramSumNative.machine P a F h).choose zero)))))

private theorem choose_model (M N : Machine) (q : List Bool) :
    (M.choose N).model q = bif M.selected q then M.model q else N.model q := by
  cases hm : M.selected q <;> simp only [Machine.choose, hm] <;> rfl

private theorem model21 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedFullRowBranch.machine P a F h).model = IntegralMixedValueRestoredSource.value P F := rfl
private theorem model22 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedValueHomogeneousBranch.machine P a F h).model = IntegralMixedValueHomogeneousMatrix.value P F := rfl
private theorem model23 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedValueReciprocalBranch.machine P a F h).model = IntegralMixedValueReciprocalMatrix.value P F := rfl
private theorem model24 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedValueMacaulayBranch.machine P a F h).model = IntegralMixedValueMacaulayMatrix.value P F := rfl
private theorem model25 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedValueGramProductNative.machine P a F h).model = IntegralMixedValueGramProductNative.value P F := rfl
private theorem model26 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedValueGramSumNative.machine P a F h).model = IntegralMixedValueGramSumSource.value P F := rfl

private theorem selected21 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedFullRowBranch.machine P a F h).selected = IntegralMixedValueRowModel.selected P 21 := rfl
private theorem selected22 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedValueHomogeneousBranch.machine P a F h).selected = IntegralMixedValueRowModel.selected P 22 := rfl
private theorem selected23 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedValueReciprocalBranch.machine P a F h).selected = IntegralMixedValueRowModel.selected P 23 := rfl
private theorem selected24 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedValueMacaulayBranch.machine P a F h).selected = IntegralMixedValueRowModel.selected P 24 := rfl
private theorem selected25 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedValueGramProductNative.machine P a F h).selected = IntegralMixedValueRowModel.selected P 25 := rfl
private theorem selected26 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (IntegralMixedValueGramSumNative.machine P a F h).selected = IntegralMixedValueRowModel.selected P 26 := rfl

attribute [local irreducible] IntegralMixedFullRowBranch.machine IntegralMixedValueHomogeneousBranch.machine
  IntegralMixedValueReciprocalBranch.machine IntegralMixedValueMacaulayBranch.machine
  IntegralMixedValueGramProductNative.machine IntegralMixedValueGramSumNative.machine

theorem machine_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    (machine P a F h).model q = IntegralMixedValueRowModel.value P F q := by
  simp only [machine, choose_model, selected21, selected22, selected23, selected24, selected25, selected26,
    model21, model22, model23, model24, model25, model26, Bool.cond_eq_ite]
  rfl

private theorem right_selected (M N : Machine) (q : List Bool) (h : N.selected q = true) :
    (M.choose N).selected q = true := by
  change (M.selected q || N.selected q) = true
  rw [h, Bool.or_true]

theorem machine_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    (machine P a F h).selected q = true := by
  unfold machine
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  rfl

theorem model_phase (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : ℕ) (q : List Bool)
    (hlo : 21 ≤ p) (hhi : p ≤ 26) (hv : IntegralMixedVirtualCaps.valid P q)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 2) (hp : phase q = p) :
    (machine P a F h).model q = IntegralMixedValueRowModel.component P F p q :=
  (machine_model P a F h q).trans (IntegralMixedValueRowModel.value_phase P F p q hlo hhi hv hr hp)

theorem canonical (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a F h).model q := by
  rw [machine_model]
  exact IntegralMixedValueRowModel.canonical P F q

end LeanCanny.Algebra.IntegralMixedValueRowDispatcher
