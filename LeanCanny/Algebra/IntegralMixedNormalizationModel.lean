/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationNodes
/-! # Direct access to the selected native normalization model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedNormalizationTopBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem nodes_length (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) : (nodes P a F h hd height hb).length = 14 := rfl

noncomputable def nodeAt (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) (i : Fin 14) : PhaseNode phase :=
  (nodes P a F h hd height hb).get ⟨i.val, by rw [nodes_length]; exact i.isLt⟩

theorem nodeAt_mem (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) (i : Fin 14) :
    nodeAt P a F h hd height hb i ∈ nodes P a F h hd height hb := List.get_mem _ _

theorem model_selected_index (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) (q : List Bool) (i : Fin 14)
    (hs : (nodeAt P a F h hd height hb i).machine.selected q = true) :
    (machine P a F h hd height hb).model q = (nodeAt P a F h hd height hb i).machine.model q :=
  model_selected_node P a F h hd height hb q _ (nodeAt_mem P a F h hd height hb i) hs

theorem model_at_index (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) (q : List Bool) (i : Fin 14)
    (hp : phase q = (nodeAt P a F h hd height hb i).code) :
    (machine P a F h hd height hb).model q =
      if (nodeAt P a F h hd height hb i).machine.selected q then (nodeAt P a F h hd height hb i).machine.model q
      else (stage14 P a F h hd).model q := by
  rw [machine_eq_dispatch]
  exact phaseDispatch_model_at_code _ _ q _ (nodes_distinct P a F h hd height hb)
    (nodeAt_mem P a F h hd height hb i) hp

theorem fallback_not14 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) (q : List Bool)
    (hp : phase q ≠ 14) : (stage14 P a F h hd).model q = [] := by
  have HS : selected P .eulerSum q = false := by
    cases hs : selected P .eulerSum q with
    | false => rfl
    | true =>
      have HP := ((selected_iff P .eulerSum q).mp hs).2.2
      exact False.elim (hp HP)
  have HM : selected14Matrix P F q = false := by
    unfold selected14Matrix
    rw [HS, Bool.false_and]
  rw [stage14_model]
  simp only [top14, low14, HM, Bool.false_and, Bool.false_eq_true, ite_false]

end LeanCanny.Algebra.IntegralMixedNormalizationDispatcherBits
