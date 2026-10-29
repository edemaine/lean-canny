/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexAffineLevelCircuit

/-! # Exact ancestral level values and circuit completion -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.AffineLevel
open scoped Classical BigOperators

def value (C : Inputs) (x : ℕ → ℂ) : ℂ := if C.mode = 1 then
  ∑ i ∈ Finset.range C.count, (C.normal i : ℂ) * x (C.left + i)
  else if C.mode = 2 then
    (∑ i ∈ Finset.range C.count, (C.normal i : ℂ) * x (C.left + i)) +
      ∑ i ∈ Finset.range C.count, (C.normal i : ℂ) * x (C.right + i)
  else (C.constant : ℂ)

private theorem table_hold (C : Inputs) (env : ℕ → ℂ) (hg : ∀ g ∈ gates C, g.Holds env) :
    ∀ g ∈ StraightLine.gates (tableBase C) (ConstantTable.program C.count C.normal), g.Holds env := by
  intro g h
  apply hg g
  rw [gates_eq]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ h))

private theorem left_hold (C : Inputs) (env : ℕ → ℂ) (hg : ∀ g ∈ gates C, g.Holds env) :
    ∀ g ∈ StraightLine.gates (leftBase C) (leftRow C), g.Holds env := by
  intro g h
  apply hg g
  rw [gates_eq]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _ h)))

private theorem right_hold (C : Inputs) (env : ℕ → ℂ) (hg : ∀ g ∈ gates C, g.Holds env) :
    ∀ g ∈ StraightLine.gates (rightBase C) (rightRow C), g.Holds env := by
  intro g h
  apply hg g
  rw [gates_eq]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ h))))

theorem values_sound (C : Inputs) (env : ℕ → ℂ) (hg : ∀ g ∈ gates C, g.Holds env) :
    env (constantWire C) = (C.constant : ℂ) ∧
      env (leftOutput C) = (∑ i ∈ Finset.range C.count, (C.normal i : ℂ) * env (C.left + i)) ∧
      env (rightOutput C) = (∑ i ∈ Finset.range C.count, (C.normal i : ℂ) * env (C.right + i)) ∧
      env (sumOutput C) = (∑ i ∈ Finset.range C.count, (C.normal i : ℂ) * env (C.left + i)) +
        ∑ i ∈ Finset.range C.count, (C.normal i : ℂ) * env (C.right + i) := by
  have hz : env C.base = 0 := by
    simpa only [Gate.Holds, Int.cast_zero] using hg (.constant C.base 0) (by rw [gates_eq]; simp)
  have hc : env (constantWire C) = (C.constant : ℂ) := hg (.constant (constantWire C) C.constant) (by rw [gates_eq]; simp)
  have ht (i : ℕ) (hi : i < C.count) : env (tableBase C + i) = (C.normal i : ℂ) :=
    ConstantTable.sound _ _ _ env (table_hold C env hg) i hi
  have hl := AffineRow.height_sound C.base (leftBase C) C.left C.count C.base (fun i => tableBase C + i)
    env hz (left_hold C env hg)
  have hr := AffineRow.height_sound C.base (rightBase C) C.right C.count C.base (fun i => tableBase C + i)
    env hz (right_hold C env hg)
  simp only [hz, sub_zero] at hl hr
  have hl' : env (leftOutput C) = ∑ i ∈ Finset.range C.count, (C.normal i : ℂ) * env (C.left + i) := by
    apply hl.trans
    apply Finset.sum_congr rfl
    intro i hi
    rw [ht i (Finset.mem_range.mp hi)]
  have hr' : env (rightOutput C) = ∑ i ∈ Finset.range C.count, (C.normal i : ℂ) * env (C.right + i) := by
    apply hr.trans
    apply Finset.sum_congr rfl
    intro i hi
    rw [ht i (Finset.mem_range.mp hi)]
  have hs := hg (.add (sumOutput C) (leftOutput C) (rightOutput C)) (by rw [gates_eq]; simp)
  exact ⟨hc, hl', hr', hs.trans (congrArg₂ (· + ·) hl' hr')⟩

theorem output_sound (C : Inputs) (env : ℕ → ℂ) (hg : ∀ g ∈ gates C, g.Holds env) : env (output C) = value C env := by
  obtain ⟨hc, hl, _, hs⟩ := values_sound C env hg
  unfold output value
  split_ifs
  · exact hl
  · exact hs
  · exact hc

theorem value_congr (C : Inputs) (h : C.Valid) (x y : ℕ → ℂ) (hxy : ∀ i < C.base, x i = y i) : value C x = value C y := by
  have hl : (∑ i ∈ Finset.range C.count, (C.normal i : ℂ) * x (C.left + i)) =
      ∑ i ∈ Finset.range C.count, (C.normal i : ℂ) * y (C.left + i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hxy _ (by have H := h.left; have Hi := Finset.mem_range.mp hi; omega)]
  have hr : (∑ i ∈ Finset.range C.count, (C.normal i : ℂ) * x (C.right + i)) =
      ∑ i ∈ Finset.range C.count, (C.normal i : ℂ) * y (C.right + i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hxy _ (by have H := h.right; have Hi := Finset.mem_range.mp hi; omega)]
  unfold value
  split_ifs
  · exact hl
  · exact congrArg₂ (· + ·) hl hr
  · rfl

theorem exists_completion (C : Inputs) (h : C.Valid) (x : ℕ → ℂ) :
    ∃ env : ℕ → ℂ, (∀ i < C.base, env i = x i) ∧ (∀ g ∈ gates C, g.Holds env) ∧ env (output C) = value C x := by
  obtain ⟨env, hp, hg⟩ := StraightLine.exists_completion x C.base (program C) (wellFormed C h)
  exact ⟨env, hp, hg, (output_sound C env hg).trans (value_congr C h env x hp)⟩

end LeanCanny.ETR.ComplexCircuit.AffineLevel
