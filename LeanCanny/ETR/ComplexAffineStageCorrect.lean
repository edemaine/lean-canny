/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexAffineStageCircuit

/-! # Original source and affine row semantics at one shared assignment -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.AffineStage
open MvPolynomial
open scoped Classical BigOperators

theorem zero_sound (C : Inputs) (env : ℕ → ℂ) (hg : ∀ g ∈ gates C, g.Holds env) : env C.base = 0 := by
  simpa only [Gate.Holds, Int.cast_zero] using hg (.constant C.base 0) (by rw [gates_eq]; simp)

theorem copies_hold (C : Inputs) (env : ℕ → ℂ) (hg : ∀ g ∈ gates C, g.Holds env) :
    ∀ g ∈ GradientFamily.gates C.base (copyBase C) C.start C.ambient C.source C.count, g.Holds env := by
  intro g h
  apply hg g
  rw [gates_eq]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ h)

theorem gradient_hold (C : Inputs) (env : ℕ → ℂ) (hg : ∀ g ∈ gates C, g.Holds env)
    (i : ℕ) (hi : i < C.count) : ∀ g ∈ StraightLine.gates (gradientStart C i) (gradientRow C i), g.Holds env := by
  intro g h
  apply hg g
  rw [gates_eq]
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  apply List.mem_append_left
  rw [gradientGates_range]
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, h⟩

theorem height_hold (C : Inputs) (env : ℕ → ℂ) (hg : ∀ g ∈ gates C, g.Holds env)
    (r : ℕ) (hr : r < C.count) : ∀ g ∈ StraightLine.gates (heightStart C r) (heightRow C r), g.Holds env := by
  intro g h
  apply hg g
  rw [gates_eq]
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  apply List.mem_append_right
  rw [heightGates_range]
  exact List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, h⟩

theorem source_sound (C : Inputs) (h : C.Valid) (wire : ℕ → MvPolynomial ℕ ℤ)
    (hr : Differential.Realizes wire C.start C.source) (hin : ∀ i < C.start, wire i = X i)
    (env : ℕ → ℂ) (hg : ∀ g ∈ gates C, g.Holds env) :
    env (sourceOutput C) = (wire C.sourceOutput).eval₂ (Int.castRingHom ℂ) env :=
  (GradientFamily.sound wire C.base (copyBase C) C.start C.ambient C.source h.source hr hin env env
    (zero_sound C env hg) (fun _ _ => rfl) C.count (copies_hold C env hg) 0 h.positive C.sourceOutput h.output).1

theorem gradient_sound (C : Inputs) (h : C.Valid) (wire : ℕ → MvPolynomial ℕ ℤ)
    (hr : Differential.Realizes wire C.start C.source) (hin : ∀ i < C.start, wire i = X i)
    (env : ℕ → ℂ) (hg : ∀ g ∈ gates C, g.Holds env) (i : ℕ) (hi : i < C.count) :
    env (gradientOutput C i) = (pderiv (C.ambient + i) (wire C.sourceOutput)).eval₂ (Int.castRingHom ℂ) env -
      ∑ r ∈ Finset.range (C.count + 1), env (C.normal r i) * env (C.multipliers + r) := by
  have H := AffineRow.difference_sound C.base (gradientStart C i) C.multipliers (C.count + 1) (derivative C i)
    (fun r => C.normal r i) env (zero_sound C env hg) (gradient_hold C env hg i hi)
  have hd := (GradientFamily.sound wire C.base (copyBase C) C.start C.ambient C.source h.source hr hin env env
    (zero_sound C env hg) (fun _ _ => rfl) C.count (copies_hold C env hg) i hi C.sourceOutput h.output).2
  exact H.trans (congrArg (fun v => v - ∑ r ∈ Finset.range (C.count + 1), env (C.normal r i) * env (C.multipliers + r)) hd)

theorem height_sound (C : Inputs) (env : ℕ → ℂ) (hg : ∀ g ∈ gates C, g.Holds env) (r : ℕ) (hr : r < C.count) :
    env (heightOutput C r) = if C.active r then
      (∑ i ∈ Finset.range C.count, env (C.normal (r + 1) i) * env (C.ambient + i)) - env (C.level r)
    else env (C.multipliers + (r + 1)) := by
  unfold heightOutput
  split_ifs
  · exact AffineRow.height_sound C.base (heightStart C r) C.ambient C.count (C.level r) (C.normal (r + 1))
      env (zero_sound C env hg) (height_hold C env hg r hr)
  · rfl

def port (C : Inputs) : Fin C.count ⊕ Fin (C.count + 1) → ℕ
  | .inl i => gradientOutput C i.val
  | .inr j => Fin.cases (sourceOutput C) (fun r => heightOutput C r.val) j

theorem port_eq_output (C : Inputs) (r : Fin C.count ⊕ Fin (C.count + 1)) :
    port C r = output C (finSumFinEquiv r).val := by
  cases r with
  | inl i =>
    change gradientOutput C i.val = output C i.val
    simp only [output, i.isLt, ite_true]
  | inr j =>
    refine Fin.cases ?_ (fun r => ?_) j
    · change sourceOutput C = output C (C.count + 0)
      simp only [Nat.add_zero, output, lt_self_iff_false, ite_false, ite_true]
    · change heightOutput C r.val = output C (C.count + (r.val + 1))
      have hlt : ¬ C.count + (r.val + 1) < C.count := by omega
      have hne : C.count + (r.val + 1) ≠ C.count := by omega
      simp only [output, hlt, hne, ite_false]
      congr 1
      omega

theorem outputs_zero_iff_ports (C : Inputs) (env : ℕ → ℂ) :
    (∀ j < C.count + (C.count + 1), env (output C j) = 0) ↔
      ∀ r : Fin C.count ⊕ Fin (C.count + 1), env (port C r) = 0 := by
  constructor
  · intro h r
    rw [port_eq_output]
    exact h _ (finSumFinEquiv r).isLt
  · intro h j hj
    let t : Fin (C.count + (C.count + 1)) := ⟨j, hj⟩
    have H := h (finSumFinEquiv.symm t)
    rw [port_eq_output, Equiv.apply_symm_apply] at H
    exact H

end LeanCanny.ETR.ComplexCircuit.AffineStage
