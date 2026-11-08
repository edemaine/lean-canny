/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.EndpointValidation

/-! # Native connectivity base cases in dimension zero

There is exactly one empty tuple. Whole-space connectivity therefore needs
only the well-formedness check, even for an empty realization. Point queries
add singleton endpoint validation and membership of that tuple. These are
uniform native polynomial-space algorithms, with all formula writers charged.
-/

@[expose] public section

namespace LeanCanny.Connectivity.ZeroDimension
open ETR Computation Turing.MultiTapeTM
open scoped Classical

theorem connected_iff (p : Formula) :
    (Description.mk 0 p).Connected ↔ p.arity ≤ 0 := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, (show (Description.mk 0 p).realization.Subsingleton from
      fun _ _ _ _ => Subsingleton.elim _ _).isPreconnected⟩

theorem denotes_iff (p : Formula) (x : Fin 0 → ℝ) :
    Denotes 0 p x ↔ p.arity ≤ 0 ∧ p.Satisfiable := by
  constructor
  · intro h
    exact ⟨h.1, ⟨Formula.extend x, (h.2 x).mpr rfl⟩⟩
  · rintro ⟨hp, hs⟩
    obtain ⟨y, hy⟩ := (EndpointValidation.exists_denotes_iff hp).mpr ⟨hs, by omega⟩
    simpa only [Subsingleton.elim y x] using hy

/-- Endpoint validity and space nonemptiness are sufficient because any two
empty tuples coincide. Ill-formed input formulas remain rejected. -/
theorem reachable_iff (p s t : Formula) :
    (PointQuery.mk ⟨0, p⟩ s t).Reachable ↔
      p.arity ≤ 0 ∧ (∃ x : Fin 0 → ℝ, Denotes 0 s x) ∧
        (∃ y : Fin 0 → ℝ, Denotes 0 t y) ∧ p.Satisfiable := by
  constructor
  · rintro ⟨hw, x, y, hx, hy, hj⟩
    exact ⟨hw, ⟨x, hx⟩, ⟨y, hy⟩, ⟨Formula.extend x, hj.source_mem⟩⟩
  · rintro ⟨hw, ⟨x, hx⟩, ⟨y, hy⟩, hs⟩
    have he : y = x := Subsingleton.elim _ _
    subst y
    have hm : x ∈ (Description.mk 0 p).realization := by
      obtain ⟨env, henv⟩ := hs
      apply (p.holds_congr env (Formula.extend x) ?_).mp henv
      intro i hi
      exact False.elim (by omega)
    exact ⟨hw, x, x, hx, hy, JoinedIn.refl hm⟩

theorem connected_computable {α : Type} {enc : α ↪ List Bool} {p : α → Formula}
    (hp : ComputableTidilyInPolyTime (fun a => (p a).encode) enc encBits) :
    ComputableTidilyInPolyTime (fun a => decide (Description.mk 0 (p a)).Connected) enc encBool := by
  have harity := ComputableTidilyInPolyTime.comp FormulaArity.value_unary hp
  have h := ComputableTidilyInPolyTime.unary_le' harity
    (ComputableTidilyInPolyTime.const (encIn := enc) (encMid := encUnary) 0)
  apply h.of_enc_eq
  intro a
  apply congrArg encBool
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq, FormulaArity.value_encode, connected_iff]

theorem point_computable {α : Type} [Inhabited α] {enc : α ↪ List Bool}
    {p s t : α → Formula}
    (hp : ComputableTidilyInPolyTime (fun a => (p a).encode) enc encBits)
    (hs : ComputableTidilyInPolyTime (fun a => (s a).encode) enc encBits)
    (ht : ComputableTidilyInPolyTime (fun a => (t a).encode) enc encBits) :
    ComputableInPolySpace
      (fun a => decide (PointQuery.mk ⟨0, p a⟩ (s a) (t a)).Reachable) enc encBool := by
  have hn : ComputableTidilyInPolyTime (fun _ : α => 0) enc encUnary := .const 0
  have hsource := EndpointValidation.exists_denotes_computable hs hn
  have htarget := EndpointValidation.exists_denotes_computable ht hn
  have hsat := satisfiable_computable hp
  have harity := ComputableTidilyInPolyTime.comp FormulaArity.value_unary hp
  have hwell := ComputableInPolySpace.of_tidyPolyTime
    (ComputableTidilyInPolyTime.unary_le' harity hn)
  have hf : ComputableInPolySpace (fun _ : α => false) enc encBool := .of_tidyPolyTime (.const false)
  apply (hwell.ite (hsource.ite (htarget.ite hsat hf) hf) hf).congr
  intro a
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq, FormulaArity.value_encode, reachable_iff]
  by_cases hp : (p a).arity ≤ 0 <;>
    by_cases hs : ∃ x : Fin 0 → ℝ, Denotes 0 (s a) x <;>
      by_cases ht : ∃ y : Fin 0 → ℝ, Denotes 0 (t a) y <;>
        simp [hp, hs, ht]

end LeanCanny.Connectivity.ZeroDimension
