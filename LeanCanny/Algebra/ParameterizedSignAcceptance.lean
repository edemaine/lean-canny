/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ParameterizedSignPatterns

/-! # Stability for arbitrary acceptance predicates on root-query signs -/

@[expose] public section
namespace LeanCanny.Algebra.ParameterTarski
open Polynomial

variable {J : Type*} [Fintype J]

def Accepted (p : (ℤ[X])[X]) (Q : J → (ℤ[X])[X]) (accept : (J → SignType) → Prop) (x : ℝ) : Prop :=
  ∃ a : ℝ, (p.map (evalHom x)).eval a = 0 ∧
    accept (fun i => SignType.sign (((Q i).map (evalHom x)).eval a))

theorem accepted_stable (p : (ℤ[X])[X]) (hp : p ≠ 0) (Q : J → (ℤ[X])[X])
    (accept : (J → SignType) → Prop) (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxs : x ≤ InfinitesimalSign.dyadic (patternBudget p Q + 1))
    (hys : y ≤ InfinitesimalSign.dyadic (patternBudget p Q + 1)) :
    Accepted p Q accept x ↔ Accepted p Q accept y := by
  have forward (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
      (hus : u ≤ InfinitesimalSign.dyadic (patternBudget p Q + 1))
      (hvs : v ≤ InfinitesimalSign.dyadic (patternBudget p Q + 1)) :
      Accepted p Q accept u → Accepted p Q accept v := by
    rintro ⟨a, ha, haccept⟩
    let signs : J → SignType := fun i => SignType.sign (((Q i).map (evalHom u)).eval a)
    obtain ⟨b, hb, hsign⟩ := (realizable_stable p hp Q signs u v hu hv hus hvs).mp ⟨a, ha, fun _ => rfl⟩
    refine ⟨b, hb, ?_⟩
    have he : (fun i => SignType.sign (((Q i).map (evalHom v)).eval b)) = signs := funext hsign
    rwa [he]
  exact ⟨forward x y hx hy hxs hys, forward y x hy hx hys hxs⟩

theorem eventually_accepted_iff_reference (p : (ℤ[X])[X]) (hp : p ≠ 0) (Q : J → (ℤ[X])[X])
    (accept : (J → SignType) → Prop) :
    (∃ delta : ℝ, 0 < delta ∧ ∀ x : ℝ, 0 < x → x < delta → Accepted p Q accept x) ↔
      Accepted p Q accept (InfinitesimalSign.dyadic (patternBudget p Q + 1)) := by
  let r := InfinitesimalSign.dyadic (patternBudget p Q + 1)
  have hr : 0 < r := InfinitesimalSign.dyadic_pos _
  constructor
  · rintro ⟨delta, hd, h⟩
    let x := min (delta / 2) r
    have hx : 0 < x := lt_min (half_pos hd) hr
    exact (accepted_stable p hp Q accept x r hx hr (min_le_right _ _) le_rfl).mp
      (h x hx ((min_le_left _ _).trans_lt (half_lt_self hd)))
  · intro h
    refine ⟨r, hr, fun x hx hxr => ?_⟩
    exact (accepted_stable p hp Q accept x r hx hr hxr.le le_rfl).mpr h

end LeanCanny.Algebra.ParameterTarski
