/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.GeneralCriticalValueBounds
public import LeanCanny.Geometry.RegularSublevelComponents
public import LeanCanny.Geometry.ProjectionCritical

/-! # An explicit dyadic sublevel preserving zero-set components

The integer source's dimension, degree and coefficient-mass allowance give
one dyadic tolerance. For a nonnegative polynomial with compact sublevels,
that sublevel has exactly the zero-set component relation on the original
zeros. The critical locus and zero fiber may be singular or positive dimensional.
-/

@[expose] public section
namespace LeanCanny.Geometry.EffectiveSublevelComponents
open MvPolynomial Set LeanCanny.Algebra

variable {n : ℕ}

theorem zero_component_iff (p : MvPolynomial (Fin n) ℤ) (D b : ℕ) (hD : p.totalDegree ≤ D)
    (hpos : 0 < D) (hp : MvMass.mass p ≤ 2 ^ b)
    (hnonneg : ∀ x : Fin n → ℝ, 0 ≤ p.eval₂ (Int.castRingHom ℝ) x)
    (hsublevel : ∀ e : ℝ, IsCompact {x : Fin n → ℝ | p.eval₂ (Int.castRingHom ℝ) x ≤ e})
    (x y : Fin n → ℝ) (hx : p.eval₂ (Int.castRingHom ℝ) x = 0)
    (hy : p.eval₂ (Int.castRingHom ℝ) y = 0) :
    y ∈ connectedComponentIn {z : Fin n → ℝ | p.eval₂ (Int.castRingHom ℝ) z = 0} x ↔
      y ∈ connectedComponentIn {z : Fin n → ℝ |
        p.eval₂ (Int.castRingHom ℝ) z ≤ GeneralCriticalValueBounds.level n D b} x := by
  exact RegularSublevelComponents.zero_component_iff_sublevel _
    ((ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) p).of_le le_top) hnonneg hsublevel
    (GeneralCriticalValueBounds.level n D b) (GeneralCriticalValueBounds.level_pos n D b)
    (GeneralCriticalValueBounds.regular_interval p D b hD hpos hp) x y hx hy

end LeanCanny.Geometry.EffectiveSublevelComponents
