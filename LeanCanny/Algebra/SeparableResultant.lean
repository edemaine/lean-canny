/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.FieldTheory.Separable

/-! # Testing integer polynomials for separability over a characteristic-zero field

The derivative resultant detects separability of every nonzero polynomial,
including constants. The zero polynomial requires a separate nonzero test.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial

theorem integer_separable_iff_resultant_ne_zero {K : Type*} [Field K] [CharZero K]
    (p : ℤ[X]) (hp : p ≠ 0) :
    (p.map (Int.castRingHom K)).Separable ↔ p.resultant p.derivative ≠ 0 := by
  have hi : Function.Injective (Int.castRingHom K) := Int.cast_injective
  have hne : p.map (Int.castRingHom K) ≠ 0 := (Polynomial.map_ne_zero_iff hi).mpr hp
  have hm : (p.map (Int.castRingHom K)).resultant
      (p.map (Int.castRingHom K)).derivative =
      (Int.castRingHom K) (p.resultant p.derivative) := by
    rw [derivative_map, natDegree_map_eq_of_injective hi, natDegree_map_eq_of_injective hi]
    exact resultant_map_map p p.derivative p.natDegree p.derivative.natDegree _
  have hz : (Int.castRingHom K) (p.resultant p.derivative) = 0 ↔ p.resultant p.derivative = 0 :=
    (map_eq_zero_iff _ hi)
  have hc : (p.map (Int.castRingHom K)).resultant
      (p.map (Int.castRingHom K)).derivative = 0 ↔
      ¬ (p.map (Int.castRingHom K)).Separable := by
    rw [resultant_eq_zero_iff, separable_def]
    exact ⟨fun h => h.2, fun h => ⟨Or.inl hne, h⟩⟩
  rw [hm, hz] at hc
  tauto

end LeanCanny.Algebra
