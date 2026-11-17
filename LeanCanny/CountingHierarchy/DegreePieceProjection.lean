/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.DegreePiecePolynomial
public import LeanCanny.Geometry.CoerciveComponentSampling

/-! # The actual degree-piece zero set projects continuously to its degree piece -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Set
open scoped Topology Classical

variable {m : ℕ}

noncomputable def firstCoefficientValues (P : MvPolynomial (Fin (m + 1)) ℤ) (N : ℕ)
    (j : Fin (N + 1)) (x : Fin m → ℝ) : ℝ :=
  MvPolynomial.eval₂ (Int.castRingHom ℝ) x (firstVariableCoefficient P j.val)

noncomputable def degreePiecePolynomialProjection (P : MvPolynomial (Fin (m + 1)) ℤ)
    (N : ℕ) (d : Fin (N + 1))
    (c : Geometry.CoerciveComponentSampling.Zeros ((degreePiecePolynomial P N d.val).map (Int.castRingHom ℝ))) :
    degreePiece (firstCoefficientValues P N) d :=
  ⟨fun i => c.val i.succ, by
    have hz : degreePieceLiftValue (firstCoefficientValues P N) d
        ((fun i => c.val i.succ), c.val 0) = 0 := by
      unfold firstCoefficientValues
      rw [← eval_degreePiecePolynomial]
      have hc : MvPolynomial.eval c.val
          ((degreePiecePolynomial P N d.val).map (Int.castRingHom ℝ)) = 0 := c.property
      rw [MvPolynomial.eval_map] at hc
      have he : Fin.cons (c.val 0) (fun i => c.val i.succ) = c.val := Fin.cons_self_tail _
      rw [he]
      exact hc
    obtain ⟨he, hh⟩ := (degreePieceLiftValue_eq_zero_iff _ _ _).mp hz
    exact ⟨left_ne_zero_of_mul_eq_one he, hh⟩⟩

theorem degreePiecePolynomialProjection_continuous (P : MvPolynomial (Fin (m + 1)) ℤ)
    (N : ℕ) (d : Fin (N + 1)) : Continuous (degreePiecePolynomialProjection P N d) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => (continuous_apply i.succ).comp continuous_subtype_val)

noncomputable def degreePiecePolynomialSection (P : MvPolynomial (Fin (m + 1)) ℤ)
    (N : ℕ) (d : Fin (N + 1)) (x : degreePiece (firstCoefficientValues P N) d) :
    Geometry.CoerciveComponentSampling.Zeros ((degreePiecePolynomial P N d.val).map (Int.castRingHom ℝ)) :=
  ⟨Fin.cons ((firstCoefficientValues P N d x.val)⁻¹) x.val, by
    change MvPolynomial.eval (Fin.cons ((firstCoefficientValues P N d x.val)⁻¹) x.val)
      ((degreePiecePolynomial P N d.val).map (Int.castRingHom ℝ)) = 0
    rw [MvPolynomial.eval_map, eval_degreePiecePolynomial]
    exact (degreePieceLiftValue_eq_zero_iff _ _ _).mpr
      ⟨mul_inv_cancel₀ x.property.1, x.property.2⟩⟩

end LeanCanny.CountingHierarchy
