/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientCoordinateDyadicBounds

/-! # Matrix bounds from specialization maps existing only above a cutoff

An inductive prefix supplies its maps only on the certified parameter tail.
Scalar interpolation uses exactly those maps; no extension below the cutoff
or arbitrary homomorphism into an incompatible earlier quotient is needed.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoefficientCoordinateDyadicBounds
open Polynomial
open scoped Classical
variable {A : Type*} [CommRing A] [Algebra ℤ[X] A]
  {B : ℕ → Type*} [∀ r, CommRing (B r)] {m width : ℕ}

theorem degree_mass_of_tail
    (b : CoefficientCoordinateBasis ℤ[X] A m (2 ^ width))
    (c : ∀ r, IntegralCoordinateBasis (B r) m (2 ^ width)) (v : A) (C K H : ℕ)
    (h : ∀ r, C ≤ r → ∃ ψ : A →+* B r,
      CoefficientCoordinateBasis.Specializes (evalRingHom ((2 : ℤ) ^ r)) ψ b
        (CoefficientCoordinateBasis.ofIntegral (c r)) ∧
      ∀ i j, (Algebra.leftMulMatrix (c r).finBasis (ψ v) i j).natAbs ≤ 2 ^ (K * r + H))
    (i j : Fin m → Fin (2 ^ width)) :
    (Algebra.leftMulMatrix b.basis v i j).natDegree ≤ K ∧
      coefficientMass (Algebra.leftMulMatrix b.basis v i j) ≤
        2 ^ IntegerPolynomialDyadic.massBudget C K H := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  obtain ⟨ψ, hb, hn⟩ := h r hr
  have he := congrArg (fun M => M i j) (hb.matrix_map v)
  change (Algebra.leftMulMatrix b.basis v i j).eval ((2 : ℤ) ^ r) = _ at he
  rw [he]
  have hf := hn (IntegralCoordinateBasis.boxEquiv m width i) (IntegralCoordinateBasis.boxEquiv m width j)
  simpa only [IntegralCoordinateBasis.finBasis, CoefficientCoordinateBasis.ofIntegral,
    Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.repr_reindex_apply,
    Module.Basis.reindex_apply, Equiv.symm_apply_apply] using hf

end LeanCanny.Algebra.CoefficientCoordinateDyadicBounds
