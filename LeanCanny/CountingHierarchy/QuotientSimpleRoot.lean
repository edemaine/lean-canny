/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.QuotientEvaluation
public import LeanCanny.CountingHierarchy.SimpleEigenvalueCharacter
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! # A simple characteristic root comes from a common zero -/

public section

namespace LeanCanny.CountingHierarchy.PurePowerResidue

open MvPolynomial Module
open scoped Classical

variable {K : Type*} [Field K] {n ell : ℕ}

/-- Over any field, a simple root of the multiplication characteristic
 polynomial is attained at a common zero of the defining relations.
 In particular, a simple real root has a real point above it. -/
theorem exists_common_zero_of_simple_charpoly_root (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) K) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) K) (η : K)
    (hroot : (multiplicationMatrix hell r hr v).charpoly.IsRoot η)
    (hsimple : (multiplicationMatrix hell r hr v).charpoly.rootMultiplicity η = 1) :
    ∃ x : Fin n → K, (∀ i, MvPolynomial.aeval x (r i) = x i ^ ell) ∧
      MvPolynomial.aeval x v = η := by
  let A := QuotientAlgebra ell r
  let b := normalBasis hell r hr
  let : Module.Finite K A := Module.Finite.of_basis b
  let π := projection ell r
  have hchar : (multiplicationMatrix hell r hr v).charpoly =
      (Algebra.lmul K A (π v)).charpoly := by
    change (Algebra.leftMulMatrix b (π v)).charpoly = _
    rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
  obtain ⟨χ, hχ⟩ := exists_character_of_simple_multiplication_eigenvalue (π v) η
    (by rwa [← hchar]) (by rwa [← hchar])
  let x : Fin n → K := fun i => χ (π (X i))
  have hcomp : χ.comp π = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, x]
  have heval (q : MvPolynomial (Fin n) K) : χ (π q) = MvPolynomial.aeval x q :=
    congrArg (fun f : MvPolynomial (Fin n) K →ₐ[K] K => f q) hcomp
  refine ⟨x, ?_, ?_⟩
  · intro i
    rw [← heval, ← projection_X_pow ell r i, map_pow]
  · rw [← heval]
    exact hχ

end LeanCanny.CountingHierarchy.PurePowerResidue
