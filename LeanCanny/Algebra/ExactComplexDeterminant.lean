/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntertwiningDeterminant
public import LeanCanny.Algebra.AlternatingProducts

/-! # Alternating determinant products of a finite exact complex

A chain endomorphism preserves every boundary space. Exactness identifies
the kernel restriction in one degree with the next boundary restriction,
so adjacent determinant factors telescope. Degree-zero surjectivity and
a zero terminal space leave equal even and odd determinant products.
The endomorphism need not be invertible.
-/

@[expose] public section

namespace LeanCanny.Algebra.ExactComplexDeterminant
open scoped Classical
variable {K : Type*} [Field K] (V : ℕ → Type*) [∀ k, AddCommGroup (V k)] [∀ k, Module K (V k)]

noncomputable def boundaryOperator (d : (k : ℕ) → V (k + 1) →ₗ[K] V k)
    (f : (k : ℕ) → V k →ₗ[K] V k) (h : ∀ k, (d k).comp (f (k + 1)) = (f k).comp (d k)) (k : ℕ) :
    Module.End K (LinearMap.range (d k)) :=
  (f k).restrict (IntertwiningDeterminant.range_preserved (d k) (f (k + 1)) (f k) (h k))

theorem determinant_succ [∀ k, FiniteDimensional K (V k)] (d : (k : ℕ) → V (k + 1) →ₗ[K] V k)
    (f : (k : ℕ) → V k →ₗ[K] V k) (h : ∀ k, (d k).comp (f (k + 1)) = (f k).comp (d k))
    (hex : ∀ k, LinearMap.ker (d k) = LinearMap.range (d (k + 1))) (k : ℕ) :
    (f (k + 1)).det = (boundaryOperator V d f h (k + 1)).det * (boundaryOperator V d f h k).det := by
  rw [IntertwiningDeterminant.determinant (d k) (f (k + 1)) (f k) (h k),
    IntertwiningDeterminant.restriction_det_congr _ _ (hex k) (f (k + 1)) _
      (IntertwiningDeterminant.range_preserved (d (k + 1)) (f (k + 2)) (f (k + 1)) (h (k + 1)))]
  rfl

theorem determinant_zero (d : (k : ℕ) → V (k + 1) →ₗ[K] V k)
    (f : (k : ℕ) → V k →ₗ[K] V k) (h : ∀ k, (d k).comp (f (k + 1)) = (f k).comp (d k))
    (hs : Function.Surjective (d 0)) : (f 0).det = (boundaryOperator V d f h 0).det :=
  (IntertwiningDeterminant.restriction_det_eq_of_top (LinearMap.range (d 0))
    (LinearMap.range_eq_top.mpr hs) (f 0) _).symm

theorem boundary_det_eq_one (d : (k : ℕ) → V (k + 1) →ₗ[K] V k)
    (f : (k : ℕ) → V k →ₗ[K] V k) (h : ∀ k, (d k).comp (f (k + 1)) = (f k).comp (d k))
    (N : ℕ) [Subsingleton (V (N + 1))] : (boundaryOperator V d f h N).det = 1 := by
  have : Subsingleton (LinearMap.range (d N)) := ⟨by
    intro x y
    apply Subtype.ext
    obtain ⟨u, hu⟩ := x.property
    obtain ⟨v, hv⟩ := y.property
    rw [← hu, ← hv, Subsingleton.elim u v]⟩
  exact LinearMap.det_eq_one_of_subsingleton _

theorem even_det_eq_odd_det [∀ k, FiniteDimensional K (V k)] (d : (k : ℕ) → V (k + 1) →ₗ[K] V k)
    (f : (k : ℕ) → V k →ₗ[K] V k) (h : ∀ k, (d k).comp (f (k + 1)) = (f k).comp (d k))
    (hex : ∀ k, LinearMap.ker (d k) = LinearMap.range (d (k + 1)))
    (hs : Function.Surjective (d 0)) (N : ℕ) [Subsingleton (V (N + 1))] :
    AlternatingProducts.evenProduct (fun k => (f k).det) (N + 1) =
      AlternatingProducts.oddProduct (fun k => (f k).det) (N + 1) :=
  AlternatingProducts.even_eq_odd_of_adjacent (fun k => (f k).det)
    (fun k => (boundaryOperator V d f h k).det) (determinant_zero V d f h hs)
    (determinant_succ V d f h hex) N (boundary_det_eq_one V d f h N)

end LeanCanny.Algebra.ExactComplexDeterminant
