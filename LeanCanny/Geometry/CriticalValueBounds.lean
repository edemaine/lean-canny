/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CriticalValueSystem
public import LeanCanny.Algebra.FermatCriticalFibers
public import LeanCanny.Geometry.AffineCoordinateFinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Bounded annihilators of critical values

The finite-fiber eliminant applied to the value-and-gradient system annihilates
all critical values over algebraically closed fields. Pure-power leading
polynomials satisfy the finiteness hypothesis without a simplicity assumption.
-/

@[expose] public section
namespace LeanCanny.Geometry.CriticalValueBounds
open MvPolynomial
open LeanCanny.Algebra
open scoped Classical

variable {n : ℕ} {R K : Type*} [CommRing R] [Field K]

noncomputable def polynomial (p : MvPolynomial (Fin n) R) (D W : ℕ) : Polynomial R :=
  AffineCoordinateEliminant.polynomial (CriticalValueSystem.equations p)
    (CriticalValueSystem.degrees n D) 0 W

theorem ne_zero [IsDomain R] (p : MvPolynomial (Fin n) R) (D W : ℕ) :
    polynomial p D W ≠ 0 := AffineCoordinateEliminant.ne_zero _ _ _ _

theorem degree_le (p : MvPolynomial (Fin n) R) (D W : ℕ) :
    (polynomial p D W).natDegree ≤ FixedWidthPolynomial.count (n + 2) W :=
  AffineCoordinateEliminant.degree_le _ _ _ _

omit [CommRing R] [Field K] in
theorem coefficient_size_le (p : MvPolynomial (Fin n) ℤ) (D W b : ℕ)
    (hp : ∀ j e, ((CriticalValueSystem.equations p j).coeff e).natAbs ≤ 2 ^ b) (k : ℕ) :
    ((polynomial p D W).coeff k).natAbs.size ≤
      (FixedWidthPolynomial.count (n + 2) W).size * FixedWidthPolynomial.count (n + 2) W +
        FixedWidthPolynomial.count (n + 2) W * (b + 3) + 1 :=
  AffineCoordinateEliminant.coefficient_size_le _ _ _ _ _ hp k

theorem eval_eq_zero [IsDomain R] [IsAlgClosed K] (φ : R →+* K)
    (p : MvPolynomial (Fin n) R) (D W : ℕ) (hp : p.totalDegree ≤ D) (hD : 1 < D)
    (hW : Macaulay.level (AffineCoordinateSystem.degrees (CriticalValueSystem.degrees n D)) < 2 ^ W)
    (hf : {x : Fin n → K | ∀ i, (pderiv i p).eval₂ φ x = 0}.Finite)
    (x : Fin n → K) (hx : ∀ i, (pderiv i p).eval₂ φ x = 0) :
    (polynomial p D W).eval₂ φ (p.eval₂ φ x) = 0 := by
  exact AffineCoordinateEliminant.eval_eq_zero_of_finite φ _ _
    (CriticalValueSystem.degree_le p D hp (by omega)) (CriticalValueSystem.degrees_pos D hD)
    0 W hW (CriticalValueSystem.finite_zero_set φ p hf)
    (Fin.cons (p.eval₂ φ x) x) (CriticalValueSystem.critical_root φ p x hx)

theorem eval_eq_zero_fermat [IsDomain R] [CharZero K] [IsAlgClosed K]
    (φ : R →+* K) (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N W : ℕ)
    (hlow : low.totalDegree < N) (ha : φ a ≠ 0) (hN : 1 < N)
    (hW : Macaulay.level (AffineCoordinateSystem.degrees
      (CriticalValueSystem.degrees (n + 1) N)) < 2 ^ W)
    (x : Fin (n + 1) → K)
    (hx : ∀ i, (pderiv i (FermatCriticalHomogenization.polynomial low a N)).eval₂ φ x = 0) :
    (polynomial (FermatCriticalHomogenization.polynomial low a N) N W).eval₂ φ
      ((FermatCriticalHomogenization.polynomial low a N).eval₂ φ x) = 0 := by
  apply eval_eq_zero φ _ N W
    (FermatCriticalHomogenization.polynomial_degree low a N hlow) hN hW _ x hx
  have hf := FermatCriticalHomogenization.finite_critical_points (low.map φ) (φ a) N
    ((PolynomialMapDegree.degree_le φ low).trans_lt hlow) ha hN
  simpa only [← FermatCriticalHomogenization.map_polynomial, pderiv_map,
    ← MvPolynomial.eval₂_eq_eval_map] using hf

/-- Embedding in an algebraic closure transfers the same annihilator to
arbitrary characteristic-zero fields. -/
theorem eval_eq_zero_fermat_extension [IsDomain R] [CharZero K]
    (φ : R →+* K) (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N W : ℕ)
    (hlow : low.totalDegree < N) (ha : φ a ≠ 0) (hN : 1 < N)
    (hW : Macaulay.level (AffineCoordinateSystem.degrees
      (CriticalValueSystem.degrees (n + 1) N)) < 2 ^ W)
    (x : Fin (n + 1) → K)
    (hx : ∀ i, (pderiv i (FermatCriticalHomogenization.polynomial low a N)).eval₂ φ x = 0) :
    (polynomial (FermatCriticalHomogenization.polynomial low a N) N W).eval₂ φ
      ((FermatCriticalHomogenization.polynomial low a N).eval₂ φ x) = 0 := by
  let ψ := (algebraMap K (AlgebraicClosure K)).comp φ
  let y : Fin (n + 1) → AlgebraicClosure K := (algebraMap K (AlgebraicClosure K)) ∘ x
  have hya : ψ a ≠ 0 := by
    intro hz
    apply ha
    exact (algebraMap K (AlgebraicClosure K)).injective (hz.trans (map_zero _).symm)
  have hy (i : Fin (n + 1)) :
      (pderiv i (FermatCriticalHomogenization.polynomial low a N)).eval₂ ψ y = 0 := by
    rw [← MvPolynomial.eval₂_comp_left, hx i, map_zero]
  have he := eval_eq_zero_fermat ψ low a N W hlow hya hN hW y hy
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [map_zero]
  rw [Polynomial.hom_eval₂, MvPolynomial.eval₂_comp_left]
  exact he

end LeanCanny.Geometry.CriticalValueBounds
