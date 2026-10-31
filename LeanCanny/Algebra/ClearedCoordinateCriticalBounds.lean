/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ClearedCoordinateCritical
public import LeanCanny.Algebra.PurePowerReductionBounds

/-! # Explicit relative annihilators on integral frozen slices

Only free spatial arity and original local degree determine the matrix
dimension. A nonzero common denominator and source coefficient preserve the
annihilator's degree under every characteristic-zero specialization.
-/

@[expose] public section
namespace LeanCanny.Algebra.ClearedCoordinateCritical
open MvPolynomial
open scoped Classical
variable {n k : ℕ} {R : Type*} [CommRing R]

theorem grid_bound (r : Fin (k + 1)) (D : ℕ) :
    PurePowerReductionMatrix.gridBound (FermatCoordinateCriticalReduction.degrees r D) + 1 ≤
      PurePowerReductionBounds.bound (k + 1) D := by
  apply PurePowerReductionBounds.grid_bound
  intro i
  unfold FermatCoordinateCriticalReduction.degrees
  split_ifs
  · exact le_rfl
  · exact Nat.sub_le _ _

noncomputable def annihilator (D : ℕ) (q : R) (H : ℕ → R) (offset : ℕ)
    (hfit : offset + (k + 1) ≤ n + 1) (low : MvPolynomial (Fin (n + 1)) R)
    (a : R) (r j : Fin (k + 1)) : Polynomial R :=
  PurePowerRelativeAnnihilator.polynomial (B := PurePowerReductionBounds.width (k + 1) D)
    r (FermatCoordinateCriticalReduction.degrees r D) (lower D q H offset hfit low a r)
    ((a * q ^ D) * (D : R)) (PurePowerReductionBounds.bound (k + 1) D)
    (grid_bound r D) (PurePowerReductionBounds.bound_lt (k + 1) D) j

theorem annihilator_root [Nontrivial R] {K : Type*} [Field K] (φ : R →+* K)
    (D : ℕ) (q : R) (H : ℕ → R) (offset : ℕ) (hfit : offset + (k + 1) ≤ n + 1)
    (low : MvPolynomial (Fin (n + 1)) R) (a : R) (hD : 2 ≤ D) (hlow : low.totalDegree < D)
    (hq : φ q ≠ 0) (r : Fin (k + 1)) (x : Fin (k + 1) → K)
    (hp : (FermatCriticalHomogenization.polynomial low a D).eval₂ φ (ClearedCoordinateBlock.point φ q H offset x) = 0)
    (hg : ∀ i, i ≠ r → (pderiv (freeIndex offset hfit i) (FermatCriticalHomogenization.polynomial low a D)).eval₂
      φ (ClearedCoordinateBlock.point φ q H offset x) = 0) (j : Fin (k + 1)) :
    (annihilator D q H offset hfit low a r j).eval₂ φ (x j) = 0 :=
  coordinate_annihilator_root φ D q H offset hfit low a hD hlow hq r _ _ _ x hp hg j

theorem annihilator_specialized_degree {K : Type*} [Field K] [CharZero K] (φ : R →+* K)
    (D : ℕ) (q : R) (H : ℕ → R) (offset : ℕ) (hfit : offset + (k + 1) ≤ n + 1)
    (low : MvPolynomial (Fin (n + 1)) R) (a : R) (hD : 0 < D)
    (ha : φ a ≠ 0) (hq : φ q ≠ 0) (r j : Fin (k + 1)) :
    ((annihilator D q H offset hfit low a r j).map φ).natDegree = PurePowerReductionBounds.dimension (k + 1) D := by
  have HC : φ ((a * q ^ D) * (D : R)) ≠ 0 := by
    rw [map_mul, map_mul, map_pow, map_natCast]
    exact mul_ne_zero (mul_ne_zero ha (pow_ne_zero _ hq)) (Nat.cast_ne_zero.mpr (by omega))
  exact PurePowerRelativeAnnihilator.specialized_degree φ r _ _ _ HC _ _ _ j

theorem annihilator_specialized_ne_zero {K : Type*} [Field K] [CharZero K] (φ : R →+* K)
    (D : ℕ) (q : R) (H : ℕ → R) (offset : ℕ) (hfit : offset + (k + 1) ≤ n + 1)
    (low : MvPolynomial (Fin (n + 1)) R) (a : R) (hD : 0 < D)
    (ha : φ a ≠ 0) (hq : φ q ≠ 0) (r j : Fin (k + 1)) :
    (annihilator D q H offset hfit low a r j).map φ ≠ 0 := by
  intro HZ
  have HD := annihilator_specialized_degree φ D q H offset hfit low a hD ha hq r j
  rw [HZ, Polynomial.natDegree_zero] at HD
  have HP : 0 < PurePowerReductionBounds.dimension (k + 1) D :=
    pow_pos (pow_pos (by decide : 0 < (2 : ℕ)) _) _
  omega

end LeanCanny.Algebra.ClearedCoordinateCritical
