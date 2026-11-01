/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ClearedCoordinateCriticalBounds

/-! # Coefficient maps preserve the literal cleared spatial rows

No injectivity or degree-preservation assumption is required. In
particular the formal sweep parameter may be mapped into a nilpotent
algebra before constructing the frozen source, gradients and Euler rows.
-/

@[expose] public section
namespace LeanCanny.Algebra.ClearedCoordinateMap
open MvPolynomial
open scoped Classical BigOperators
variable {R A : Type*} [CommRing R] [CommRing A] {n dim : ℕ}

theorem clear (φ : R →+* A) (D : ℕ) (q : R) (v : Fin n → MvPolynomial (Fin dim) R)
    (p : MvPolynomial (Fin n) R) :
    (CommonDenominatorSpecialization.clear D q v p).map φ =
      CommonDenominatorSpecialization.clear D (φ q) (fun i => (v i).map φ) (p.map φ) := by
  induction p using MvPolynomial.induction_on' with
  | add p t hp ht => simp only [map_add, hp, ht]
  | monomial e a =>
    rw [CommonDenominatorSpecialization.monomial, MvPolynomial.map_monomial,
      CommonDenominatorSpecialization.monomial]
    simp only [CommonDenominatorSpecialization.factor, map_mul, map_C, map_pow, map_prod]

theorem coordinate (φ : R →+* A) (q : R) (H : ℕ → R) (offset dim i : ℕ) :
    (ClearedCoordinateBlock.coordinate q H offset dim i).map φ =
      ClearedCoordinateBlock.coordinate (φ q) (fun i => φ (H i)) offset dim i := by
  unfold ClearedCoordinateBlock.coordinate
  split_ifs <;> simp only [map_mul, map_C, map_X]

theorem specialize (φ : R →+* A) (D : ℕ) (q : R) (H : ℕ → R) (offset dim : ℕ)
    (p : MvPolynomial (Fin n) R) :
    (ClearedCoordinateBlock.specialize D q H offset dim p).map φ =
      ClearedCoordinateBlock.specialize D (φ q) (fun i => φ (H i)) offset dim (p.map φ) := by
  unfold ClearedCoordinateBlock.specialize
  rw [clear]
  simp only [coordinate]

theorem frozenPower (φ : R →+* A) (H : ℕ → R) (offset dim D : ℕ) :
    φ (CoordinateBlockSpecialization.frozenPower (n := n) H offset dim D) =
      CoordinateBlockSpecialization.frozenPower (n := n) (fun i => φ (H i)) offset dim D := by
  unfold CoordinateBlockSpecialization.frozenPower
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp only [map_zero, map_pow]

theorem block_lower (φ : R →+* A) (D : ℕ) (q : R) (H : ℕ → R) (offset dim : ℕ)
    (p : MvPolynomial (Fin n) R) (a : R) :
    (ClearedCoordinateBlock.lower D q H offset dim p a).map φ =
      ClearedCoordinateBlock.lower D (φ q) (fun i => φ (H i)) offset dim (p.map φ) (φ a) := by
  simp only [ClearedCoordinateBlock.lower, map_add, specialize, map_C, map_mul, frozenPower]

theorem euler_lower {k : ℕ} (φ : R →+* A) (p : MvPolynomial (Fin (k + 1)) R)
    (g : Fin (k + 1) → MvPolynomial (Fin (k + 1)) R) (D : ℕ) (r i : Fin (k + 1)) :
    (PurePowerEulerReduction.lower p g D r i).map φ =
      PurePowerEulerReduction.lower (p.map φ) (fun j => (g j).map φ) D r i := by
  unfold PurePowerEulerReduction.lower
  split_ifs
  · simp only [PurePowerEulerReduction.objectiveLower, map_sub, map_mul, map_natCast,
      map_sum, map_X]
  · rfl

theorem lower {k : ℕ} (φ : R →+* A) (D : ℕ) (q : R) (H : ℕ → R)
    (offset : ℕ) (hfit : offset + (k + 1) ≤ n + 1) (p : MvPolynomial (Fin (n + 1)) R)
    (a : R) (r i : Fin (k + 1)) :
    (ClearedCoordinateCritical.lower D q H offset hfit p a r i).map φ =
      ClearedCoordinateCritical.lower D (φ q) (fun j => φ (H j)) offset hfit (p.map φ) (φ a) r i := by
  unfold ClearedCoordinateCritical.lower
  rw [euler_lower, block_lower]
  congr 1
  funext j
  unfold ClearedCoordinateCritical.gradientLower
  rw [specialize, MvPolynomial.pderiv_map]

end LeanCanny.Algebra.ClearedCoordinateMap
