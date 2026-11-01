/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueDoubleSystem
public import LeanCanny.Algebra.HomogeneousCoefficientRequest

/-! # Exact entry cases of the double-nilpotent reciprocal system

The value row has only a constant chart term and a linear value term.
Coordinate rows have only a constant value term. The triangular second
nilpotent digit selects these cases without wrapping higher powers.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralReciprocalEntry
open Polynomial MvPolynomial FixedWidthPolynomial IntegralCoordinateBasis
open scoped Classical

theorem zero_coefficient {A : Type*} [CommRing A] {n : ℕ}
    (rows : Fin n → MvPolynomial (Fin (n + 1)) A) (p : MvPolynomial (Fin (n + 1)) A)
    (D : ℕ) (e : Fin (n + 1) →₀ ℕ) (k : ℕ) :
    (((RelativeValueSystemMap.reciprocal rows p D 0).coeff e).coeff k) =
      (if k = 1 then p.coeff e else 0) -
        (if k = 0 ∧ Finsupp.single (0 : Fin (n + 1)) D = e then 1 else 0) := by
  rw [RelativeValueSystemMap.reciprocal, Fin.cases_zero, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, MvPolynomial.coeff_X_pow, Polynomial.coeff_sub,
    mul_comm, ← pow_one (Polynomial.X : Polynomial A), Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.coeff_monomial]
  congr 1 <;> split_ifs <;> simp_all [Polynomial.coeff_one]

theorem succ_coefficient {A : Type*} [CommRing A] {n : ℕ}
    (rows : Fin n → MvPolynomial (Fin (n + 1)) A) (p : MvPolynomial (Fin (n + 1)) A)
    (D : ℕ) (j : Fin n) (e : Fin (n + 1) →₀ ℕ) (k : ℕ) :
    (((RelativeValueSystemMap.reciprocal rows p D j.succ).coeff e).coeff k) =
      if k = 0 then (rows j).coeff e else 0 := by
  rw [RelativeValueSystemMap.reciprocal, Fin.cases_succ, MvPolynomial.coeff_map, Polynomial.coeff_C]

theorem zero_entry {A : Type*} [CommRing A] {n M : ℕ} (b : Module.Basis (Fin M) ℤ A)
    (rows : Fin n → MvPolynomial (Fin (n + 1)) A) (p : MvPolynomial (Fin (n + 1)) A)
    (D : ℕ) (e : Fin (n + 1) →₀ ℕ) (k : ℕ) (r t : Fin M) :
    Algebra.leftMulMatrix b (((RelativeValueSystemMap.reciprocal rows p D 0).coeff e).coeff k) r t =
      (if k = 1 then Algebra.leftMulMatrix b (p.coeff e) r t else 0) -
        (if k = 0 ∧ Finsupp.single (0 : Fin (n + 1)) D = e ∧ r = t then 1 else 0) := by
  rw [zero_coefficient, map_sub, Matrix.sub_apply]
  split_ifs <;> simp_all

theorem succ_entry {A : Type*} [CommRing A] {n M : ℕ} (b : Module.Basis (Fin M) ℤ A)
    (rows : Fin n → MvPolynomial (Fin (n + 1)) A) (p : MvPolynomial (Fin (n + 1)) A)
    (D : ℕ) (j : Fin n) (e : Fin (n + 1) →₀ ℕ) (k : ℕ) (r t : Fin M) :
    Algebra.leftMulMatrix b (((RelativeValueSystemMap.reciprocal rows p D j.succ).coeff e).coeff k) r t =
      if k = 0 then Algebra.leftMulMatrix b ((rows j).coeff e) r t else 0 := by
  rw [succ_coefficient]
  split_ifs <;> simp only [map_zero, Matrix.zero_apply]

open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource IntegralMixedValueDoubleSystem
attribute [local irreducible] IntegralMixedValueDoubleNilpotent.basis

theorem mapped_entry (F : Family) (q : List Bool)
    (i : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1))
    (e : Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1) →₀ ℕ)
    (r t : Fin (count (F.birth q + 1) (F.width q))) (a c : Fin (2 ^ F.width q)) :
    Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
      ((mappedSystem F q i j).coeff e)
      (pairIndex (F.birth q + 1) (F.width q) (r, a))
      (pairIndex (F.birth q + 1) (F.width q) (t, c)) =
      if c.val ≤ a.val then
        Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
          (((system F q i j).coeff e).coeff (a.val - c.val)) r t else 0 := by
  rw [mappedSystem, MvPolynomial.coeff_map, IntegralMixedValueDoubleNilpotent.basis_matrix]

theorem mapped_zero (F : Family) (q : List Bool)
    (i : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (e : Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1) →₀ ℕ)
    (r t : Fin (count (F.birth q + 1) (F.width q))) (a c : Fin (2 ^ F.width q)) :
    Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
      ((mappedSystem F q i 0).coeff e)
      (pairIndex (F.birth q + 1) (F.width q) (r, a))
      (pairIndex (F.birth q + 1) (F.width q) (t, c)) =
      if c.val ≤ a.val then
        (if a.val - c.val = 1 then
          Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
            ((RelativeValueSystemMap.homogeneousTest (IntegralMixedVirtualOriginalRows.row F q i)
              (F.spatial q).degree).coeff e) r t else 0) -
        (if a.val - c.val = 0 ∧ Finsupp.single (0 : Fin (_ + 1)) (F.spatial q).degree = e ∧ r = t
          then 1 else 0)
      else 0 := by
  rw [mapped_entry]
  congr 1
  exact zero_entry _ _ _ _ _ _ _ _

theorem mapped_succ (F : Family) (q : List Bool)
    (i j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (e : Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1) →₀ ℕ)
    (r t : Fin (count (F.birth q + 1) (F.width q))) (a c : Fin (2 ^ F.width q)) :
    Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
      ((mappedSystem F q i j.succ).coeff e)
      (pairIndex (F.birth q + 1) (F.width q) (r, a))
      (pairIndex (F.birth q + 1) (F.width q) (t, c)) =
      if c.val ≤ a.val ∧ a.val - c.val = 0 then
        Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
          ((AffineRingCoordinates.homogeneousRows (coordinates F q)
            (fun _ => IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q)) j).coeff e) r t else 0 := by
  rw [mapped_entry]
  by_cases HC : c.val ≤ a.val
  · simp only [HC, true_and, ite_true]
    exact succ_entry _ _ _ _ _ _ _ _ _
  · simp only [HC, false_and, ite_false]

end LeanCanny.Algebra.IntegralReciprocalEntry
