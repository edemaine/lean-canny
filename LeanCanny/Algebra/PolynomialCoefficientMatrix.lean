/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.Matrix.Composition
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Polynomial coefficients as finite scalar matrix entries

A lower triangular coefficient matrix represents multiplication modulo
`X^(d+1)`. Applying this representation entrywise and flattening the blocks
turns any coefficient through degree `d` of a polynomial matrix power into a
scalar matrix-power entry. Only one input coefficient is needed per entry of
the enlarged matrix; no intermediate polynomial is required by this identity.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialCoefficientMatrix
open Polynomial

variable {R : Type*} [Semiring R]

def scalar (d : ℕ) (p : R[X]) : Matrix (Fin (d + 1)) (Fin (d + 1)) R := fun i j =>
  if j.val ≤ i.val then p.coeff (i.val - j.val) else 0

theorem scalar_zero (d : ℕ) : scalar d (0 : R[X]) = 0 := by
  ext i j
  simp [scalar]

theorem scalar_one (d : ℕ) : scalar d (1 : R[X]) = 1 := by
  ext i j
  by_cases he : i = j
  · subst j
    simp [scalar]
  · have hv : i.val ≠ j.val := by simpa only [Fin.ext_iff] using he
    by_cases hj : j.val ≤ i.val
    · have hd : i.val - j.val ≠ 0 := by omega
      simp [scalar, hj, Polynomial.coeff_one, hd, he]
    · simp [scalar, hj, he]

theorem scalar_add (d : ℕ) (p q : R[X]) : scalar d (p + q) = scalar d p + scalar d q := by
  ext i j
  by_cases h : j.val ≤ i.val <;> simp [scalar, h]

theorem scalar_mul (d : ℕ) (p q : R[X]) : scalar d (p * q) = scalar d p * scalar d q := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : j.val ≤ i.val
  · rw [scalar, ite_eq_left hij, Polynomial.coeff_mul]
    have hsum : (∑ k : Fin (d + 1), scalar d p i k * scalar d q k j) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin (d + 1) => j.val ≤ k.val ∧ k.val ≤ i.val),
          p.coeff (i.val - k.val) * q.coeff (k.val - j.val) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hjk : j.val ≤ k.val <;> by_cases hki : k.val ≤ i.val <;>
        simp [scalar, hjk, hki]
    rw [hsum]
    symm
    refine Finset.sum_bij (fun k _ => (i.val - k.val, k.val - j.val)) ?_ ?_ ?_ ?_
    · intro k hk
      have hk := (Finset.mem_filter.mp hk).2
      simp only [Finset.mem_antidiagonal]
      omega
    · intro k hk l hl he
      have hk := (Finset.mem_filter.mp hk).2
      have hl := (Finset.mem_filter.mp hl).2
      have he := congrArg Prod.snd he
      apply Fin.ext
      change k.val - j.val = l.val - j.val at he
      omega
    · intro ab hab
      have hab := Finset.mem_antidiagonal.mp hab
      have hv : j.val + ab.2 < d + 1 := by have hi := i.isLt; omega
      refine ⟨⟨j.val + ab.2, hv⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · apply Prod.ext <;> dsimp only <;> omega
    · intro k _
      rfl
  · rw [scalar, ite_eq_right hij]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k.val ≤ i.val
    · have hjk : ¬ j.val ≤ k.val := by omega
      simp [scalar, hjk]
    · simp [scalar, hki]

def scalarHom (d : ℕ) : R[X] →+* Matrix (Fin (d + 1)) (Fin (d + 1)) R where
  toFun := scalar d
  map_zero' := scalar_zero d
  map_one' := scalar_one d
  map_add' := scalar_add d
  map_mul' := scalar_mul d

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def liftHom (d : ℕ) : Matrix n n R[X] →+* Matrix (n × Fin (d + 1)) (n × Fin (d + 1)) R :=
  (Matrix.compRingEquiv n (Fin (d + 1)) R).toRingHom.comp (scalarHom d).mapMatrix

theorem liftHom_apply (d : ℕ) (A : Matrix n n R[X]) (i j : n × Fin (d + 1)) :
    liftHom d A i j = if j.2.val ≤ i.2.val then (A i.1 j.1).coeff (i.2.val - j.2.val) else 0 := rfl

theorem liftHom_pow (d k : ℕ) (A : Matrix n n R[X]) : liftHom d (A ^ k) = liftHom d A ^ k :=
  map_pow (liftHom d) A k

theorem pow_apply (d k : ℕ) (A : Matrix n n R[X]) (i j : n) (a b : Fin (d + 1)) :
    (liftHom d A ^ k) (i, a) (j, b) =
      if b.val ≤ a.val then ((A ^ k) i j).coeff (a.val - b.val) else 0 := by
  rw [← liftHom_pow, liftHom_apply]

theorem pow_last_zero (d k : ℕ) (A : Matrix n n R[X]) (i j : n) :
    (liftHom d A ^ k) (i, Fin.last d) (j, 0) = ((A ^ k) i j).coeff d := by
  simp only [pow_apply, Fin.val_zero, Fin.val_last, Nat.zero_le, ↓reduceIte, Nat.sub_zero]

noncomputable def finHom (n d : ℕ) :
    Matrix (Fin n) (Fin n) R[X] →+* Matrix (Fin (n * (d + 1))) (Fin (n * (d + 1))) R :=
  (Matrix.reindexRingEquiv R finProdFinEquiv).toRingHom.comp (liftHom d)

theorem finHom_apply (n d : ℕ) (A : Matrix (Fin n) (Fin n) R[X])
    (i j : Fin (n * (d + 1))) :
    finHom n d A i j =
      if j.modNat.val ≤ i.modNat.val then
        (A i.divNat j.divNat).coeff (i.modNat.val - j.modNat.val) else 0 := rfl

theorem finHom_pow_last_zero (n d k : ℕ) (A : Matrix (Fin n) (Fin n) R[X]) (i j : Fin n) :
    (finHom n d A ^ k) (finProdFinEquiv (i, Fin.last d)) (finProdFinEquiv (j, 0)) =
      ((A ^ k) i j).coeff d := by
  change (Matrix.reindexRingEquiv R finProdFinEquiv (liftHom d A) ^ k)
    (finProdFinEquiv (i, Fin.last d)) (finProdFinEquiv (j, 0)) = _
  rw [← map_pow]
  simpa only [Matrix.coe_reindexRingEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply] using pow_last_zero d k A i j

end LeanCanny.Algebra.PolynomialCoefficientMatrix
