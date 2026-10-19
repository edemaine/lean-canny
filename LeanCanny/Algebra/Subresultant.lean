/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Subresultants as selected Sylvester minors

The column order follows Mathlib: shifted copies of `g`, then shifted copies
of `f`, with ascending coefficient rows. Order `k` retains `m-k` and `n-k`
columns. Its coefficient `r` selects row `r`, then rows `k+1,k+2,...`.
This fixes the convention by making order zero exactly Mathlib's resultant.

The polynomial is defined for `k < m` and `k < n`; other orders default to zero.
The top-order boundary cases require a separate interface. In particular this
file does not yet prove the GCD/subresultant theorem needed for coordinate recovery.
-/

@[expose] public section

namespace LeanCanny.Algebra.Subresultant
open Polynomial
open scoped BigOperators

def rowIndex (k r i : ℕ) : ℕ := if i = 0 then r else k + i

def band {R : Type*} [Semiring R] (f : Polynomial R) (d i j : ℕ) : R :=
  if j ≤ i ∧ i ≤ j + d then f.coeff (i - j) else 0

def minor {R : Type*} [Semiring R] (f g : Polynomial R) (m n k r : ℕ) :
    Matrix (Fin ((m - k) + (n - k))) (Fin ((m - k) + (n - k))) R :=
  .of fun i j => j.addCases
    (fun j => band g n (rowIndex k r i.val) j.val)
    (fun j => band f m (rowIndex k r i.val) j.val)

noncomputable def polynomial {R : Type*} [CommRing R] (f g : Polynomial R) (m n k : ℕ) : Polynomial R :=
  if k < m ∧ k < n then ∑ r ∈ Finset.range (k + 1), monomial r (minor f g m n k r).det else 0

theorem rowIndex_zero (i : ℕ) : rowIndex 0 0 i = i := by
  by_cases h : i = 0 <;> simp [rowIndex, h]

theorem minor_zero {R : Type*} [Semiring R] (f g : Polynomial R) (m n : ℕ) :
    minor f g m n 0 0 = Polynomial.sylvester f g m n := by
  funext i j
  induction j using Fin.addCases <;>
    simp only [minor, Nat.sub_zero, Matrix.of_apply, rowIndex_zero, band, Polynomial.sylvester,
      Fin.addCases_left, Fin.addCases_right, Set.mem_Icc]

theorem polynomial_zero {R : Type*} [CommRing R] (f g : Polynomial R) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) : polynomial f g m n 0 = C (f.resultant g m n) := by
  simp [polynomial, hm, hn, minor_zero, Polynomial.resultant]

theorem coeff {R : Type*} [CommRing R] (f g : Polynomial R) (m n k r : ℕ) :
    (polynomial f g m n k).coeff r =
      if k < m ∧ k < n ∧ r ≤ k then (minor f g m n k r).det else 0 := by
  classical
  by_cases h : k < m ∧ k < n
  · simp [polynomial, h, Polynomial.coeff_monomial, Finset.mem_range]
  · simp only [polynomial, ite_eq_right h, Polynomial.coeff_zero]
    have h' : ¬ (k < m ∧ k < n ∧ r ≤ k) := by tauto
    rw [ite_eq_right h']

theorem natDegree_le {R : Type*} [CommRing R] (f g : Polynomial R) (m n k : ℕ) :
    (polynomial f g m n k).natDegree ≤ k := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro r hr
  rw [coeff, ite_eq_right (by omega : ¬ (k < m ∧ k < n ∧ r ≤ k))]

theorem minor_map {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S)
    (f g : Polynomial R) (m n k r : ℕ) :
    minor (f.map φ) (g.map φ) m n k r = (minor f g m n k r).map φ := by
  funext i j
  induction j using Fin.addCases <;>
    simp only [minor, Matrix.of_apply, Matrix.map_apply, Fin.addCases_left, Fin.addCases_right,
      band, Polynomial.coeff_map, apply_ite φ, map_zero]

theorem polynomial_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f g : Polynomial R) (m n k : ℕ) :
    polynomial (f.map φ) (g.map φ) m n k = (polynomial f g m n k).map φ := by
  classical
  unfold polynomial
  split_ifs <;> simp only [minor_map, Polynomial.map_sum, Polynomial.map_monomial, RingHom.map_det, Polynomial.map_zero]
  rfl

theorem first_eq_linear {R : Type*} [CommRing R] (f g : Polynomial R) (m n : ℕ)
    (hm : 1 < m) (hn : 1 < n) :
    polynomial f g m n 1 = C (minor f g m n 1 0).det + C (minor f g m n 1 1).det * X := by
  ext r
  rcases r with _ | (_ | r)
  · simp [coeff, hm, hn]
  · simp [coeff, hm, hn]
  · have hr : ¬ r + 2 ≤ 1 := by omega
    simp [coeff, hm, hn, hr]

end LeanCanny.Algebra.Subresultant
