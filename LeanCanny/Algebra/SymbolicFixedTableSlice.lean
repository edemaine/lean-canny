/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableCoordinateBounds
public import LeanCanny.Algebra.CannyResultantDegrees

/-! # Coefficient slices for symbolic determinant entry sources

The existing integer shifted-entry routine can read one alpha slice while
retaining its genuine outer polynomial index. Slicing is used only for matrix
entries; it is not asserted to commute with determinants or multiplication.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTable
open Polynomial SymbolicScaledSquarefree
open scoped Classical BigOperators

noncomputable def slice {R : Type*} [Semiring R] (p : Polynomial (Polynomial R)) (u : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range (p.natDegree + 1), monomial k ((p.coeff k).coeff u)

theorem slice_coeff {R : Type*} [Semiring R] (p : Polynomial (Polynomial R)) (u k : ℕ) :
    (slice p u).coeff k = (p.coeff k).coeff u := by
  by_cases hk : k < p.natDegree + 1
  · simp [slice, coeff_monomial, hk]
  · have hz : p.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp [slice, coeff_monomial, hk, hz]

theorem slice_zero {R : Type*} [Semiring R] (u : ℕ) : slice (0 : Polynomial (Polynomial R)) u = 0 := by
  ext k
  simp only [slice_coeff, coeff_zero]

theorem slice_add {R : Type*} [Semiring R] (p q : Polynomial (Polynomial R)) (u : ℕ) :
    slice (p + q) u = slice p u + slice q u := by
  ext k
  simp only [slice_coeff, coeff_add]

theorem shift_slice {R : Type*} [CommRing R] (p : Polynomial (Polynomial R)) (c u i j : ℕ) :
    (((shiftFamily p c).coeff i).coeff j).coeff u = ((shiftFamily (slice p u) c).coeff i).coeff j := by
  rw [shiftFamily_coeff_coeff, shiftFamily_coeff_coeff, slice_coeff]
  have hn : ((i + j).choose i : Polynomial R) = C (((i + j).choose i : ℕ) : R) := (map_natCast C _).symm
  have hc : (-(c : Polynomial R)) ^ i = C ((-(c : R)) ^ i) := by simp only [map_pow, map_neg, map_natCast]
  rw [hn, hc, coeff_mul_C, coeff_C_mul]

theorem constant_slice {R : Type*} [CommRing R] (p : Polynomial (Polynomial R)) (u i j : ℕ) :
    (((p.map C).coeff i).coeff j).coeff u = (((slice p u).map C).coeff i).coeff j := by
  simp only [coeff_map, coeff_C, slice_coeff]
  split_ifs <;> simp only [coeff_zero]

theorem sylvester_slice {R : Type*} [CommRing R] (p q : Polynomial (Polynomial R))
    (c m n u v : ℕ) (i j : Fin (m + n)) :
    (((Polynomial.sylvester (shiftFamily p c) (q.map C) m n i j).coeff v).coeff u) =
      (Polynomial.sylvester (shiftFamily (slice p u) c) ((slice q u).map C) m n i j).coeff v := by
  induction j using Fin.addCases <;>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
  · split_ifs
    · exact constant_slice q u _ v
    · simp only [coeff_zero]
  · split_ifs
    · exact shift_slice p c u _ v
    · simp only [coeff_zero]

theorem shift_inner_degree {R : Type*} [CommRing R] (p : Polynomial (Polynomial R)) (c E : ℕ)
    (hE : ∀ k, (p.coeff k).natDegree ≤ E) (i j : ℕ) :
    (((shiftFamily p c).coeff i).coeff j).natDegree ≤ E := by
  rw [shiftFamily_coeff_coeff]
  calc
    _ ≤ ((i + j).choose i : Polynomial R).natDegree + (p.coeff (i + j)).natDegree +
        i * (-(c : Polynomial R)).natDegree :=
      natDegree_mul_le.trans (Nat.add_le_add natDegree_mul_le natDegree_pow_le)
    _ ≤ E := by simpa only [natDegree_natCast, natDegree_neg, Nat.zero_add, Nat.mul_zero,
      Nat.add_zero] using hE (i + j)

theorem sylvester_inner_degree {R : Type*} [CommRing R]
    (p q : Polynomial (Polynomial R)) (c m n E : ℕ)
    (hp : ∀ k, (p.coeff k).natDegree ≤ E) (hq : ∀ k, (q.coeff k).natDegree ≤ E)
    (i j : Fin (m + n)) (k : ℕ) :
    ((Polynomial.sylvester (shiftFamily p c) (q.map C) m n i j).coeff k).natDegree ≤ E := by
  induction j using Fin.addCases <;>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
  · split_ifs
    · simp only [coeff_map, coeff_C]
      split_ifs
      · exact hq _
      · simp
    · simp
  · split_ifs
    · exact shift_inner_degree p c E hp _ k
    · simp

theorem encoded_sylvester_coefficient {R : Type*} [CommRing R]
    (p q : Polynomial (Polynomial R)) (c m n E B : ℕ)
    (hp : ∀ k, (p.coeff k).natDegree ≤ E) (hq : ∀ k, (q.coeff k).natDegree ≤ E)
    (hB : E < B) (i j : Fin (m + n)) (d : ℕ) :
    (PolynomialKronecker.encode B (Polynomial.sylvester (shiftFamily p c) (q.map C) m n i j)).coeff d =
      (Polynomial.sylvester (shiftFamily (slice p (d % B)) c) ((slice q (d % B)).map C) m n i j).coeff (d / B) := by
  rw [PolynomialKronecker.coefficient_any B (by omega) _ ?_ d]
  · exact sylvester_slice p q c m n _ _ i j
  · intro k
    induction j using Fin.addCases <;>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
    · split_ifs
      · simp only [coeff_map, coeff_C]
        split_ifs
        · exact (hq _).trans_lt hB
        · simpa only [natDegree_zero] using (Nat.zero_le E).trans_lt hB
      · simpa only [coeff_zero, natDegree_zero] using (Nat.zero_le E).trans_lt hB
    · split_ifs
      · exact (shift_inner_degree p c E hp _ k).trans_lt hB
      · simpa only [coeff_zero, natDegree_zero] using (Nat.zero_le E).trans_lt hB

end LeanCanny.Algebra.SymbolicFixedTable
