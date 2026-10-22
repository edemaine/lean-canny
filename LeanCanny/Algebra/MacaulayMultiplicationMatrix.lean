/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayActiveCharacteristic
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # The full graded Macaulay multiplication matrix

Rows are all degree-compatible monomial multiples of all input polynomials.
The square Macaulay matrix selects one such row for each level monomial.
Finite coefficient reconstruction identifies row combinations with polynomial
multiplication, without identity padding in either index set.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def multiplierIndices (d : Fin n → ℕ) (W : ℕ) (i : Fin n) : Finset (Index n W) :=
  Finset.univ.filter (fun r => (FixedWidthPolynomial.vector n W r).degree + d i = level d)

theorem mem_multiplierIndices (d : Fin n → ℕ) (W : ℕ) (i : Fin n) (r : Index n W) :
    r ∈ multiplierIndices d W i ↔ (FixedWidthPolynomial.vector n W r).degree + d i = level d := by
  simp only [multiplierIndices, Finset.mem_filter, Finset.mem_univ, true_and]

abbrev MultiplierIndex (d : Fin n → ℕ) (W : ℕ) := (i : Fin n) × ↥(multiplierIndices d W i)

noncomputable def sourceRow (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (a : MultiplierIndex d W) : MvPolynomial (Fin n) R :=
  MvPolynomial.monomial (FixedWidthPolynomial.vector n W a.2.val) 1 * p a.1

theorem sourceRow_homogeneous (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (a : MultiplierIndex d W) :
    (sourceRow p d W a).IsHomogeneous (level d) := by
  have h := (MvPolynomial.isHomogeneous_monomial (d := FixedWidthPolynomial.vector n W a.2.val) (1 : R) rfl).mul (hp a.1)
  simpa only [sourceRow, (mem_multiplierIndices d W a.1 a.2.val).mp a.2.property] using h

noncomputable def fullMatrix (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    Matrix (MultiplierIndex d W) (activeIndices d W) R :=
  fun a r => (sourceRow p d W a).coeff (FixedWidthPolynomial.vector n W r.val)

noncomputable def selectedMultiplier (d : Fin n → ℕ) (W : ℕ) (r : activeIndices d W) : MultiplierIndex d W := by
  have hr := (mem_activeIndices d W r.val).mp r.property
  have hb (j : Fin n) : remainder d (FixedWidthPolynomial.vector n W r.val) hr j < 2 ^ W := by
    have h : remainder d (FixedWidthPolynomial.vector n W r.val) hr j ≤ FixedWidthPolynomial.vector n W r.val j := by
      simp only [remainder, Finsupp.tsub_apply]
      exact Nat.sub_le _ _
    exact h.trans_lt (FixedWidthPolynomial.vector_lt n W r.val j)
  refine ⟨pivot d _ hr, FixedWidthPolynomial.index n W (remainder d _ hr) hb, ?_⟩
  rw [mem_multiplierIndices, FixedWidthPolynomial.vector_index]
  exact remainder_degree d _ hr

theorem selectedMultiplier_add (d : Fin n → ℕ) (W : ℕ) (r : activeIndices d W) :
    FixedWidthPolynomial.vector n W (selectedMultiplier d W r).2.val +
      Finsupp.single (selectedMultiplier d W r).1 (d (selectedMultiplier d W r).1) =
        FixedWidthPolynomial.vector n W r.val := by
  change FixedWidthPolynomial.vector n W (FixedWidthPolynomial.index n W _ _) + _ = _
  rw [FixedWidthPolynomial.vector_index]
  exact remainder_add d _ _

theorem selectedMultiplier_injective (d : Fin n → ℕ) (W : ℕ) : Function.Injective (selectedMultiplier d W) := by
  intro r s h
  have he := congrArg (fun a : MultiplierIndex d W =>
    FixedWidthPolynomial.vector n W a.2.val + Finsupp.single a.1 (d a.1)) h
  rw [selectedMultiplier_add, selectedMultiplier_add] at he
  exact Subtype.ext (FixedWidthPolynomial.vector_injective n W he)

theorem sourceRow_selected (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) (r : activeIndices d W) :
    sourceRow p d W (selectedMultiplier d W r) =
      rowPolynomial p d W r.val ((mem_activeIndices d W r.val).mp r.property) := by
  change MvPolynomial.monomial (FixedWidthPolynomial.vector n W (FixedWidthPolynomial.index n W _ _)) 1 * _ = _
  rw [FixedWidthPolynomial.vector_index]
  rfl

theorem fullMatrix_selected (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (fullMatrix p d W).submatrix (selectedMultiplier d W) id = activeMinor p d W := by
  funext r s
  change (sourceRow p d W (selectedMultiplier d W r)).coeff (FixedWidthPolynomial.vector n W s.val) =
    matrix p d W r.val s.val
  rw [sourceRow_selected, matrix, dite_eq_left ((mem_activeIndices d W r.val).mp r.property)]

noncomputable def sourceCoefficients (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) : MultiplierIndex d W → R :=
  fun a => (q a.1).coeff (FixedWidthPolynomial.vector n W a.2.val)

noncomputable def assemble (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (v : MultiplierIndex d W → R) : MvPolynomial (Fin n) R :=
  ∑ a, MvPolynomial.C (v a) * sourceRow p d W a

theorem multiplier_reconstruction (q : MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) (i : Fin n)
    (hW : level d < 2 ^ W) (hq : ∀ m ∈ q.support, m.degree + d i = level d) :
    (∑ r : multiplierIndices d W i,
      MvPolynomial.monomial (FixedWidthPolynomial.vector n W r.val) (q.coeff (FixedWidthPolynomial.vector n W r.val))) = q := by
  calc
    _ = ∑ r ∈ multiplierIndices d W i, MvPolynomial.monomial (FixedWidthPolynomial.vector n W r)
        (q.coeff (FixedWidthPolynomial.vector n W r)) := Finset.sum_coe_sort _ _
    _ = ∑ r : Index n W, MvPolynomial.monomial (FixedWidthPolynomial.vector n W r)
        (q.coeff (FixedWidthPolynomial.vector n W r)) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro r _ hr
      have hc : q.coeff (FixedWidthPolynomial.vector n W r) = 0 := by
        by_contra hc
        exact hr ((mem_multiplierIndices d W i r).mpr (hq _ (MvPolynomial.mem_support_iff.mpr hc)))
      rw [hc, map_zero]
    _ = q := FixedWidthPolynomial.sum_monomials_eq n W q (by
      intro m hm j
      have hg := hq m hm
      have hj : m j ≤ m.degree := by
        rw [Finsupp.degree_eq_sum]
        exact Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
      exact (hj.trans (by omega)).trans_lt hW)

theorem assemble_coefficients (p q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hW : level d < 2 ^ W) (hq : ∀ i m, m ∈ (q i).support → m.degree + d i = level d) :
    assemble p d W (sourceCoefficients q d W) = ∑ i, q i * p i := by
  unfold assemble
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (∑ r : multiplierIndices d W i, MvPolynomial.monomial (FixedWidthPolynomial.vector n W r.val)
        ((q i).coeff (FixedWidthPolynomial.vector n W r.val))) * p i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      simp only [sourceCoefficients, sourceRow, ← mul_assoc, MvPolynomial.C_mul_monomial, mul_one]
    _ = q i * p i := by rw [multiplier_reconstruction (q i) d W i hW (hq i)]

theorem vecMul_fullMatrix (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (v : MultiplierIndex d W → R) (r : activeIndices d W) :
    Matrix.vecMul v (fullMatrix p d W) r = (assemble p d W v).coeff (FixedWidthPolynomial.vector n W r.val) := by
  change (∑ a, v a * fullMatrix p d W a r) = _
  simp only [assemble, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, fullMatrix]

end LeanCanny.Algebra.Macaulay
