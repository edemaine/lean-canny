/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPolynomial
public import LeanCanny.Algebra.RowSpanEliminant
public import Mathlib.Data.Finsupp.Weight

/-! # A bounded affine Macaulay coefficient matrix

Columns enumerate fixed-width affine monomials. Rows enumerate monomial
multiples of the original equations, with zero rows beyond a degree cutoff.
The matrix is exact whenever the cutoff fits the exponent width. No assertion
about the cutoff needed for an affine Nullstellensatz certificate is made.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineMacaulayMatrix
open scoped Classical BigOperators Matrix
open MvPolynomial
set_option backward.isDefEq.respectTransparency false

abbrev Column (n W : ℕ) := Fin (FixedWidthPolynomial.count n W)
abbrev Row (m n W : ℕ) := Fin m × Column n W

variable {R : Type*} [CommRing R] {m n : ℕ}

noncomputable def admissible (p : Fin m → MvPolynomial (Fin n) R) (L W : ℕ)
    (r : Row m n W) : Prop :=
  (FixedWidthPolynomial.vector n W r.2).degree + (p r.1).totalDegree ≤ L

noncomputable def rowPolynomial (p : Fin m → MvPolynomial (Fin n) R) (L W : ℕ)
    (r : Row m n W) : MvPolynomial (Fin n) R :=
  if admissible p L W r then monomial (FixedWidthPolynomial.vector n W r.2) 1 * p r.1 else 0

noncomputable def matrix (p : Fin m → MvPolynomial (Fin n) R) (L W : ℕ) :
    Matrix (Row m n W) (Column n W) R :=
  fun r s => (rowPolynomial p L W r).coeff (FixedWidthPolynomial.vector n W s)

noncomputable def target (n W : ℕ) : Column n W → R :=
  fun s => (1 : MvPolynomial (Fin n) R).coeff (FixedWidthPolynomial.vector n W s)

theorem matrix_entry (p : Fin m → MvPolynomial (Fin n) R) (L W : ℕ)
    (r : Row m n W) (s : Column n W) :
    matrix p L W r s =
      if admissible p L W r then
        if FixedWidthPolynomial.vector n W r.2 ≤ FixedWidthPolynomial.vector n W s then
          (p r.1).coeff (FixedWidthPolynomial.vector n W s - FixedWidthPolynomial.vector n W r.2)
        else 0
      else 0 := by
  by_cases hr : admissible p L W r
  · rw [matrix, rowPolynomial, ite_eq_left hr, ite_eq_left hr, coeff_monomial_mul']
    split_ifs <;> simp
  · simp [matrix, rowPolynomial, hr]

theorem rowPolynomial_totalDegree_le (p : Fin m → MvPolynomial (Fin n) R) (L W : ℕ)
    (r : Row m n W) : (rowPolynomial p L W r).totalDegree ≤ L := by
  by_cases hr : admissible p L W r
  · rw [rowPolynomial, ite_eq_left hr]
    apply (totalDegree_mul _ _).trans
    apply (Nat.add_le_add_right (totalDegree_monomial_le _ (1 : R)) _).trans
    exact hr
  · simp [rowPolynomial, hr]

theorem support_fits_of_totalDegree_le (p : MvPolynomial (Fin n) R) (L W : ℕ)
    (hp : p.totalDegree ≤ L) (hW : L < 2 ^ W) :
    ∀ a ∈ p.support, ∀ i, a i < 2 ^ W := by
  intro a ha i
  have hi : a i ≤ a.degree := by
    rw [Finsupp.degree_eq_sum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact (hi.trans ((le_totalDegree ha).trans hp)).trans_lt hW

/-- Every matrix row reconstructs its actual monomial multiple, including the
zero rows whose shifts exceed the degree allowance. -/
theorem form_row (p : Fin m → MvPolynomial (Fin n) R) (L W : ℕ)
    (hW : L < 2 ^ W) (r : Row m n W) :
    RowSpanEliminant.form (FixedWidthPolynomial.vector n W) (matrix p L W r) =
      rowPolynomial p L W r :=
  FixedWidthPolynomial.sum_monomials_eq n W _
    (support_fits_of_totalDegree_le _ L W (rowPolynomial_totalDegree_le p L W r) hW)

/-- The constant target is represented exactly even with no variables or
zero-width exponent blocks. -/
theorem form_target (n W : ℕ) :
    RowSpanEliminant.form (FixedWidthPolynomial.vector n W) (target (R := R) n W) = 1 := by
  apply FixedWidthPolynomial.sum_monomials_eq
  intro a ha i
  have hz : a = 0 := by
    by_contra h
    exact (mem_support_iff.mp ha) (by simp [coeff_one, Ne.symm h])
  rw [hz]
  exact Nat.two_pow_pos W

theorem rowPolynomial_mem_ideal (p : Fin m → MvPolynomial (Fin n) R) (L W : ℕ)
    (r : Row m n W) : rowPolynomial p L W r ∈ Ideal.span (Set.range p) := by
  unfold rowPolynomial
  split_ifs
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self r.1))
  · exact Ideal.zero_mem _

theorem rows_ideal_le (p : Fin m → MvPolynomial (Fin n) R) (L W : ℕ) (hW : L < 2 ^ W) :
    Ideal.span (Set.range (fun r => RowSpanEliminant.form (FixedWidthPolynomial.vector n W)
      (matrix p L W r))) ≤ Ideal.span (Set.range p) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨r, rfl⟩
  change RowSpanEliminant.form (FixedWidthPolynomial.vector n W) (matrix p L W r) ∈ _
  rw [form_row p L W hW]
  exact rowPolynomial_mem_ideal p L W r



lemma form_coefficient (W : ℕ) (v : Column n W → R) (s : Column n W) :
    (RowSpanEliminant.form (FixedWidthPolynomial.vector n W) v).coeff
      (FixedWidthPolynomial.vector n W s) = v s := by
  simp [RowSpanEliminant.form, coeff_monomial,
    (FixedWidthPolynomial.vector_injective n W).eq_iff]

lemma form_map {S : Type*} [CommRing S] (phi : R →+* S) (W : ℕ) (v : Column n W → R) :
    (RowSpanEliminant.form (FixedWidthPolynomial.vector n W) v).map phi =
      RowSpanEliminant.form (FixedWidthPolynomial.vector n W) (phi ∘ v) := by
  simp [RowSpanEliminant.form]

/-- A bounded affine Bezout identity is exactly enough to supply the finite
row-span premise. The bound concerns each supported multiplier monomial and
the degree of the original, unspecialized equation. -/
theorem rowSpan_of_identity {S : Type*} [CommRing S]
    (phi : R →+* S) (p : Fin m → MvPolynomial (Fin n) R) (L W : ℕ)
    (hW : L < 2 ^ W) (q : Fin m → MvPolynomial (Fin n) S)
    (hcut : ∀ i a, a ∈ (q i).support → a.degree + (p i).totalDegree ≤ L)
    (hid : ∑ i, q i * (p i).map phi = 1) :
    ∃ u, Matrix.vecMul u ((matrix p L W).map phi) = phi ∘ target n W := by
  let u : Row m n W → S := fun r => (q r.1).coeff (FixedWidthPolynomial.vector n W r.2)
  have hq (i : Fin m) : ∀ a ∈ (q i).support, ∀ j, a j < 2 ^ W := by
    intro a ha j
    have hj : a j ≤ a.degree := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact (hj.trans ((Nat.le_add_right _ _).trans (hcut i a ha))).trans_lt hW
  have hr (i : Fin m) :
      ∑ r : Column n W, C ((q i).coeff (FixedWidthPolynomial.vector n W r)) *
        (rowPolynomial p L W (i, r)).map phi = q i * (p i).map phi := by
    calc
      _ = ∑ r : Column n W, monomial (FixedWidthPolynomial.vector n W r)
          ((q i).coeff (FixedWidthPolynomial.vector n W r)) * (p i).map phi := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases ha : admissible p L W (i, r)
        · simp [rowPolynomial, ha, ← mul_assoc, C_mul_monomial]
        · have hz : (q i).coeff (FixedWidthPolynomial.vector n W r) = 0 := by
            by_contra hn
            exact ha (hcut i _ (mem_support_iff.mpr hn))
          simp [rowPolynomial, ha, hz]
      _ = (∑ r : Column n W, monomial (FixedWidthPolynomial.vector n W r)
          ((q i).coeff (FixedWidthPolynomial.vector n W r))) * (p i).map phi :=
        (Finset.sum_mul _ _ _).symm
      _ = _ := by rw [FixedWidthPolynomial.sum_monomials_eq n W _ (hq i)]
  have hrow (r : Row m n W) :
      RowSpanEliminant.form (FixedWidthPolynomial.vector n W) (((matrix p L W).map phi) r) =
        (rowPolynomial p L W r).map phi := by
    change RowSpanEliminant.form (FixedWidthPolynomial.vector n W) (phi ∘ matrix p L W r) = _
    rw [← form_map phi W (matrix p L W r), form_row p L W hW]
  have he : RowSpanEliminant.form (FixedWidthPolynomial.vector n W)
      (Matrix.vecMul u ((matrix p L W).map phi)) = 1 := by
    rw [RowSpanEliminant.form_vecMul]
    simp_rw [hrow]
    rw [Fintype.sum_prod_type]
    change (∑ i, ∑ r, C ((q i).coeff (FixedWidthPolynomial.vector n W r)) *
      (rowPolynomial p L W (i, r)).map phi) = 1
    simp_rw [hr]
    exact hid
  refine ⟨u, ?_⟩
  funext s
  have H := congrArg (fun f : MvPolynomial (Fin n) S => f.coeff (FixedWidthPolynomial.vector n W s)) he
  rw [form_coefficient] at H
  exact H.trans (by simp [target, coeff_one])

section ParameterPolynomials
variable {π K : Type*} [Field K]

/-- A finite row-span certificate produces an actual bounded eliminant in the
ideal of the original affine equations. Only the degree cutoff that makes the
constant target lie in this row span remains to be supplied. -/
theorem exists_bounded_ideal_certificate
    (phi : MvPolynomial π ℤ →+* K) (hi : Function.Injective phi)
    (p : Fin m → MvPolynomial (Fin n) (MvPolynomial π ℤ)) (L W D M : ℕ)
    (hW : L < 2 ^ W) (hM : 1 ≤ M)
    (hD : ∀ i a, ((p i).coeff a).totalDegree ≤ D)
    (hMass : ∀ i a, MvMass.mass ((p i).coeff a) ≤ M)
    (hw : ∃ u, Matrix.vecMul u ((matrix p L W).map phi) = phi ∘ target n W) :
    ∃ d : MvPolynomial π ℤ, d ≠ 0 ∧
      d.totalDegree ≤ FixedWidthPolynomial.count n W * D ∧
      MvMass.mass d ≤ (FixedWidthPolynomial.count n W).factorial *
        M ^ FixedWidthPolynomial.count n W ∧
      MvPolynomial.C d ∈ Ideal.span (Set.range p) := by
  have hd : ∀ r s, (matrix p L W r s).totalDegree ≤ D := by
    intro r s
    rw [matrix_entry]
    split_ifs <;> simp_all only [totalDegree_zero, Nat.zero_le]
  have hm : ∀ r s, MvMass.mass (matrix p L W r s) ≤ M := by
    intro r s
    rw [matrix_entry]
    split_ifs <;> simp_all only [MvMass.zero, Nat.zero_le]
  obtain ⟨d, hne, hdeg, hmass, hmem⟩ := RowSpanEliminant.exists_bounded_ideal_certificate
    phi hi (matrix p L W) (FixedWidthPolynomial.vector n W) (target n W)
    (form_target n W) D M hM hd hm hw
  exact ⟨d, hne, by simpa using hdeg, by simpa using hmass,
    rows_ideal_le p L W hW hmem⟩


/-- The bounded Bezout form of the parameter-eliminant theorem. -/
theorem exists_bounded_ideal_certificate_of_identity
    (phi : MvPolynomial π ℤ →+* K) (hi : Function.Injective phi)
    (p : Fin m → MvPolynomial (Fin n) (MvPolynomial π ℤ)) (L W D M : ℕ)
    (hW : L < 2 ^ W) (hM : 1 ≤ M)
    (hD : ∀ i a, ((p i).coeff a).totalDegree ≤ D)
    (hMass : ∀ i a, MvMass.mass ((p i).coeff a) ≤ M)
    (q : Fin m → MvPolynomial (Fin n) K)
    (hcut : ∀ i a, a ∈ (q i).support → a.degree + (p i).totalDegree ≤ L)
    (hid : ∑ i, q i * (p i).map phi = 1) :
    ∃ d : MvPolynomial π ℤ, d ≠ 0 ∧
      d.totalDegree ≤ FixedWidthPolynomial.count n W * D ∧
      MvMass.mass d ≤ (FixedWidthPolynomial.count n W).factorial *
        M ^ FixedWidthPolynomial.count n W ∧
      MvPolynomial.C d ∈ Ideal.span (Set.range p) :=
  exists_bounded_ideal_certificate phi hi p L W D M hW hM hD hMass
    (rowSpan_of_identity phi p L W hW q hcut hid)

end ParameterPolynomials
end LeanCanny.Algebra.AffineMacaulayMatrix
