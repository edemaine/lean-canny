/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RowSpanSpecialization
public import LeanCanny.Algebra.MacaulayProjectiveCriterion
public import LeanCanny.Algebra.MacaulayMaximalMinors
public import LeanCanny.Algebra.NestedCoefficientMass
public import LeanCanny.Algebra.PolynomialKronecker

/-! # Bounded parameter eliminants from one empty projective fiber

Select a nonzero maximal minor of the full Macaulay matrix using a single
specialization without projective roots. Every projective common root in
any other characteristic-zero specialization annihilates this same minor.
The degree and mass estimates use the full number of monomial columns.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace LeanCanny.Algebra.ProjectiveMinorEliminant
open scoped Classical Matrix BigOperators
open Polynomial

abbrev Coefficient := Polynomial (Polynomial ℤ)

private theorem full_entry_cases {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) Coefficient) (d : Fin n → ℕ) (W : ℕ)
    (a : Macaulay.MultiplierIndex d W) (r : Macaulay.activeIndices d W) :
    Macaulay.fullMatrix p d W a r = 0 ∨
      ∃ e, Macaulay.fullMatrix p d W a r = (p a.1).coeff e := by
  unfold Macaulay.fullMatrix Macaulay.sourceRow
  rw [MvPolynomial.coeff_monomial_mul']
  split_ifs
  · exact Or.inr ⟨_, one_mul _⟩
  · exact Or.inl rfl

theorem minor_eval_eq_zero {n : ℕ} {E : Type*} [CommRing E] [IsDomain E]
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) Coefficient)
    (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (f : Macaulay.activeIndices d W → Macaulay.MultiplierIndex d W)
    (phi : Coefficient →+* E) (x : Fin (n + 1) → E)
    (hx : ∀ i, MvPolynomial.eval₂ phi x (p i) = 0) (hnz : ∃ j, x j ≠ 0) :
    phi ((Macaulay.fullMatrix p d W).submatrix f id).det = 0 := by
  obtain ⟨c, hc⟩ := MacaulayUniversal.polynomialValue_dvd_fullMinor d W hdegree hW p hp hd f
  rw [hc, map_mul,
    MacaulayUniversal.map_polynomialValue_eq_zero_of_common_root phi d W hdegree hW p hp hd x hx hnz,
    zero_mul]

/-- A root-free specialization supplies an actual nonzero parameter minor.
The specializing map itself may have a kernel. -/
theorem exists_minor {n : ℕ} {K : Type*} [Field K] [IsAlgClosed K]
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) Coefficient)
    (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (phi : Coefficient →+* K)
    (hroot : ∀ x : Fin (n + 1) → K,
      (∀ i, MvPolynomial.eval₂ phi x (p i) = 0) → x = 0) :
    ∃ f : Macaulay.activeIndices d W → Macaulay.MultiplierIndex d W,
      ((Macaulay.fullMatrix p d W).submatrix f id).det ≠ 0 := by
  apply RowSpanSpecialization.exists_nonzero_minor phi (Macaulay.fullMatrix p d W)
  rw [Macaulay.fullMatrix_map]
  apply Macaulay.fullMatrix_surjective_of_no_nonzero_root _ d W
    (fun i => (hp i).map phi) hd hW
  intro x hx
  apply hroot x
  intro i
  simpa only [MvPolynomial.eval_map] using hx i

/-- Explicit determinant budgets for the selected nonzero parameter minor. -/
theorem exists_bounded_minor {n : ℕ} {K : Type*} [Field K] [IsAlgClosed K]
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) Coefficient)
    (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (phi : Coefficient →+* K)
    (hroot : ∀ x : Fin (n + 1) → K,
      (∀ i, MvPolynomial.eval₂ phi x (p i) = 0) → x = 0)
    (Ds Dt M : ℕ)
    (hDs : ∀ i e, ((p i).coeff e).natDegree ≤ Ds)
    (hDt : ∀ i e j, (((p i).coeff e).coeff j).natDegree ≤ Dt)
    (hM : ∀ i e, NestedMass.mass ((p i).coeff e) ≤ M) :
    ∃ f : Macaulay.activeIndices d W → Macaulay.MultiplierIndex d W,
      let H := ((Macaulay.fullMatrix p d W).submatrix f id).det
      let C := Fintype.card (Macaulay.activeIndices d W)
      H ≠ 0 ∧ H.natDegree ≤ C * Ds ∧
        (∀ j, (H.coeff j).natDegree ≤ C * Dt) ∧
        NestedMass.mass H ≤ C.factorial * M ^ C := by
  obtain ⟨f, hf⟩ := exists_minor p d W hW hp hd phi hroot
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · have h := det_natDegree_le ((Macaulay.fullMatrix p d W).submatrix f id)
      (fun _ => Ds) (fun r s => by
        rcases full_entry_cases p d W (f r) s with hz | ⟨e, he⟩
        · simpa only [Matrix.submatrix_apply, id_eq, hz, Polynomial.natDegree_zero] using Nat.zero_le Ds
        · simpa only [Matrix.submatrix_apply, id_eq, he] using hDs (f r).1 e)
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using h
  · intro j
    have h := PolynomialKronecker.determinant_inner_degree
      ((Macaulay.fullMatrix p d W).submatrix f id) (fun _ => Dt)
      (fun r s k => by
        rcases full_entry_cases p d W (f r) s with hz | ⟨e, he⟩
        · simp only [Matrix.submatrix_apply, id_eq, hz, Polynomial.coeff_zero, Polynomial.natDegree_zero]
          exact Nat.zero_le Dt
        · simpa only [Matrix.submatrix_apply, id_eq, he] using hDt (f r).1 e k) j
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using h
  · apply NestedMass.det_le
    intro r s
    rcases full_entry_cases p d W (f r) s with hz | ⟨e, he⟩
    · simp only [Matrix.submatrix_apply, id_eq, hz, NestedMass.zero]
      exact Nat.zero_le M
    · simpa only [Matrix.submatrix_apply, id_eq, he] using hM (f r).1 e

end LeanCanny.Algebra.ProjectiveMinorEliminant
