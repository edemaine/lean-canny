/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixMaximalMinorSpan
public import LeanCanny.Algebra.MatrixMinorSection
public import LeanCanny.Algebra.MvCoefficientMass
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Clearing a row-span certificate with a matrix minor

A vector in the row span over a fraction field admits an integral linear
certificate after multiplication by one nonzero minor. The minor's order is
at most the number of columns, so its arithmetic size follows from determinant
bounds rather than from arbitrary denominators of a field-valued solution.
-/

@[expose] public section
namespace LeanCanny.Algebra.RowSpanEliminant
open scoped Matrix BigOperators Classical
universe uR uK uι uκ

variable {R : Type uR} {K : Type uK} {ι : Type uι} {κ : Type uκ}
variable [CommRing R] [Field K] [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- Cramer's numerator using just the selected coordinates of the target. -/
noncomputable def coefficients (A : Matrix ι κ R) (g : ι → κ) (w : κ → R) : ι → R :=
  Matrix.vecMul (w ∘ g) (A.submatrix id g).adjugate

omit [Fintype κ] [DecidableEq ι] in
private theorem selected_vecMul (A : Matrix ι κ R) (g : ι → κ) (u : ι → R) :
    Matrix.vecMul u (A.submatrix id g) = Matrix.vecMul u A ∘ g := by
  funext i
  rfl

omit [Fintype κ] in
theorem certificate (A : Matrix ι κ R) (g : ι → κ) (w : κ → R)
    (hw : ∃ u, Matrix.vecMul u A = w) :
    Matrix.vecMul (coefficients A g w) A = (A.submatrix id g).det • w := by
  obtain ⟨u, rfl⟩ := hw
  have hc : coefficients A g (Matrix.vecMul u A) = (A.submatrix id g).det • u := by
    rw [coefficients, ← selected_vecMul, Matrix.vecMul_vecMul, Matrix.mul_adjugate,
      Matrix.vecMul_smul, Matrix.vecMul_one]
  rw [hc, Matrix.smul_vecMul]

omit [Fintype κ] in
theorem coefficients_map (phi : R →+* K) (A : Matrix ι κ R) (g : ι → κ) (w : κ → R) :
    phi ∘ coefficients A g w = coefficients (A.map phi) g (phi ∘ w) := by
  have ha : (A.submatrix id g).adjugate.map phi = ((A.map phi).submatrix id g).adjugate :=
    phi.map_adjugate (A.submatrix id g)
  funext i
  simp only [Function.comp_apply, coefficients, phi.map_vecMul, ha]
  rfl

omit [Fintype κ] in
theorem certificate_of_map (phi : R →+* K) (hi : Function.Injective phi)
    (A : Matrix ι κ R) (g : ι → κ) (w : κ → R)
    (hw : ∃ u, Matrix.vecMul u (A.map phi) = phi ∘ w) :
    Matrix.vecMul (coefficients A g w) A = (A.submatrix id g).det • w := by
  have H := certificate (A.map phi) g (phi ∘ w) hw
  funext j
  apply hi
  change phi (Matrix.vecMul (coefficients A g w) A j) = phi ((A.submatrix id g).det * w j)
  rw [phi.map_vecMul, coefficients_map, map_mul, phi.map_det]
  exact congrFun H j

/-- Every independent family of rows has a nonzero selected square minor. -/
theorem exists_minor (A : Matrix ι κ K) (hA : LinearIndependent K A.row) :
    ∃ g : ι → κ, (A.submatrix id g).det ≠ 0 := by
  by_contra! h
  have hz : ∀ g : ι → κ, (0 : K) ∣ (A.transpose.submatrix g id).det := by
    intro g
    have he : A.transpose.submatrix g id = (A.submatrix id g).transpose := rfl
    rw [he, Matrix.det_transpose, h g]
  have hs : Function.Surjective (fun v => Matrix.vecMul v A.transpose) := by
    simpa only [Matrix.vecMul_transpose] using hA.mulVec_surjective
  exact not_isUnit_zero (MatrixMaximalMinorSpan.isUnit_of_dvd_maximal_minors_of_surjective A.transpose 0 hz hs)

omit [DecidableEq ι] in
/-- A row-span certificate over an injective field extension clears with one
minor whose order is bounded by the number of columns. -/
theorem exists_certificate (phi : R →+* K) (hi : Function.Injective phi)
    (A : Matrix ι κ R) (w : κ → R)
    (hw : ∃ u, Matrix.vecMul u (A.map phi) = phi ∘ w) :
    ∃ (τ : Type uι) (_ : Fintype τ) (_ : DecidableEq τ) (a : τ → ι) (g : τ → κ),
      Function.Injective a ∧ Fintype.card τ ≤ Fintype.card κ ∧
      ((A.submatrix a g).det ≠ 0) ∧
      ∃ c : τ → R, Matrix.vecMul c (A.submatrix a id) = (A.submatrix a g).det • w := by
  obtain ⟨τ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (A.map phi).row
  let : Fintype τ := Fintype.ofInjective a ha
  let : DecidableEq τ := Classical.decEq τ
  let B : Matrix τ κ R := A.submatrix a id
  have hB : LinearIndependent K (B.map phi).row := hli
  obtain ⟨g, hg⟩ := exists_minor (B.map phi) hB
  have hm : phi ∘ w ∈ Submodule.span K (Set.range (B.map phi).row) := by
    change phi ∘ w ∈ Submodule.span K (Set.range ((A.map phi).row ∘ a))
    rw [hspan, ← range_vecMulLinear]
    exact hw
  have hwB : ∃ u, Matrix.vecMul u (B.map phi) = phi ∘ w := by
    rw [← range_vecMulLinear] at hm
    exact hm
  have hd : (B.submatrix id g).det ≠ 0 := by
    intro hz
    apply hg
    change (phi.mapMatrix (B.submatrix id g)).det = 0
    rw [← phi.map_det, hz, map_zero]
  refine ⟨τ, inferInstance, inferInstance, a, g, ha, ?_, hd,
    coefficients B g w, certificate_of_map phi hi B g w hwB⟩
  simpa using hB.fintype_card_le_finrank

private theorem det_mass_le {η σ : Type*} [Fintype η] [DecidableEq η]
    (A : Matrix η η (MvPolynomial σ ℤ)) (H : ℕ)
    (hH : ∀ i j, MvMass.mass (A i j) ≤ H) :
    MvMass.mass A.det ≤ (Fintype.card η).factorial * H ^ Fintype.card η := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ p : Equiv.Perm η, MvMass.mass (Equiv.Perm.sign p • ∏ j, A (p j) j) := MvMass.sum_le _ _
    _ ≤ ∑ _p : Equiv.Perm η, ∏ _j : η, H := by
      apply Finset.sum_le_sum
      intro p _
      rw [Units.smul_def, MvPolynomial.smul_eq_C_mul]
      calc
        _ ≤ MvMass.mass (MvPolynomial.C (Equiv.Perm.sign p : ℤ)) * MvMass.mass (∏ j, A (p j) j) :=
          MvMass.mul_le _ _
        _ = MvMass.mass (∏ j, A (p j) j) := by rw [MvMass.C, Int.units_natAbs, one_mul]
        _ ≤ ∏ j, MvMass.mass (A (p j) j) := MvMass.prod_le _ _
        _ ≤ ∏ _j : η, H := Finset.prod_le_prod fun j _ => hH (p j) j
    _ = _ := by simp [Fintype.card_perm]

private theorem det_degree_le {η σ : Type*} [Fintype η] [DecidableEq η]
    (A : Matrix η η (MvPolynomial σ ℤ)) (D : ℕ)
    (hD : ∀ i j, (A i j).totalDegree ≤ D) :
    A.det.totalDegree ≤ Fintype.card η * D := by
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro p _
  apply (MvPolynomial.totalDegree_smul_le _ _).trans
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _j : η, D := Finset.sum_le_sum fun j _ => hD (p j) j
    _ = _ := by simp

/-- Integral parameter polynomials admit a bounded eliminant minor whenever
the target is in their row span over an injective field extension. -/
theorem exists_bounded_certificate {σ : Type*}
    (phi : MvPolynomial σ ℤ →+* K) (hi : Function.Injective phi)
    (A : Matrix ι κ (MvPolynomial σ ℤ)) (w : κ → MvPolynomial σ ℤ)
    (D M : ℕ) (hM : 1 ≤ M)
    (hD : ∀ i j, (A i j).totalDegree ≤ D) (hMass : ∀ i j, MvMass.mass (A i j) ≤ M)
    (hw : ∃ u, Matrix.vecMul u (A.map phi) = phi ∘ w) :
    ∃ d : MvPolynomial σ ℤ, d ≠ 0 ∧ d.totalDegree ≤ Fintype.card κ * D ∧
      MvMass.mass d ≤ (Fintype.card κ).factorial * M ^ Fintype.card κ ∧
      ∃ c : ι → MvPolynomial σ ℤ, Matrix.vecMul c A = d • w := by
  obtain ⟨τ, ht, he, a, g, _ha, hcard, hd, c, hc⟩ := exists_certificate phi hi A w hw
  let : Fintype τ := ht
  let : DecidableEq τ := he
  refine ⟨(A.submatrix a g).det, hd, ?_, ?_, ?_⟩
  · exact (det_degree_le _ D (fun i j => hD (a i) (g j))).trans (Nat.mul_le_mul_right D hcard)
  · exact (det_mass_le _ M (fun i j => hMass (a i) (g j))).trans
      (Nat.mul_le_mul (Nat.factorial_le hcard) (Nat.pow_le_pow_right hM hcard))
  · refine ⟨Matrix.vecMul c (MatrixMinorSection.rowSelection a), ?_⟩
    have hm : MatrixMinorSection.rowSelection a * A = A.submatrix a id :=
      Matrix.one_submatrix_mul a (Equiv.refl ι) A
    rw [Matrix.vecMul_vecMul, hm]
    exact hc

/-- Interpret a coefficient row as a polynomial in the affine unknowns. -/
noncomputable def form {σ : Type*} (monomials : κ → (σ →₀ ℕ)) (v : κ → R) : MvPolynomial σ R :=
  ∑ j, MvPolynomial.monomial (monomials j) (v j)

omit [DecidableEq ι] in
theorem form_vecMul {σ : Type*} (monomials : κ → (σ →₀ ℕ)) (A : Matrix ι κ R) (c : ι → R) :
    form monomials (Matrix.vecMul c A) = ∑ i, MvPolynomial.C (c i) * form monomials (A i) := by
  unfold form
  simp only [Matrix.vecMul, dotProduct, map_sum, Finset.mul_sum, MvPolynomial.C_mul_monomial]
  exact Finset.sum_comm

omit [Fintype ι] [DecidableEq ι] in
theorem form_smul {σ : Type*} (monomials : κ → (σ →₀ ℕ)) (d : R) (v : κ → R) :
    form monomials (d • v) = MvPolynomial.C d * form monomials v := by
  simp only [form, Finset.mul_sum, MvPolynomial.C_mul_monomial, Pi.smul_apply, smul_eq_mul]

/-- The bounded minor is an actual parameter eliminant in the generated affine
ideal. The remaining Nullstellensatz obligation is a degree bound ensuring the
constant row belongs to this finite row span. -/
theorem exists_bounded_ideal_certificate {σ π : Type*}
    (phi : MvPolynomial π ℤ →+* K) (hi : Function.Injective phi)
    (A : Matrix ι κ (MvPolynomial π ℤ)) (monomials : κ → (σ →₀ ℕ)) (w : κ → MvPolynomial π ℤ)
    (hw1 : form monomials w = 1) (D M : ℕ) (hM : 1 ≤ M)
    (hD : ∀ i j, (A i j).totalDegree ≤ D) (hMass : ∀ i j, MvMass.mass (A i j) ≤ M)
    (hw : ∃ u, Matrix.vecMul u (A.map phi) = phi ∘ w) :
    ∃ d : MvPolynomial π ℤ, d ≠ 0 ∧ d.totalDegree ≤ Fintype.card κ * D ∧
      MvMass.mass d ≤ (Fintype.card κ).factorial * M ^ Fintype.card κ ∧
      MvPolynomial.C d ∈ Ideal.span (Set.range (fun i => form monomials (A i))) := by
  obtain ⟨d, hd, hdeg, hmass, c, hc⟩ := exists_bounded_certificate phi hi A w D M hM hD hMass hw
  refine ⟨d, hd, hdeg, hmass, ?_⟩
  have he := congrArg (form monomials) hc
  rw [form_vecMul, form_smul, hw1, mul_one] at he
  rw [← he]
  apply Submodule.sum_mem
  intro i _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

end LeanCanny.Algebra.RowSpanEliminant
