/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveMinorEliminant
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # A fixed Gram eliminant for the full projective Macaulay matrix

The determinant of AᵀA has no row selector. Every projective common root
annihilates it. A real coefficient specialization whose complex projective
fiber is empty proves this same fixed determinant nonzero by positivity.
-/

@[expose] public section
namespace LeanCanny.Algebra.ProjectiveGramEliminant
open scoped Classical Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
attribute [local irreducible] Macaulay.fullMatrix Matrix.det

abbrev Coefficient := Polynomial (Polynomial ℤ)

section Matrix
variable {R K ι κ : Type*} [CommRing R] [Field K] [Fintype ι] [Fintype κ]

noncomputable def gram (A : Matrix ι κ R) : Matrix κ κ R := A.transpose * A

omit [Fintype κ] in
lemma gram_map {S : Type*} [CommRing S] (phi : R →+* S) (A : Matrix ι κ R) :
    (gram A).map phi = gram (A.map phi) := by
  rw [gram, Matrix.map_mul]
  rfl

/-- A nonsingular Gram matrix supplies a left inverse even over fields where
sums of squares need not be positive. -/
lemma vecMul_surjective_of_gram_det_ne_zero [DecidableEq κ] (A : Matrix ι κ K) (hA : (gram A).det ≠ 0) :
    Function.Surjective A.vecMul := by
  apply Matrix.vecMul_surjective_iff_exists_left_inverse.mpr
  refine ⟨(gram A)⁻¹ * A.transpose, ?_⟩
  rw [Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul (gram A) (isUnit_iff_ne_zero.mpr hA)

/-- Real positivity is used only for nonvanishing, after transferring full
column rank from the complex coefficient extension. -/
lemma gram_det_pos_of_complex_surjective [DecidableEq κ] (A : Matrix ι κ ℝ)
    (hA : Function.Surjective (A.map Complex.ofRealHom).vecMul) : 0 < (gram A).det := by
  obtain ⟨f, hf⟩ := RowSpanSpecialization.exists_nonzero_minor Complex.ofRealHom A hA
  have hi : Function.Injective A.mulVec := by
    intro x y hxy
    apply Matrix.mulVec_injective_of_det_ne_zero hf
    funext i
    exact congrFun hxy (f i)
  have hp := Matrix.PosDef.conjTranspose_mul_self A hi
  change 0 < (A.transpose * A).det
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial A]
  exact hp.det_pos

omit [Fintype κ] in
lemma gram_entry_mass (A : Matrix ι κ Coefficient) (M : ℕ)
    (hM : ∀ i j, NestedMass.mass (A i j) ≤ M) (r s : κ) :
    NestedMass.mass (gram A r s) ≤ Fintype.card ι * M ^ 2 := by
  change NestedMass.mass (∑ i, A i r * A i s) ≤ _
  apply (NestedMass.sum_le _ _).trans
  calc
    _ ≤ ∑ _i : ι, M * M := Finset.sum_le_sum fun i _ =>
      (NestedMass.mul_le _ _).trans (Nat.mul_le_mul (hM i r) (hM i s))
    _ = _ := by simp [pow_two]

lemma gram_det_mass [DecidableEq κ] (A : Matrix ι κ Coefficient) (M : ℕ)
    (hM : ∀ i j, NestedMass.mass (A i j) ≤ M) :
    NestedMass.mass (gram A).det ≤ (Fintype.card κ).factorial *
      (Fintype.card ι * M ^ 2) ^ Fintype.card κ :=
  NestedMass.det_le _ _ (gram_entry_mass A M hM)


/-- The same canonical determinant as one block matrix with no product sums
in its entries. Its dimensions are the row count plus the column count. -/
noncomputable def block [DecidableEq ι] (A : Matrix ι κ R) : Matrix (Sum ι κ) (Sum ι κ) R :=
  Matrix.fromBlocks 1 A (-A.transpose) 0

lemma block_det [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ R) : (block A).det = (gram A).det := by
  rw [block, Matrix.det_fromBlocks_one₁₁, Matrix.neg_mul, zero_sub, neg_neg]
  rfl


end Matrix

variable {n : ℕ}

noncomputable def polynomial
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) Coefficient)
    (d : Fin (n + 1) → ℕ) (W : ℕ) : Coefficient :=
  (gram (Macaulay.fullMatrix p d W)).det

lemma eval_polynomial {K : Type*} [CommRing K]
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) Coefficient)
    (d : Fin (n + 1) → ℕ) (W : ℕ) (phi : Coefficient →+* K) :
    phi (polynomial p d W) = (gram ((Macaulay.fullMatrix p d W).map phi)).det := by
  rw [polynomial, RingHom.map_det]
  change ((gram (Macaulay.fullMatrix p d W)).map phi).det = _
  rw [gram_map]

/-- The fixed determinant vanishes at every nonzero projective common root,
including roots over complex fields. -/
theorem eval_eq_zero_of_common_root {K : Type*} [Field K]
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) Coefficient)
    (d : Fin (n + 1) → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (hp : ∀ i, (p i).IsHomogeneous (d i))
    (phi : Coefficient →+* K) (x : Fin (n + 1) → K)
    (hx : ∀ i, MvPolynomial.eval₂ phi x (p i) = 0) (hnz : ∃ i, x i ≠ 0) :
    phi (polynomial p d W) = 0 := by
  by_contra h
  rw [eval_polynomial] at h
  have hs := vecMul_surjective_of_gram_det_ne_zero ((Macaulay.fullMatrix p d W).map phi) h
  rw [Macaulay.fullMatrix_map] at hs
  have hz := Macaulay.no_nonzero_root_of_fullMatrix_surjective
    (fun i => (p i).map phi) d W (fun i => (hp i).map phi) hW hs x
    (fun i => by simpa only [MvPolynomial.eval_map] using hx i)
  obtain ⟨i, hi⟩ := hnz
  exact hi (congrFun hz i)

/-- A real specialization that has no nonzero complex projective root makes
the canonical Gram determinant nonzero over the integer parameter ring. -/
theorem ne_zero_of_real_specialization
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) Coefficient)
    (d : Fin (n + 1) → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (phi : Coefficient →+* ℝ)
    (hroot : ∀ x : Fin (n + 1) → ℂ,
      (∀ i, MvPolynomial.eval₂ (Complex.ofRealHom.comp phi) x (p i) = 0) → x = 0) :
    polynomial p d W ≠ 0 := by
  have hs : Function.Surjective
      (((Macaulay.fullMatrix p d W).map phi).map Complex.ofRealHom).vecMul := by
    rw [Macaulay.fullMatrix_map, Macaulay.fullMatrix_map]
    apply Macaulay.fullMatrix_surjective_of_no_nonzero_root _ d W
      (fun i => ((hp i).map phi).map Complex.ofRealHom) hd hW
    intro x hx
    apply hroot x
    intro i
    simpa only [MvPolynomial.eval_map, MvPolynomial.eval₂_map] using hx i
  have hg := gram_det_pos_of_complex_surjective ((Macaulay.fullMatrix p d W).map phi) hs
  intro hz
  have hv : 0 < phi (polynomial p d W) := by
    rw [eval_polynomial p d W phi]
    exact hg
  rw [hz, map_zero] at hv
  exact (lt_irrefl 0) hv

private theorem full_entry_cases
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) Coefficient)
    (d : Fin (n + 1) → ℕ) (W : ℕ)
    (a : Macaulay.MultiplierIndex d W) (r : Macaulay.activeIndices d W) :
    Macaulay.fullMatrix p d W a r = 0 ∨
      ∃ e, Macaulay.fullMatrix p d W a r = (p a.1).coeff e := by
  unfold Macaulay.fullMatrix Macaulay.sourceRow
  rw [MvPolynomial.coeff_monomial_mul']
  split_ifs
  · exact Or.inr ⟨_, one_mul _⟩
  · exact Or.inl rfl

/-- A fixed full-matrix Gram determinant has an explicit integer mass budget. -/
theorem mass_le
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) Coefficient)
    (d : Fin (n + 1) → ℕ) (W M : ℕ)
    (hM : ∀ i e, NestedMass.mass ((p i).coeff e) ≤ M) :
    NestedMass.mass (polynomial p d W) ≤
      (Fintype.card (Macaulay.activeIndices d W)).factorial *
      (Fintype.card (Macaulay.MultiplierIndex d W) * M ^ 2) ^
        Fintype.card (Macaulay.activeIndices d W) := by
  apply gram_det_mass
  intro a r
  rcases full_entry_cases p d W a r with h | ⟨e, h⟩
  · simp only [h, NestedMass.zero, Nat.zero_le]
  · rw [h]
    exact hM a.1 e

end LeanCanny.Algebra.ProjectiveGramEliminant
