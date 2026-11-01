/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveBoxGramEliminant

/-! # The actual full-box Gram determinant over a relative coefficient ring

The coefficient ring is arbitrary. Common projective roots annihilate the
constructed determinant. A real specialization with empty complex projective
fiber makes its value positive. Degree bounds use the fixed relative box,
without multiplying its dimension by an old algebra rank.
-/

@[expose] public section
namespace LeanCanny.Algebra.RelativeProjectiveBoxGram
open MvPolynomial ProjectiveGramEliminant
open scoped Classical Matrix BigOperators
variable {n : ℕ} {C : Type*} [CommRing C]

noncomputable def polynomial (p : Fin n → MvPolynomial (Fin n) C) (d : Fin n → ℕ) (W : ℕ) : C :=
  (gram (MacaulayFullBox.matrix p d W)).det

theorem eval_polynomial {K : Type*} [CommRing K] (p : Fin n → MvPolynomial (Fin n) C)
    (d : Fin n → ℕ) (W : ℕ) (φ : C →+* K) :
    φ (polynomial p d W) = (gram ((MacaulayFullBox.matrix p d W).map φ)).det := by
  rw [polynomial, RingHom.map_det]
  change ((gram (MacaulayFullBox.matrix p d W)).map φ).det = _
  rw [gram_map]

theorem root {K : Type*} [Field K] (p : Fin n → MvPolynomial (Fin n) C)
    (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (φ : C →+* K) (x : Fin n → K)
    (hx : ∀ i, (p i).eval₂ φ x = 0) (hnz : ∃ i, x i ≠ 0) : φ (polynomial p d W) = 0 := by
  by_contra H
  rw [eval_polynomial, MacaulayFullBox.matrix_map] at H
  let A := MacaulayFullBox.matrix (fun i => (p i).map φ) d W
  have HZ : A *ᵥ Macaulay.evaluationVector d W x = 0 := by
    apply MacaulayFullBox.mulVec_evaluation_eq_zero _ d W (fun i => (hp i).map φ) hW x
    intro i
    simpa only [MvPolynomial.eval_map] using hx i
  have HI := Matrix.mulVec_injective_of_det_ne_zero H
  have HV : gram A *ᵥ Macaulay.evaluationVector d W x = 0 := by
    rw [gram, ← Matrix.mulVec_mulVec, HZ, Matrix.mulVec_zero]
  have HE := HI (HV.trans (Matrix.mulVec_zero _).symm)
  obtain ⟨i, hi⟩ := hnz
  obtain ⟨r, hr⟩ := Macaulay.evaluationVector_ne_zero d W hW x i hi
  exact hr (congrFun HE r)

theorem positive (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) C)
    (d : Fin (n + 1) → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (φ : C →+* ℝ)
    (hroot : ∀ x : Fin (n + 1) → ℂ,
      (∀ i, (p i).eval₂ (Complex.ofRealHom.comp φ) x = 0) → x = 0) :
    0 < φ (polynomial p d W) := by
  let pr := fun i => (p i).map φ
  let pc := fun i => (pr i).map Complex.ofRealHom
  have HS : Function.Surjective (Macaulay.fullMatrix pc d W).vecMul := by
    apply Macaulay.fullMatrix_surjective_of_no_nonzero_root _ d W
      (fun i => ((hp i).map φ).map Complex.ofRealHom) hd hW
    intro x hx
    apply hroot x
    intro i
    simpa only [pc, pr, MvPolynomial.eval_map, MvPolynomial.eval₂_map] using hx i
  have HC := MacaulayFullBox.mulVec_injective_of_fullMatrix_surjective pc d W
    (fun i => ((hp i).map φ).map Complex.ofRealHom) HS
  have HR : Function.Injective (MacaulayFullBox.matrix pr d W).mulVec := by
    intro x y hxy
    have H : Complex.ofRealHom ∘ x = Complex.ofRealHom ∘ y := by
      apply HC
      funext a
      have H := congrArg Complex.ofRealHom (congrFun hxy a)
      simpa only [RingHom.map_mulVec, MacaulayFullBox.matrix_map] using H
    funext i
    exact Complex.ofReal_injective (congrFun H i)
  have Hpos := (Matrix.PosDef.conjTranspose_mul_self (MacaulayFullBox.matrix pr d W) HR).det_pos
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at Hpos
  rw [eval_polynomial, MacaulayFullBox.matrix_map]
  exact Hpos

private theorem block_entry_property (p : Fin n → MvPolynomial (Fin n) C) (d : Fin n → ℕ) (W : ℕ)
    (P : C → Prop) (h0 : P 0) (h1 : P 1) (hn : ∀ a, P a → P (-a))
    (hp : ∀ i e, P ((p i).coeff e)) :
    ∀ a b, P (block (MacaulayFullBox.matrix p d W) a b) := by
  have HA : ∀ a b, P (MacaulayFullBox.matrix p d W a b) := by
    intro a b
    rcases MacaulayFullBox.entry_cases p d W a b with H | H | ⟨i, e, H⟩
    · rw [H]; exact h0
    · rw [H]; exact h1
    · rw [H]; exact hp i e
  intro a b
  rcases a with a | a <;> rcases b with b | b
  · change P ((1 : Matrix (MacaulayFullBox.Row n W) (MacaulayFullBox.Row n W) C) a b)
    by_cases H : a = b
    · simpa only [Matrix.one_apply, ite_eq_left H] using h1
    · simpa only [Matrix.one_apply, ite_eq_right H] using h0
  · exact HA a b
  · exact hn _ (HA b a)
  · exact h0

section Degrees
variable {R : Type*} [CommRing R]

theorem outer_degree (p : Fin n → MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ) (W E : ℕ)
    (hp : ∀ i e, ((p i).coeff e).natDegree ≤ E) :
    (polynomial p d W).natDegree ≤ (n + 2) * FixedWidthPolynomial.count n W * E := by
  have H := det_natDegree_le (block (MacaulayFullBox.matrix p d W)) (fun _ => E)
    (block_entry_property p d W (fun a => a.natDegree ≤ E)
      (by simp) (by simp) (fun a ha => by simpa only [Polynomial.natDegree_neg] using ha) hp)
  rw [ProjectiveGramEliminant.block_det] at H
  simpa only [polynomial, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ProjectiveBoxGramEliminant.card_block] using H

theorem inner_degree (p : Fin n → MvPolynomial (Fin n) (Polynomial (Polynomial R)))
    (d : Fin n → ℕ) (W E : ℕ) (hp : ∀ i e j, (((p i).coeff e).coeff j).natDegree ≤ E) (j : ℕ) :
    ((polynomial p d W).coeff j).natDegree ≤ (n + 2) * FixedWidthPolynomial.count n W * E := by
  have H := PolynomialKronecker.determinant_inner_degree (block (MacaulayFullBox.matrix p d W)) (fun _ => E)
    (fun a b k => block_entry_property p d W (fun a => (a.coeff k).natDegree ≤ E)
      (by simp) (by simp only [Polynomial.coeff_one]; split_ifs <;> simp)
      (fun a ha => by simpa only [Polynomial.coeff_neg, Polynomial.natDegree_neg] using ha)
      (fun i e => hp i e k) a b) j
  rw [ProjectiveGramEliminant.block_det] at H
  simpa only [polynomial, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ProjectiveBoxGramEliminant.card_block] using H

end Degrees
end LeanCanny.Algebra.RelativeProjectiveBoxGram
