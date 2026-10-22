/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayFullBox

/-! # The canonical Gram eliminant of the fixed-width full Macaulay box -/

@[expose] public section
namespace LeanCanny.Algebra.ProjectiveBoxGramEliminant
open scoped Classical Matrix BigOperators
open ProjectiveGramEliminant
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] MacaulayFullBox.matrix Matrix.det

abbrev Coefficient := Polynomial (Polynomial ℤ)
variable {n : ℕ}

noncomputable def polynomial (p : Fin n → MvPolynomial (Fin n) Coefficient)
    (d : Fin n → ℕ) (W : ℕ) : Coefficient :=
  (gram (MacaulayFullBox.matrix p d W)).det

lemma eval_polynomial {K : Type*} [CommRing K]
    (p : Fin n → MvPolynomial (Fin n) Coefficient) (d : Fin n → ℕ) (W : ℕ)
    (phi : Coefficient →+* K) :
    phi (polynomial p d W) = (gram ((MacaulayFullBox.matrix p d W).map phi)).det := by
  rw [polynomial, RingHom.map_det]
  change ((gram (MacaulayFullBox.matrix p d W)).map phi).det = _
  rw [gram_map]

lemma block_det (p : Fin n → MvPolynomial (Fin n) Coefficient)
    (d : Fin n → ℕ) (W : ℕ) :
    (block (MacaulayFullBox.matrix p d W)).det = polynomial p d W :=
  ProjectiveGramEliminant.block_det _

/-- Every projective common root kills the fixed determinant, over any field. -/
theorem eval_eq_zero_of_common_root {K : Type*} [Field K]
    (p : Fin n → MvPolynomial (Fin n) Coefficient) (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (phi : Coefficient →+* K) (x : Fin n → K)
    (hx : ∀ i, MvPolynomial.eval₂ phi x (p i) = 0) (hnz : ∃ i, x i ≠ 0) :
    phi (polynomial p d W) = 0 := by
  by_contra h
  rw [eval_polynomial, MacaulayFullBox.matrix_map] at h
  let A := MacaulayFullBox.matrix (fun i => (p i).map phi) d W
  have hz : A *ᵥ Macaulay.evaluationVector d W x = 0 := by
    apply MacaulayFullBox.mulVec_evaluation_eq_zero _ d W (fun i => (hp i).map phi) hW x
    intro i
    simpa only [MvPolynomial.eval_map] using hx i
  have hi := Matrix.mulVec_injective_of_det_ne_zero h
  have hv : gram A *ᵥ Macaulay.evaluationVector d W x = 0 := by
    rw [gram, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  have he := hi (hv.trans (Matrix.mulVec_zero _).symm)
  obtain ⟨i, hi⟩ := hnz
  obtain ⟨r, hr⟩ := Macaulay.evaluationVector_ne_zero d W hW x i hi
  exact hr (congrFun he r)

/-- A single real specialization with empty complex projective fiber proves
nonvanishing without selecting any minor. -/
theorem ne_zero_of_real_specialization
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) Coefficient)
    (d : Fin (n + 1) → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (phi : Coefficient →+* ℝ)
    (hroot : ∀ x : Fin (n + 1) → ℂ,
      (∀ i, MvPolynomial.eval₂ (Complex.ofRealHom.comp phi) x (p i) = 0) → x = 0) :
    polynomial p d W ≠ 0 := by
  let pr := fun i => (p i).map phi
  let pc := fun i => (pr i).map Complex.ofRealHom
  have hs : Function.Surjective (Macaulay.fullMatrix pc d W).vecMul := by
    apply Macaulay.fullMatrix_surjective_of_no_nonzero_root _ d W
      (fun i => ((hp i).map phi).map Complex.ofRealHom) hd hW
    intro x hx
    apply hroot x
    intro i
    simpa only [pc, pr, MvPolynomial.eval_map, MvPolynomial.eval₂_map] using hx i
  have hc := MacaulayFullBox.mulVec_injective_of_fullMatrix_surjective pc d W
    (fun i => ((hp i).map phi).map Complex.ofRealHom) hs
  have hr : Function.Injective (MacaulayFullBox.matrix pr d W).mulVec := by
    intro x y hxy
    have H : Complex.ofRealHom ∘ x = Complex.ofRealHom ∘ y := by
      apply hc
      funext a
      have H := congrArg Complex.ofRealHom (congrFun hxy a)
      simpa only [RingHom.map_mulVec, MacaulayFullBox.matrix_map] using H
    funext i
    exact Complex.ofReal_injective (congrFun H i)
  have hpos := (Matrix.PosDef.conjTranspose_mul_self (MacaulayFullBox.matrix pr d W) hr).det_pos
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hpos
  intro hz
  have hv : 0 < phi (polynomial p d W) := by
    rw [eval_polynomial, MacaulayFullBox.matrix_map]
    exact hpos
  rw [hz, map_zero] at hv
  exact (lt_irrefl 0) hv

lemma mass_le (p : Fin n → MvPolynomial (Fin n) Coefficient)
    (d : Fin n → ℕ) (W M : ℕ) (h1 : 1 ≤ M)
    (hM : ∀ i e, NestedMass.mass ((p i).coeff e) ≤ M) :
    NestedMass.mass (polynomial p d W) ≤
      (FixedWidthPolynomial.count n W).factorial *
      ((n + 1) * FixedWidthPolynomial.count n W * M ^ 2) ^ FixedWidthPolynomial.count n W := by
  have h := gram_det_mass (MacaulayFullBox.matrix p d W) M (fun a b => by
    rcases MacaulayFullBox.entry_cases p d W a b with hz | ho | ⟨i, e, he⟩
    · simp only [hz, NestedMass.zero, Nat.zero_le]
    · rw [ho]
      change NestedMass.mass (Polynomial.C (Polynomial.C (1 : ℤ))) ≤ M
      rw [NestedMass.C, coefficientMass_C]
      exact h1
    · rw [he]
      exact hM i e)
  simpa only [polynomial, MacaulayFullBox.card_column, MacaulayFullBox.card_row] using h

lemma card_block (n W : ℕ) :
    Fintype.card (Sum (MacaulayFullBox.Row n W) (MacaulayFullBox.Column n W)) =
      (n + 2) * FixedWidthPolynomial.count n W := by
  rw [Fintype.card_sum, MacaulayFullBox.card_row, MacaulayFullBox.card_column]
  ring

private lemma block_entry_property (p : Fin n → MvPolynomial (Fin n) Coefficient)
    (d : Fin n → ℕ) (W : ℕ) (P : Coefficient → Prop)
    (h0 : P 0) (h1 : P 1) (hn : ∀ a, P a → P (-a))
    (hp : ∀ i e, P ((p i).coeff e)) :
    ∀ a b, P (block (MacaulayFullBox.matrix p d W) a b) := by
  have hA : ∀ a b, P (MacaulayFullBox.matrix p d W a b) := by
    intro a b
    rcases MacaulayFullBox.entry_cases p d W a b with hz | ho | ⟨i, e, he⟩
    · rw [hz]; exact h0
    · rw [ho]; exact h1
    · rw [he]; exact hp i e
  intro a b
  rcases a with a | a <;> rcases b with b | b
  · change P ((1 : Matrix (MacaulayFullBox.Row n W) (MacaulayFullBox.Row n W) Coefficient) a b)
    by_cases h : a = b
    · simpa only [Matrix.one_apply, ite_eq_left h] using h1
    · simpa only [Matrix.one_apply, ite_eq_right h] using h0
  · exact hA a b
  · exact hn _ (hA b a)
  · exact h0

/-- The block determinant uses only original entries, their negatives and units.
Its dimension supplies a uniform degree bound in either parameter. -/
lemma outer_degree (p : Fin n → MvPolynomial (Fin n) Coefficient)
    (d : Fin n → ℕ) (W Ds : ℕ)
    (hp : ∀ i e, ((p i).coeff e).natDegree ≤ Ds) :
    (polynomial p d W).natDegree ≤ (n + 2) * FixedWidthPolynomial.count n W * Ds := by
  have h := det_natDegree_le (block (MacaulayFullBox.matrix p d W)) (fun _ => Ds)
    (block_entry_property p d W (fun a => a.natDegree ≤ Ds)
      (by simp) (by simp) (fun a ha => by simpa only [Polynomial.natDegree_neg] using ha) hp)
  rw [block_det] at h
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, card_block] using h

lemma inner_degree (p : Fin n → MvPolynomial (Fin n) Coefficient)
    (d : Fin n → ℕ) (W Dt : ℕ)
    (hp : ∀ i e j, (((p i).coeff e).coeff j).natDegree ≤ Dt) (j : ℕ) :
    ((polynomial p d W).coeff j).natDegree ≤ (n + 2) * FixedWidthPolynomial.count n W * Dt := by
  have h := PolynomialKronecker.determinant_inner_degree
    (block (MacaulayFullBox.matrix p d W)) (fun _ => Dt)
    (fun a b k => block_entry_property p d W (fun a => (a.coeff k).natDegree ≤ Dt)
      (by simp) (by simp only [Polynomial.coeff_one]; split_ifs <;> simp)
      (fun a ha => by simpa only [Polynomial.coeff_neg, Polynomial.natDegree_neg] using ha)
      (fun i e => hp i e k) a b) j
  rw [block_det] at h
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, card_block] using h

end LeanCanny.Algebra.ProjectiveBoxGramEliminant
