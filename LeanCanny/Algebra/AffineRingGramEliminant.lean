/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineBoxGramEliminant

/-! # Reciprocal coordinate Gram polynomials over coefficient rings

The complete coordinate annihilator is defined over any commutative ring,
including polynomial parameter rings. Evaluation retains every chart root,
with no regularity assumption on that root.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineRingGramEliminant
open MvPolynomial ProjectiveGramEliminant
open scoped Classical Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] Matrix.det MacaulayFullBox.matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def system (H : Fin n → MvPolynomial (Fin (n + 1)) R)
    (coordinate : Fin (n + 1)) : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (Polynomial R) :=
  Fin.cases (C Polynomial.X * X coordinate - X 0) (fun i => (H i).map Polynomial.C)

def degrees (d : Fin n → ℕ) : Fin (n + 1) → ℕ := Fin.cases 1 d

def dimension (n W : ℕ) : ℕ := (n + 3) * FixedWidthPolynomial.count (n + 1) W

noncomputable def polynomial (H : Fin n → MvPolynomial (Fin (n + 1)) R)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) : Polynomial R :=
  (gram (MacaulayFullBox.matrix (system H coordinate) (degrees d) W)).det

noncomputable def annihilator (H : Fin n → MvPolynomial (Fin (n + 1)) R)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) : Polynomial R :=
  Polynomial.X * (polynomial H d W coordinate).reflect (dimension n W)

lemma homogeneous (H : Fin n → MvPolynomial (Fin (n + 1)) R) (d : Fin n → ℕ)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (coordinate : Fin (n + 1)) (j : Fin (n + 1)) :
    (system H coordinate j).IsHomogeneous (degrees d j) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · exact ((isHomogeneous_X _ coordinate).C_mul Polynomial.X).sub (isHomogeneous_X _ 0)
  · exact (hH i).map Polynomial.C

lemma eval_polynomial {K : Type*} [CommRing K]
    (H : Fin n → MvPolynomial (Fin (n + 1)) R) (d : Fin n → ℕ) (W : ℕ)
    (coordinate : Fin (n + 1)) (phi : Polynomial R →+* K) :
    phi (polynomial H d W coordinate) =
      (gram (MacaulayFullBox.matrix (fun j => (system H coordinate j).map phi) (degrees d) W)).det := by
  rw [polynomial, RingHom.map_det]
  change ((gram (MacaulayFullBox.matrix (system H coordinate) (degrees d) W)).map phi).det = _
  rw [gram_map, MacaulayFullBox.matrix_map]

/-- The reciprocal determinant vanishes at every nonzero common projective root. -/
theorem eval_eq_zero_of_common_root {K : Type*} [Field K]
    (H : Fin n → MvPolynomial (Fin (n + 1)) R) (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level (degrees d) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (coordinate : Fin (n + 1))
    (phi : Polynomial R →+* K) (x : Fin (n + 1) → K)
    (hx : ∀ j, (system H coordinate j).eval₂ phi x = 0) (hnz : ∃ j, x j ≠ 0) :
    phi (polynomial H d W coordinate) = 0 := by
  by_contra h
  rw [eval_polynomial] at h
  let p := fun j => (system H coordinate j).map phi
  let A := MacaulayFullBox.matrix p (degrees d) W
  have hz : A *ᵥ Macaulay.evaluationVector (degrees d) W x = 0 := by
    apply MacaulayFullBox.mulVec_evaluation_eq_zero _ _ W
      (fun j => (homogeneous H d hH coordinate j).map phi) hW x
    intro j
    simpa only [p, MvPolynomial.eval_map] using hx j
  have hi := Matrix.mulVec_injective_of_det_ne_zero h
  have hv : gram A *ᵥ Macaulay.evaluationVector (degrees d) W x = 0 := by
    rw [gram, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  have he := hi (hv.trans (Matrix.mulVec_zero _).symm)
  obtain ⟨j, hj⟩ := hnz
  obtain ⟨r, hr⟩ := Macaulay.evaluationVector_ne_zero (degrees d) W hW x j hj
  exact hr (congrFun he r)

lemma system_coefficient_degree (H : Fin n → MvPolynomial (Fin (n + 1)) R)
    (coordinate : Fin (n + 1)) (j : Fin (n + 1)) (e : Fin (n + 1) →₀ ℕ) :
    ((system H coordinate j).coeff e).natDegree ≤ 1 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [system, Fin.cases_zero, coeff_sub, coeff_C_mul, coeff_X]
    split_ifs <;> simp [Polynomial.natDegree_X_le]
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp [Polynomial.natDegree_X_le])
  · simp [system, MvPolynomial.coeff_map]

lemma numeric_det (H : Fin n → MvPolynomial (Fin (n + 1)) R)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) :
    (MacaulayFullBoxFinite.matrix (system H coordinate) (degrees d) W).det =
      polynomial H d W coordinate := by
  rw [MacaulayFullBoxFinite.matrix, Matrix.det_submatrix_equiv_self, ProjectiveGramEliminant.block_det]
  rfl

/-- A fixed degree bound, with no dependence on a chosen minor or actual rank. -/
theorem degree_le (H : Fin n → MvPolynomial (Fin (n + 1)) R)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) :
    (polynomial H d W coordinate).natDegree ≤ dimension n W := by
  have h := det_natDegree_le (MacaulayFullBoxFinite.matrix (system H coordinate) (degrees d) W)
    (fun _ => 1) (MacaulayFullBoxFinite.matrix_entry_property _ _ _ (fun a : Polynomial R => a.natDegree ≤ 1)
      (by simp) (by simp) (fun a ha => by simpa only [Polynomial.natDegree_neg] using ha)
      (system_coefficient_degree H coordinate))
  rw [numeric_det] at h
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, dimension] using h

theorem annihilator_degree_le (H : Fin n → MvPolynomial (Fin (n + 1)) R)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) :
    (annihilator H d W coordinate).natDegree ≤ dimension n W + 1 := by
  apply (Polynomial.natDegree_mul_le).trans
  have hr := (Polynomial.natDegree_reflect_le (p := polynomial H d W coordinate) (N := dimension n W)).trans
    (max_le le_rfl (degree_le H d W coordinate))
  simpa only [Nat.add_comm] using Nat.add_le_add Polynomial.natDegree_X_le hr

/-- Every finite-chart coordinate is retained, including zero coordinates and
coordinates of singular or multiple roots. -/
theorem annihilator_eval_eq_zero {K : Type*} [Field K]
    (rho : R →+* K) (H : Fin n → MvPolynomial (Fin (n + 1)) R) (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level (degrees d) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (coordinate : Fin (n + 1))
    (x : Fin (n + 1) → K) (hchart : x 0 = 1)
    (hx : ∀ i, (H i).eval₂ rho x = 0) :
    (annihilator H d W coordinate).eval₂ rho (x coordinate) = 0 := by
  by_cases hc : x coordinate = 0
  · simp [annihilator, hc]
  · have hp : (polynomial H d W coordinate).eval₂ rho (x coordinate)⁻¹ = 0 := by
      apply eval_eq_zero_of_common_root H d W hW hH coordinate
        (Polynomial.eval₂RingHom rho (x coordinate)⁻¹) x
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp [system, hchart, hc]
        · have he : (Polynomial.eval₂RingHom rho (x coordinate)⁻¹).comp Polynomial.C =
              rho := Polynomial.eval₂RingHom_comp_C _ _
          simpa only [system, Fin.cases_succ, MvPolynomial.eval₂_map, he] using hx i
      · exact ⟨0, hchart.trans_ne one_ne_zero⟩
    let : Invertible (x coordinate)⁻¹ := invertibleOfNonzero (inv_ne_zero hc)
    have hr := (Polynomial.eval₂_reflect_eq_zero_iff rho (x coordinate)⁻¹
      (dimension n W) (polynomial H d W coordinate) (degree_le H d W coordinate)).mpr hp
    simp only [invOf_eq_inv, inv_inv] at hr
    simp only [annihilator, Polynomial.eval₂_mul, Polynomial.eval₂_X, hr, mul_zero]


/-- Exclusion only on the hyperplane X₀ = 0 makes the zero-parameter real
specialization positive, even when the finite chart has singular roots. -/
theorem eval_zero_pos (rho : R →+* ℝ) (H : Fin n → MvPolynomial (Fin (n + 1)) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level (degrees d) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hinfinity : ∀ x : Fin (n + 1) → ℂ, x 0 = 0 →
      (∀ i, (H i).eval₂ (Complex.ofRealHom.comp rho) x = 0) → x = 0)
    (coordinate : Fin (n + 1)) :
    (polynomial H d W coordinate).eval₂ rho 0 > 0 := by
  let phi := Polynomial.eval₂RingHom rho 0
  let pr := fun j => (system H coordinate j).map phi
  let pc := fun j => (pr j).map Complex.ofRealHom
  have hs : Function.Surjective (Macaulay.fullMatrix pc (degrees d) W).vecMul := by
    apply Macaulay.fullMatrix_surjective_of_no_nonzero_root _ _ W
      (fun j => ((homogeneous H d hH coordinate j).map phi).map Complex.ofRealHom)
      (Fin.cases (by change 0 < 1; decide) hd) hW
    intro x hx
    apply hinfinity x
    · have hz := hx 0
      simpa [pc, pr, system, phi, MvPolynomial.eval_map] using hz
    · intro i
      have hz := hx i.succ
      have he : (Complex.ofRealHom.comp phi).comp Polynomial.C = Complex.ofRealHom.comp rho := by
        rw [RingHom.comp_assoc, Polynomial.eval₂RingHom_comp_C]
      simpa only [pc, pr, system, Fin.cases_succ, MvPolynomial.eval_map, MvPolynomial.eval₂_map, he] using hz
  have hc := MacaulayFullBox.mulVec_injective_of_fullMatrix_surjective pc (degrees d) W
    (fun j => ((homogeneous H d hH coordinate j).map phi).map Complex.ofRealHom) hs
  have hr : Function.Injective (MacaulayFullBox.matrix pr (degrees d) W).mulVec := by
    intro x y hxy
    have he : Complex.ofRealHom ∘ x = Complex.ofRealHom ∘ y := by
      apply hc
      funext a
      have he := congrArg Complex.ofRealHom (congrFun hxy a)
      simpa only [RingHom.map_mulVec, MacaulayFullBox.matrix_map] using he
    funext i
    exact Complex.ofReal_injective (congrFun he i)
  have hpos := (Matrix.PosDef.conjTranspose_mul_self (MacaulayFullBox.matrix pr (degrees d) W) hr).det_pos
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hpos
  change phi (polynomial H d W coordinate) > 0
  rw [eval_polynomial]
  exact hpos


lemma coefficient_top (H : Fin n → MvPolynomial (Fin (n + 1)) R)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) :
    (annihilator H d W coordinate).coeff (dimension n W + 1) =
      (polynomial H d W coordinate).coeff 0 := by
  rw [annihilator, Polynomial.coeff_X_mul, Polynomial.coeff_reflect,
    Polynomial.revAt_le le_rfl, Nat.sub_self]

/-- The degree is fixed before specialization, and its leading coefficient
stays positive under every real specialization satisfying infinity exclusion. -/
theorem exact_degree_and_positive_leading (rho : R →+* ℝ)
    (H : Fin n → MvPolynomial (Fin (n + 1)) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level (degrees d) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hinfinity : ∀ x : Fin (n + 1) → ℂ, x 0 = 0 →
      (∀ i, (H i).eval₂ (Complex.ofRealHom.comp rho) x = 0) → x = 0)
    (coordinate : Fin (n + 1)) :
    (annihilator H d W coordinate).natDegree = dimension n W + 1 ∧
      0 < rho (annihilator H d W coordinate).leadingCoeff := by
  have hz := eval_zero_pos rho H d W hW hH hd hinfinity coordinate
  rw [Polynomial.eval₂_at_zero] at hz
  have hc : (annihilator H d W coordinate).coeff (dimension n W + 1) ≠ 0 := by
    rw [coefficient_top]
    intro he
    rw [he, map_zero] at hz
    exact (lt_irrefl 0) hz
  have hdeg := Nat.le_antisymm (annihilator_degree_le H d W coordinate)
    (Polynomial.le_natDegree_of_ne_zero hc)
  refine ⟨hdeg, ?_⟩
  rw [Polynomial.leadingCoeff, hdeg, coefficient_top]
  exact hz

/-- The ring-generic construction agrees definitionally with the original
integer certificate, preserving its coefficient-reader interface. -/
lemma integer_annihilator_eq (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) :
    annihilator H d W coordinate = AffineBoxGramEliminant.annihilator H d W coordinate := rfl

end LeanCanny.Algebra.AffineRingGramEliminant
