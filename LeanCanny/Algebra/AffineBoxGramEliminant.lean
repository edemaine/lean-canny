/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayFullBoxFinite
public import LeanCanny.Algebra.PrincipalParameterMass
public import Mathlib.Algebra.Polynomial.Reverse

/-! # Coordinate annihilators from exclusion of roots at infinity

Append the reciprocal coordinate row T Xᵢ - X₀ to homogeneous source rows.
At T = 0, exclusion at infinity makes the padded Macaulay matrix injective.
Its real Gram determinant is therefore nonzero. Every source root in the
X₀ = 1 chart kills this determinant at T = xᵢ⁻¹. Reflection, with an extra
factor X to retain zero coordinates, gives one integer annihilator for all
chart roots. No Jacobian condition or preliminary finiteness theorem is used.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineBoxGramEliminant
open MvPolynomial ProjectiveGramEliminant
open scoped Classical Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] Matrix.det MacaulayFullBox.matrix

variable {n : ℕ}

noncomputable def system (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (coordinate : Fin (n + 1)) : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (Polynomial ℤ) :=
  Fin.cases (C Polynomial.X * X coordinate - X 0) (fun i => (H i).map Polynomial.C)

def degrees (d : Fin n → ℕ) : Fin (n + 1) → ℕ := Fin.cases 1 d

def dimension (n W : ℕ) : ℕ := (n + 3) * FixedWidthPolynomial.count (n + 1) W

noncomputable def polynomial (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) : Polynomial ℤ :=
  (gram (MacaulayFullBox.matrix (system H coordinate) (degrees d) W)).det

noncomputable def annihilator (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) : Polynomial ℤ :=
  Polynomial.X * (polynomial H d W coordinate).reflect (dimension n W)

lemma homogeneous (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ) (d : Fin n → ℕ)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (coordinate : Fin (n + 1)) (j : Fin (n + 1)) :
    (system H coordinate j).IsHomogeneous (degrees d j) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · exact ((isHomogeneous_X _ coordinate).C_mul Polynomial.X).sub (isHomogeneous_X _ 0)
  · exact (hH i).map Polynomial.C

lemma eval_polynomial {K : Type*} [CommRing K]
    (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ) (d : Fin n → ℕ) (W : ℕ)
    (coordinate : Fin (n + 1)) (phi : Polynomial ℤ →+* K) :
    phi (polynomial H d W coordinate) =
      (gram (MacaulayFullBox.matrix (fun j => (system H coordinate j).map phi) (degrees d) W)).det := by
  rw [polynomial, RingHom.map_det]
  change ((gram (MacaulayFullBox.matrix (system H coordinate) (degrees d) W)).map phi).det = _
  rw [gram_map, MacaulayFullBox.matrix_map]

/-- The reciprocal determinant vanishes at every nonzero common projective root. -/
theorem eval_eq_zero_of_common_root {K : Type*} [Field K]
    (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ) (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level (degrees d) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (coordinate : Fin (n + 1))
    (phi : Polynomial ℤ →+* K) (x : Fin (n + 1) → K)
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

/-- Exclusion only on the hyperplane X₀ = 0 makes the zero-parameter real
specialization positive, even when the finite chart has singular roots. -/
theorem eval_zero_pos (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level (degrees d) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hinfinity : ∀ x : Fin (n + 1) → ℂ, x 0 = 0 →
      (∀ i, (H i).eval₂ (Int.castRingHom ℂ) x = 0) → x = 0)
    (coordinate : Fin (n + 1)) :
    (polynomial H d W coordinate).eval₂ (Int.castRingHom ℝ) 0 > 0 := by
  let phi := Polynomial.eval₂RingHom (Int.castRingHom ℝ) 0
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
      have he : (Complex.ofRealHom.comp phi).comp Polynomial.C = Int.castRingHom ℂ := Subsingleton.elim _ _
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

theorem ne_zero (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level (degrees d) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hinfinity : ∀ x : Fin (n + 1) → ℂ, x 0 = 0 →
      (∀ i, (H i).eval₂ (Int.castRingHom ℂ) x = 0) → x = 0)
    (coordinate : Fin (n + 1)) : polynomial H d W coordinate ≠ 0 := by
  intro h
  have hp := eval_zero_pos H d W hW hH hd hinfinity coordinate
  rw [h, Polynomial.eval₂_zero] at hp
  exact (lt_irrefl 0) hp

lemma system_coefficient_degree (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (coordinate : Fin (n + 1)) (j : Fin (n + 1)) (e : Fin (n + 1) →₀ ℕ) :
    ((system H coordinate j).coeff e).natDegree ≤ 1 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [system, Fin.cases_zero, coeff_sub, coeff_C_mul, coeff_X]
    split_ifs <;> simp
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  · simp [system, MvPolynomial.coeff_map]

lemma numeric_det (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) :
    (MacaulayFullBoxFinite.matrix (system H coordinate) (degrees d) W).det =
      polynomial H d W coordinate := by
  rw [MacaulayFullBoxFinite.matrix, Matrix.det_submatrix_equiv_self, ProjectiveGramEliminant.block_det]
  rfl

/-- A fixed degree bound, with no dependence on a chosen minor or actual rank. -/
theorem degree_le (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) :
    (polynomial H d W coordinate).natDegree ≤ dimension n W := by
  have h := det_natDegree_le (MacaulayFullBoxFinite.matrix (system H coordinate) (degrees d) W)
    (fun _ => 1) (MacaulayFullBoxFinite.matrix_entry_property _ _ _ (fun a : Polynomial ℤ => a.natDegree ≤ 1)
      (by simp) (by simp) (fun a ha => by simpa only [Polynomial.natDegree_neg] using ha)
      (system_coefficient_degree H coordinate))
  rw [numeric_det] at h
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, dimension] using h

theorem annihilator_ne_zero (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level (degrees d) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hinfinity : ∀ x : Fin (n + 1) → ℂ, x 0 = 0 →
      (∀ i, (H i).eval₂ (Int.castRingHom ℂ) x = 0) → x = 0)
    (coordinate : Fin (n + 1)) : annihilator H d W coordinate ≠ 0 :=
  mul_ne_zero Polynomial.X_ne_zero (Polynomial.reflect_eq_zero_iff.not.mpr
    (ne_zero H d W hW hH hd hinfinity coordinate))

theorem annihilator_degree_le (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) :
    (annihilator H d W coordinate).natDegree ≤ dimension n W + 1 := by
  apply (Polynomial.natDegree_mul_le).trans
  have hr := (Polynomial.natDegree_reflect_le (p := polynomial H d W coordinate) (N := dimension n W)).trans
    (max_le le_rfl (degree_le H d W coordinate))
  simpa only [Polynomial.natDegree_X, Nat.add_comm] using Nat.add_le_add_left hr 1

/-- Every finite-chart coordinate is retained, including zero coordinates and
coordinates of singular or multiple roots. -/
theorem annihilator_eval_eq_zero {K : Type*} [Field K]
    (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ) (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level (degrees d) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (coordinate : Fin (n + 1))
    (x : Fin (n + 1) → K) (hchart : x 0 = 1)
    (hx : ∀ i, (H i).eval₂ (Int.castRingHom K) x = 0) :
    (annihilator H d W coordinate).eval₂ (Int.castRingHom K) (x coordinate) = 0 := by
  by_cases hc : x coordinate = 0
  · simp [annihilator, hc]
  · have hp : (polynomial H d W coordinate).eval₂ (Int.castRingHom K) (x coordinate)⁻¹ = 0 := by
      apply eval_eq_zero_of_common_root H d W hW hH coordinate
        (Polynomial.eval₂RingHom (Int.castRingHom K) (x coordinate)⁻¹) x
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp [system, hchart, hc]
        · have he : (Polynomial.eval₂RingHom (Int.castRingHom K) (x coordinate)⁻¹).comp Polynomial.C =
              Int.castRingHom K := Subsingleton.elim _ _
          simpa only [system, Fin.cases_succ, MvPolynomial.eval₂_map, he] using hx i
      · exact ⟨0, hchart.trans_ne one_ne_zero⟩
    let : Invertible (x coordinate)⁻¹ := invertibleOfNonzero (inv_ne_zero hc)
    have hr := (Polynomial.eval₂_reflect_eq_zero_iff (Int.castRingHom K) (x coordinate)⁻¹
      (dimension n W) (polynomial H d W coordinate) (degree_le H d W coordinate)).mpr hp
    simp only [invOf_eq_inv, inv_inv] at hr
    simp only [annihilator, Polynomial.eval₂_mul, Polynomial.eval₂_X, hr, mul_zero]

/-- Exclusion at infinity implies finiteness over every characteristic-zero
field. The certificate annihilates the complete chart, not only regular roots. -/
theorem finite_chart {K : Type*} [Field K] [CharZero K]
    (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ) (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level (degrees d) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hinfinity : ∀ x : Fin (n + 1) → ℂ, x 0 = 0 →
      (∀ i, (H i).eval₂ (Int.castRingHom ℂ) x = 0) → x = 0) :
    {x : Fin (n + 1) → K | x 0 = 1 ∧ ∀ i, (H i).eval₂ (Int.castRingHom K) x = 0}.Finite := by
  have hn (i : Fin (n + 1)) : ((annihilator H d W i).map (Int.castRingHom K)) ≠ 0 :=
    fun hz => (annihilator_ne_zero H d W hW hH hd hinfinity i)
      (Polynomial.map_injective (Int.castRingHom K) Int.cast_injective (hz.trans (by simp)))
  apply (Set.Finite.pi' (fun i => Polynomial.finite_setOfPred_isRoot (hn i))).subset
  intro x hx i
  change Polynomial.eval (x i) ((annihilator H d W i).map (Int.castRingHom K)) = 0
  rw [Polynomial.eval_map]
  exact annihilator_eval_eq_zero H d W hW hH i x hx.1 hx.2

lemma system_coefficient_mass (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (M : ℕ) (hM : 2 ≤ M) (hH : ∀ i e, ((H i).coeff e).natAbs ≤ M)
    (coordinate : Fin (n + 1)) (j : Fin (n + 1)) (e : Fin (n + 1) →₀ ℕ) :
    coefficientMass ((system H coordinate j).coeff e) ≤ M := by
  refine Fin.cases ?_ (fun i => ?_) j
  · have hx : coefficientMass (Polynomial.X : Polynomial ℤ) = 1 := by
      simp [coefficientMass, Polynomial.sum_X_index]
    apply (coefficientMass_sub_le _ _).trans
    apply (Nat.add_le_add (show coefficientMass ((C Polynomial.X * X coordinate : MvPolynomial (Fin (n + 1)) (Polynomial ℤ)).coeff e) ≤ 1 from ?_)
      (show coefficientMass ((X 0 : MvPolynomial (Fin (n + 1)) (Polynomial ℤ)).coeff e) ≤ 1 from ?_)).trans hM
    · simp only [coeff_C_mul, coeff_X]
      split_ifs <;> simp [hx]
    · simp only [coeff_X]
      split_ifs
      · change coefficientMass (Polynomial.C (1 : ℤ)) ≤ 1
        rw [coefficientMass_C]
        decide
      · simp
  · simpa only [system, Fin.cases_succ, MvPolynomial.coeff_map, coefficientMass_C] using hH i e

/-- Integer coefficient mass is controlled by the fixed block dimension. -/
theorem mass_le (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (d : Fin n → ℕ) (W M : ℕ) (hM : 2 ≤ M)
    (hH : ∀ i e, ((H i).coeff e).natAbs ≤ M) (coordinate : Fin (n + 1)) :
    coefficientMass (polynomial H d W coordinate) ≤ (dimension n W).factorial * M ^ dimension n W := by
  have hm := MacaulayFullBoxFinite.matrix_entry_property (system H coordinate) (degrees d) W
    (fun a : Polynomial ℤ => coefficientMass a ≤ M)
    (by simp) (by simpa only [show (1 : Polynomial ℤ) = Polynomial.C 1 from rfl, coefficientMass_C,
      Int.natAbs_one] using (show 1 ≤ M by omega))
    (fun a ha => by simpa only [coefficientMass_neg] using ha)
    (system_coefficient_mass H M hM hH coordinate)
  have h := det_coefficientMass_le (MacaulayFullBoxFinite.matrix (system H coordinate) (degrees d) W)
    (fun _ => M) hm
  rw [numeric_det] at h
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, dimension] using h

lemma reflection_mass (p : Polynomial ℤ) (N : ℕ) : coefficientMass (p.reflect N) = coefficientMass p := by
  simp only [coefficientMass, Polynomial.sum_def, Polynomial.reflect_support]
  rw [Finset.sum_image]
  · simp only [Polynomial.coeff_reflect, Polynomial.revAt_invol]
  · intro a _ b _ he
    exact (Polynomial.revAt N).injective he

theorem annihilator_mass_le (H : Fin n → MvPolynomial (Fin (n + 1)) ℤ)
    (d : Fin n → ℕ) (W M : ℕ) (hM : 2 ≤ M)
    (hH : ∀ i e, ((H i).coeff e).natAbs ≤ M) (coordinate : Fin (n + 1)) :
    coefficientMass (annihilator H d W coordinate) ≤ (dimension n W).factorial * M ^ dimension n W := by
  have hx : coefficientMass (Polynomial.X : Polynomial ℤ) = 1 := by
    simp [coefficientMass, Polynomial.sum_X_index]
  apply (coefficientMass_mul_le _ _).trans
  rw [hx, one_mul, reflection_mass]
  exact mass_le H d W M hM hH coordinate

end LeanCanny.Algebra.AffineBoxGramEliminant
