/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveBoxGramEliminant

/-! # Explicit Gram annihilators of polynomial test values

A reciprocal row U * F - X₀^e evaluates a homogeneous polynomial test F on
the affine chart. Reflection yields a nonzero integer parameter polynomial
annihilating every original test value. Infinity exclusion is required only
at one real specialization. Original roots may be singular or repeated.
-/

@[expose] public section
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
namespace LeanCanny.Algebra.ProjectiveValueGram
abbrev Base := Polynomial ℤ
abbrev Coefficient := Polynomial Base
variable {n : ℕ}
noncomputable def system (H : Fin n → MvPolynomial (Fin (n + 1)) Base)
    (F : MvPolynomial (Fin (n + 1)) Base) (e : ℕ) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) Coefficient :=
  Fin.cases (C Polynomial.X * F.map Polynomial.C - X 0 ^ e) (fun i => (H i).map Polynomial.C)

def degrees (d : Fin n → ℕ) (e : ℕ) : Fin (n + 1) → ℕ := Fin.cases e d

def dimension (n W : ℕ) : ℕ := (n + 3) * FixedWidthPolynomial.count (n + 1) W

noncomputable def polynomial (H : Fin n → MvPolynomial (Fin (n + 1)) Base)
    (F : MvPolynomial (Fin (n + 1)) Base) (d : Fin n → ℕ) (e W : ℕ) : Coefficient :=
  ProjectiveBoxGramEliminant.polynomial (system H F e) (degrees d e) W

noncomputable def annihilator (H : Fin n → MvPolynomial (Fin (n + 1)) Base)
    (F : MvPolynomial (Fin (n + 1)) Base) (d : Fin n → ℕ) (e W : ℕ) : Coefficient :=
  Polynomial.X * (polynomial H F d e W).reflect (dimension n W)

lemma homogeneous (H : Fin n → MvPolynomial (Fin (n + 1)) Base)
    (F : MvPolynomial (Fin (n + 1)) Base) (d : Fin n → ℕ) (e : ℕ)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (hF : F.IsHomogeneous e) (j : Fin (n + 1)) :
    (system H F e j).IsHomogeneous (degrees d e j) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · exact ((hF.map Polynomial.C).C_mul Polynomial.X).sub (isHomogeneous_X_pow 0 e)
  · exact (hH i).map Polynomial.C

lemma coefficient_degree (H : Fin n → MvPolynomial (Fin (n + 1)) Base)
    (F : MvPolynomial (Fin (n + 1)) Base) (e : ℕ)
    (j : Fin (n + 1)) (u : Fin (n + 1) →₀ ℕ) :
    ((system H F e j).coeff u).natDegree ≤ 1 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [system, Fin.cases_zero, coeff_sub, coeff_C_mul, coeff_map, coeff_X_pow]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply Polynomial.natDegree_mul_le.trans
      simp
    · split_ifs <;> simp
  · simp [system, coeff_map]

lemma degree_le (H : Fin n → MvPolynomial (Fin (n + 1)) Base)
    (F : MvPolynomial (Fin (n + 1)) Base) (d : Fin n → ℕ) (e W : ℕ) :
    (polynomial H F d e W).natDegree ≤ dimension n W :=
  by
    simpa only [polynomial, dimension, Nat.mul_one] using
      ProjectiveBoxGramEliminant.outer_degree (system H F e) (degrees d e) W 1
        (coefficient_degree H F e)

lemma annihilator_eval {K : Type*} [Field K]
    (H : Fin n → MvPolynomial (Fin (n + 1)) Base)
    (F : MvPolynomial (Fin (n + 1)) Base) (d : Fin n → ℕ) (e W : ℕ)
    (hW : Macaulay.level (degrees d e) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (hF : F.IsHomogeneous e)
    (rho : Base →+* K) (x : Fin (n + 1) → K) (hchart : x 0 = 1)
    (hx : ∀ i, (H i).eval₂ rho x = 0) :
    (annihilator H F d e W).eval₂ rho (F.eval₂ rho x) = 0 := by
  by_cases hc : F.eval₂ rho x = 0
  · simp [annihilator, hc]
  · have hp : (polynomial H F d e W).eval₂ rho (F.eval₂ rho x)⁻¹ = 0 := by
      apply ProjectiveBoxGramEliminant.eval_eq_zero_of_common_root _ _ W hW
        (homogeneous H F d e hH hF) (Polynomial.eval₂RingHom rho (F.eval₂ rho x)⁻¹) x
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp [system, hchart, hc, Polynomial.eval₂RingHom_comp_C]
        · simpa only [system, Fin.cases_succ, eval₂_map, Polynomial.eval₂RingHom_comp_C] using hx i
      · exact ⟨0, hchart.trans_ne one_ne_zero⟩
    let : Invertible (F.eval₂ rho x)⁻¹ := invertibleOfNonzero (inv_ne_zero hc)
    have hr := (Polynomial.eval₂_reflect_eq_zero_iff rho (F.eval₂ rho x)⁻¹
      (dimension n W) (polynomial H F d e W) (degree_le H F d e W)).mpr hp
    simp only [invOf_eq_inv, inv_inv] at hr
    simp only [annihilator, Polynomial.eval₂_mul, Polynomial.eval₂_X, hr, mul_zero]

lemma ne_zero (H : Fin n → MvPolynomial (Fin (n + 1)) Base)
    (F : MvPolynomial (Fin (n + 1)) Base) (d : Fin n → ℕ) (e W : ℕ)
    (hW : Macaulay.level (degrees d e) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (hF : F.IsHomogeneous e)
    (hd : ∀ i, 0 < d i) (he : 0 < e) (rho : Base →+* ℝ)
    (hinfinity : ∀ x : Fin (n + 1) → ℂ, x 0 = 0 →
      (∀ i, (H i).eval₂ (Complex.ofRealHom.comp rho) x = 0) → x = 0) :
    polynomial H F d e W ≠ 0 := by
  apply ProjectiveBoxGramEliminant.ne_zero_of_real_specialization _ _ W hW
    (homogeneous H F d e hH hF) (Fin.cases he hd) (Polynomial.eval₂RingHom rho 0)
  intro x hx
  apply hinfinity x
  · have hz := hx 0
    have hp : x 0 ^ e = 0 := by simpa [system] using hz
    exact (pow_eq_zero_iff (Nat.ne_of_gt he)).mp hp
  · intro i
    simpa only [system, Fin.cases_succ, eval₂_map, RingHom.comp_assoc,
      Polynomial.eval₂RingHom_comp_C] using hx i.succ

lemma annihilator_ne_zero (H : Fin n → MvPolynomial (Fin (n + 1)) Base)
    (F : MvPolynomial (Fin (n + 1)) Base) (d : Fin n → ℕ) (e W : ℕ)
    (hW : Macaulay.level (degrees d e) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (hF : F.IsHomogeneous e)
    (hd : ∀ i, 0 < d i) (he : 0 < e) (rho : Base →+* ℝ)
    (hinfinity : ∀ x : Fin (n + 1) → ℂ, x 0 = 0 →
      (∀ i, (H i).eval₂ (Complex.ofRealHom.comp rho) x = 0) → x = 0) :
    annihilator H F d e W ≠ 0 :=
  mul_ne_zero Polynomial.X_ne_zero (Polynomial.reflect_eq_zero_iff.not.mpr
    (ne_zero H F d e W hW hH hF hd he rho hinfinity))

lemma annihilator_degree_le (H : Fin n → MvPolynomial (Fin (n + 1)) Base)
    (F : MvPolynomial (Fin (n + 1)) Base) (d : Fin n → ℕ) (e W : ℕ) :
    (annihilator H F d e W).natDegree ≤ dimension n W + 1 := by
  apply Polynomial.natDegree_mul_le.trans
  have hr := (Polynomial.natDegree_reflect_le (p := polynomial H F d e W) (N := dimension n W)).trans
    (max_le le_rfl (degree_le H F d e W))
  simpa only [Polynomial.natDegree_X, Nat.add_comm] using Nat.add_le_add_left hr 1

lemma coefficient_inner_degree (H : Fin n → MvPolynomial (Fin (n + 1)) Base)
    (F : MvPolynomial (Fin (n + 1)) Base) (e E : ℕ)
    (hH : ∀ i u, ((H i).coeff u).natDegree ≤ E) (hF : ∀ u, (F.coeff u).natDegree ≤ E)
    (j : Fin (n + 1)) (u : Fin (n + 1) →₀ ℕ) (k : ℕ) :
    (((system H F e j).coeff u).coeff k).natDegree ≤ E := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [system, Fin.cases_zero, coeff_sub, coeff_C_mul, coeff_map, coeff_X_pow,
      Polynomial.coeff_sub]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · cases k with
      | zero => simp
      | succ k =>
        rw [Polynomial.coeff_X_mul, Polynomial.coeff_C]
        split_ifs
        · exact hF u
        · simp
    · split_ifs
      · simp only [Polynomial.coeff_one]
        split_ifs <;> simp
      · simp
  · simp only [system, Fin.cases_succ, coeff_map, Polynomial.coeff_C]
    split_ifs
    · exact hH i u
    · simp

lemma annihilator_inner_degree (H : Fin n → MvPolynomial (Fin (n + 1)) Base)
    (F : MvPolynomial (Fin (n + 1)) Base) (d : Fin n → ℕ) (e W E : ℕ)
    (hH : ∀ i u, ((H i).coeff u).natDegree ≤ E) (hF : ∀ u, (F.coeff u).natDegree ≤ E)
    (k : ℕ) :
    ((annihilator H F d e W).coeff k).natDegree ≤ dimension n W * E := by
  cases k with
  | zero => simp [annihilator]
  | succ k =>
    rw [annihilator, Polynomial.coeff_X_mul, Polynomial.coeff_reflect]
    simpa only [dimension, polynomial, Nat.add_assoc] using ProjectiveBoxGramEliminant.inner_degree
      (system H F e) (degrees d e) W E (coefficient_inner_degree H F e E hH hF) _

lemma coefficient_nested_mass (H : Fin n → MvPolynomial (Fin (n + 1)) Base)
    (F : MvPolynomial (Fin (n + 1)) Base) (e M : ℕ)
    (hH : ∀ i u, coefficientMass ((H i).coeff u) ≤ M)
    (hF : ∀ u, coefficientMass (F.coeff u) ≤ M)
    (j : Fin (n + 1)) (u : Fin (n + 1) →₀ ℕ) :
    NestedMass.mass ((system H F e j).coeff u) ≤ M + 1 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [system, Fin.cases_zero, coeff_sub, coeff_C_mul, coeff_map, coeff_X_pow]
    have hX : NestedMass.mass (Polynomial.X : Coefficient) = 1 := by
      change NestedMass.mass (Polynomial.monomial 1 (Polynomial.C (1 : ℤ))) = 1
      rw [NestedMass.monomial, coefficientMass_C]
      rfl
    have h1 : NestedMass.mass (1 : Coefficient) = 1 := by
      change NestedMass.mass (Polynomial.C (Polynomial.C (1 : ℤ))) = 1
      rw [NestedMass.C, coefficientMass_C]
      rfl
    apply (NestedMass.sub_le _ _).trans
    apply Nat.add_le_add
    · apply (NestedMass.mul_le _ _).trans
      rw [hX, NestedMass.C, one_mul]
      exact hF u
    · split_ifs <;> simp [h1]
  · simpa only [system, Fin.cases_succ, coeff_map, NestedMass.C] using (hH i u).trans (Nat.le_succ M)

lemma reflection_nested_mass (p : Coefficient) (N : ℕ) :
    NestedMass.mass (p.reflect N) = NestedMass.mass p := by
  simp only [NestedMass.mass, Polynomial.sum_def, Polynomial.reflect_support]
  rw [Finset.sum_image]
  · simp only [Polynomial.coeff_reflect, Polynomial.revAt_invol]
  · intro a _ b _ he
    exact (Polynomial.revAt N).injective he

lemma annihilator_mass_le (H : Fin n → MvPolynomial (Fin (n + 1)) Base)
    (F : MvPolynomial (Fin (n + 1)) Base) (d : Fin n → ℕ) (e W M : ℕ)
    (hH : ∀ i u, coefficientMass ((H i).coeff u) ≤ M)
    (hF : ∀ u, coefficientMass (F.coeff u) ≤ M) :
    NestedMass.mass (annihilator H F d e W) ≤
      (FixedWidthPolynomial.count (n + 1) W).factorial *
        ((n + 2) * FixedWidthPolynomial.count (n + 1) W * (M + 1) ^ 2) ^
          FixedWidthPolynomial.count (n + 1) W := by
  have hX : NestedMass.mass (Polynomial.X : Coefficient) = 1 := by
    change NestedMass.mass (Polynomial.monomial 1 (Polynomial.C (1 : ℤ))) = 1
    rw [NestedMass.monomial, coefficientMass_C]
    rfl
  apply (NestedMass.mul_le _ _).trans
  rw [hX, one_mul, reflection_nested_mass]
  exact ProjectiveBoxGramEliminant.mass_le (system H F e) (degrees d e) W (M + 1)
    (Nat.le_add_left 1 M) (coefficient_nested_mass H F e M hH hF)

end LeanCanny.Algebra.ProjectiveValueGram
