/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RelativeProjectiveBoxGram

/-! # Actual relative value certificates on projective coordinate grids

The reciprocal test row and complete Macaulay Gram determinant are built
over oldAlgebra[t]. Reflection gives a value annihilator for every grid
root, including singular and repeated roots. Its selected-component
nonvanishing follows from one real sweep specialization with no points at
infinity. Both degree ceilings use only the relative box dimension.
-/

@[expose] public section
namespace LeanCanny.Algebra.RelativeProjectiveValueGram
open MvPolynomial
open scoped Classical BigOperators
variable {R : Type*} [CommRing R] {n : ℕ}

noncomputable def system (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial R)) (e : ℕ) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) (Polynomial (Polynomial R)) :=
  Fin.cases (C Polynomial.X * F.map Polynomial.C - X 0 ^ e) (fun i => (H i).map Polynomial.C)

def degrees (d : Fin n → ℕ) (e : ℕ) : Fin (n + 1) → ℕ := Fin.cases e d
def dimension (n W : ℕ) : ℕ := (n + 3) * FixedWidthPolynomial.count (n + 1) W

noncomputable def polynomial (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial R)) (d : Fin n → ℕ) (e W : ℕ) :=
  RelativeProjectiveBoxGram.polynomial (system H F e) (degrees d e) W

noncomputable def annihilator (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial R)) (d : Fin n → ℕ) (e W : ℕ) : Polynomial (Polynomial R) :=
  Polynomial.X * (polynomial H F d e W).reflect (dimension n W)

theorem homogeneous (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial R)) (d : Fin n → ℕ) (e : ℕ)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (hF : F.IsHomogeneous e) (j : Fin (n + 1)) :
    (system H F e j).IsHomogeneous (degrees d e j) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · exact ((hF.map Polynomial.C).C_mul Polynomial.X).sub (isHomogeneous_X_pow 0 e)
  · exact (hH i).map Polynomial.C

theorem coefficient_degree (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial R)) (e : ℕ)
    (j : Fin (n + 1)) (u : Fin (n + 1) →₀ ℕ) : ((system H F e j).coeff u).natDegree ≤ 1 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [system, Fin.cases_zero, coeff_sub, coeff_C_mul, coeff_map, coeff_X_pow]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply Polynomial.natDegree_mul_le.trans
      simpa only [Polynomial.natDegree_C, Nat.add_zero] using (Polynomial.natDegree_X_le : (Polynomial.X : Polynomial (Polynomial R)).natDegree ≤ 1)
    · split_ifs <;> simp
  · simp [system, coeff_map]

theorem degree_le (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial R)) (d : Fin n → ℕ) (e W : ℕ) :
    (polynomial H F d e W).natDegree ≤ dimension n W := by
  simpa only [polynomial, dimension, Nat.mul_one] using
    RelativeProjectiveBoxGram.outer_degree (system H F e) (degrees d e) W 1 (coefficient_degree H F e)

theorem root {K : Type*} [Field K]
    (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial R)) (d : Fin n → ℕ) (e W : ℕ)
    (hW : Macaulay.level (degrees d e) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (hF : F.IsHomogeneous e)
    (ρ : Polynomial R →+* K) (x : Fin (n + 1) → K) (hchart : x 0 = 1)
    (hx : ∀ i, (H i).eval₂ ρ x = 0) :
    (annihilator H F d e W).eval₂ ρ (F.eval₂ ρ x) = 0 := by
  by_cases HC : F.eval₂ ρ x = 0
  · simp [annihilator, HC]
  · have HP : (polynomial H F d e W).eval₂ ρ (F.eval₂ ρ x)⁻¹ = 0 := by
      apply RelativeProjectiveBoxGram.root _ _ W hW (homogeneous H F d e hH hF)
        (Polynomial.eval₂RingHom ρ (F.eval₂ ρ x)⁻¹) x
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp [system, hchart, HC, Polynomial.eval₂RingHom_comp_C]
        · simpa only [system, Fin.cases_succ, eval₂_map, Polynomial.eval₂RingHom_comp_C] using hx i
      · exact ⟨0, hchart.trans_ne one_ne_zero⟩
    let _ : Invertible (F.eval₂ ρ x)⁻¹ := invertibleOfNonzero (inv_ne_zero HC)
    have HR := (Polynomial.eval₂_reflect_eq_zero_iff ρ (F.eval₂ ρ x)⁻¹ (dimension n W)
      (polynomial H F d e W) (degree_le H F d e W)).mpr HP
    simp only [invOf_eq_inv, inv_inv] at HR
    simp only [annihilator, Polynomial.eval₂_mul, Polynomial.eval₂_X, HR, mul_zero]

theorem positive_constant (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial R)) (d : Fin n → ℕ) (e W : ℕ)
    (hW : Macaulay.level (degrees d e) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (hF : F.IsHomogeneous e)
    (hd : ∀ i, 0 < d i) (he : 0 < e) (ρ : Polynomial R →+* ℝ)
    (hinfinity : ∀ x : Fin (n + 1) → ℂ, x 0 = 0 →
      (∀ i, (H i).eval₂ (Complex.ofRealHom.comp ρ) x = 0) → x = 0) :
    0 < ρ ((polynomial H F d e W).coeff 0) := by
  have HP := RelativeProjectiveBoxGram.positive (system H F e) (degrees d e) W hW
    (homogeneous H F d e hH hF) (Fin.cases he hd) (Polynomial.eval₂RingHom ρ 0) (fun x hx => ?_)
  · simpa only [polynomial, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_at_zero] using HP
  · apply hinfinity x
    · have HZ := hx 0
      have HE : x 0 ^ e = 0 := by simpa [system] using HZ
      exact (pow_eq_zero_iff (Nat.ne_of_gt he)).mp HE
    · intro i
      simpa only [system, Fin.cases_succ, eval₂_map, RingHom.comp_assoc,
        Polynomial.eval₂RingHom_comp_C] using hx i.succ

theorem top_coefficient (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial R)) (d : Fin n → ℕ) (e W : ℕ) :
    (annihilator H F d e W).coeff (dimension n W + 1) = (polynomial H F d e W).coeff 0 := by
  rw [annihilator, Polynomial.coeff_X_mul, Polynomial.coeff_reflect, Polynomial.revAt_le (Nat.le_refl _), Nat.sub_self]

theorem selected_ne_zero (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial R)) (d : Fin n → ℕ) (e W : ℕ)
    (hW : Macaulay.level (degrees d e) < 2 ^ W)
    (hH : ∀ i, (H i).IsHomogeneous (d i)) (hF : F.IsHomogeneous e)
    (hd : ∀ i, 0 < d i) (he : 0 < e) (φ : R →+* ℝ) (t₀ : ℝ)
    (hinfinity : ∀ x : Fin (n + 1) → ℂ, x 0 = 0 →
      (∀ i, (H i).eval₂ (Complex.ofRealHom.comp (Polynomial.eval₂RingHom φ t₀)) x = 0) → x = 0) :
    (annihilator H F d e W).map (Polynomial.mapRingHom φ) ≠ 0 := by
  have HP := positive_constant H F d e W hW hH hF hd he (Polynomial.eval₂RingHom φ t₀) hinfinity
  intro HZ
  have HC := congrArg (fun q : Polynomial (Polynomial ℝ) => q.coeff (dimension n W + 1)) HZ
  rw [Polynomial.coeff_map, top_coefficient, Polynomial.coeff_zero] at HC
  have HE := congrArg (fun q : Polynomial ℝ => q.eval t₀) HC
  simp only [Polynomial.coe_mapRingHom, Polynomial.eval_map, Polynomial.eval_zero] at HE
  exact HP.ne' HE

theorem annihilator_degree (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial R)) (d : Fin n → ℕ) (e W : ℕ) :
    (annihilator H F d e W).natDegree ≤ dimension n W + 1 := by
  apply Polynomial.natDegree_mul_le.trans
  have H := (Polynomial.natDegree_reflect_le (p := polynomial H F d e W) (N := dimension n W)).trans
    (max_le le_rfl (degree_le H F d e W))
  exact (Nat.add_le_add Polynomial.natDegree_X_le H).trans_eq (Nat.add_comm 1 _)

theorem coefficient_inner_degree (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial R)) (e E : ℕ)
    (hH : ∀ i u, ((H i).coeff u).natDegree ≤ E) (hF : ∀ u, (F.coeff u).natDegree ≤ E)
    (j : Fin (n + 1)) (u : Fin (n + 1) →₀ ℕ) (k : ℕ) :
    (((system H F e j).coeff u).coeff k).natDegree ≤ E := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [system, Fin.cases_zero, coeff_sub, coeff_C_mul, coeff_map, coeff_X_pow, Polynomial.coeff_sub]
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

theorem annihilator_inner_degree (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial R)) (d : Fin n → ℕ) (e W E : ℕ)
    (hH : ∀ i u, ((H i).coeff u).natDegree ≤ E) (hF : ∀ u, (F.coeff u).natDegree ≤ E) (k : ℕ) :
    ((annihilator H F d e W).coeff k).natDegree ≤ dimension n W * E := by
  cases k with
  | zero => simp [annihilator]
  | succ k =>
    rw [annihilator, Polynomial.coeff_X_mul, Polynomial.coeff_reflect]
    simpa only [dimension, polynomial, Nat.add_assoc] using RelativeProjectiveBoxGram.inner_degree
      (system H F e) (degrees d e) W E (coefficient_inner_degree H F e E hH hF) _

end LeanCanny.Algebra.RelativeProjectiveValueGram
