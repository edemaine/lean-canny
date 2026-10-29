/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineRingCoordinates
public import LeanCanny.Algebra.PolynomialKronecker

/-! # Parameter-degree bounds for complete coordinate Gram certificates

The reciprocal variable and the external parameter remain separate. A uniform
external degree bound E on homogeneous-row coefficients gives dimension * E
as a bound on every external coefficient of the complete annihilator.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineRingGramEliminant
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {R : Type*} [CommRing R]

lemma system_coefficient_inner_degree
    (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R)) (E : ℕ)
    (hH : ∀ i e, ((H i).coeff e).natDegree ≤ E) (coordinate : Fin (n + 1))
    (j : Fin (n + 1)) (e : Fin (n + 1) →₀ ℕ) (k : ℕ) :
    (((system H coordinate j).coeff e).coeff k).natDegree ≤ E := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [system, Fin.cases_zero, coeff_sub, coeff_C_mul, coeff_X]
    split_ifs <;> simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_one] <;>
      split_ifs <;> simp
  · simp only [system, Fin.cases_succ, MvPolynomial.coeff_map, Polynomial.coeff_C]
    split_ifs
    · exact hH i e
    · simp

theorem polynomial_inner_degree
    (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (d : Fin n → ℕ) (W E : ℕ) (hH : ∀ i e, ((H i).coeff e).natDegree ≤ E)
    (coordinate : Fin (n + 1)) (k : ℕ) :
    ((polynomial H d W coordinate).coeff k).natDegree ≤ dimension n W * E := by
  have h := PolynomialKronecker.determinant_inner_degree
    (MacaulayFullBoxFinite.matrix (system H coordinate) (degrees d) W) (fun _ => E)
    (MacaulayFullBoxFinite.matrix_inner_degree _ _ W E
      (system_coefficient_inner_degree H E hH coordinate)) k
  rw [numeric_det] at h
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, dimension] using h

theorem annihilator_inner_degree
    (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (d : Fin n → ℕ) (W E : ℕ) (hH : ∀ i e, ((H i).coeff e).natDegree ≤ E)
    (coordinate : Fin (n + 1)) (k : ℕ) :
    ((annihilator H d W coordinate).coeff k).natDegree ≤ dimension n W * E := by
  cases k with
  | zero => simp [annihilator]
  | succ k =>
    rw [annihilator, Polynomial.coeff_X_mul, Polynomial.coeff_reflect]
    exact polynomial_inner_degree H d W E hH coordinate _

end LeanCanny.Algebra.AffineRingGramEliminant

namespace LeanCanny.Algebra.AffineRingCoordinates
open MvPolynomial WeightedHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {R : Type*} [CommRing R]

lemma homogeneous_coefficient_inner_degree
    (p : Fin n → MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ)
    (E : ℕ) (hp : ∀ i e, ((p i).coeff e).natDegree ≤ E)
    (i : Fin n) (e : Fin (n + 1) →₀ ℕ) :
    ((homogeneousRows p d i).coeff e).natDegree ≤ E := by
  by_cases hz : (homogeneousRows p d i).coeff e = 0
  · simp [hz]
  · obtain ⟨u, hu, _⟩ := coeff_rename_ne_zero (AffineFiniteCoordinates.layout n) _ e hz
    rw [homogeneousRows, ← hu, coeff_rename_mapDomain _ (AffineFiniteCoordinates.layout n).injective,
      WeightedHomogenization.coefficient]
    split_ifs
    · exact hp i u.some
    · simp

theorem annihilator_inner_degree
    (p : Fin n → MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ)
    (E : ℕ) (hp : ∀ i e, ((p i).coeff e).natDegree ≤ E) (coordinate : Fin n) (k : ℕ) :
    ((annihilator p d coordinate).coeff k).natDegree ≤ dimension d * E :=
  AffineRingGramEliminant.annihilator_inner_degree (homogeneousRows p d) d (width d) E
    (homogeneous_coefficient_inner_degree p d E hp) coordinate.succ k

end LeanCanny.Algebra.AffineRingCoordinates
