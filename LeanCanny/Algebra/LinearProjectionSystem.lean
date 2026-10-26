/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineCoordinateSystem

/-! # Homogeneous systems retaining an integer linear projection

The extra row is u X₀ minus the weighted spatial coordinates. The original
square system is homogenized without changing its spatial variables.
-/

@[expose] public section
namespace LeanCanny.Algebra.LinearProjectionSystem
open MvPolynomial AffineCoordinateSystem
open scoped Classical BigOperators

variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def nativeRow (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (v : Fin n → R) : Option (Fin n) → MvPolynomial (Option (Fin n)) (Polynomial R)
  | none => C Polynomial.X * X none - ∑ i, C (Polynomial.C (v i)) * X (some i)
  | some j => WeightedHomogenization.homogenize (fun _ => 1) (d j) ((q j).map Polynomial.C)

noncomputable def rows (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (v : Fin n → R) : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (Polynomial R) :=
  Fin.cons (rename layout (nativeRow q d v none))
    (fun j => rename layout (nativeRow q d v (some j)))

theorem eval_rows {S : Type*} [CommRing S] (φ : R →+* S)
    (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ d j) (v : Fin n → R) (u : S) (x : Fin n → S) :
    (fun j => (rows q d v j).eval₂ (Polynomial.eval₂RingHom φ u)
      (fun k => (layout.symm k).elim 1 x)) =
      Fin.cons (u - ∑ i, φ (v i) * x i) (fun j => (q j).eval₂ φ x) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [rows, nativeRow, eval₂_sum]
  · simp only [rows, Fin.cons_succ, eval₂_rename, Function.comp_def,
      Equiv.symm_apply_apply, nativeRow]
    rw [WeightedHomogenization.eval_chart]
    · simp [eval₂_map]
    · intro e he
      exact (WeightedHomogenization.weight_le_degree _ (by simp) e).trans
        ((MvPolynomial.le_totalDegree he).trans ((PolynomialMapDegree.degree_le Polynomial.C (q j)).trans (hD j)))

theorem homogeneous (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (v : Fin n → R) (j : Fin (n + 1)) :
    (rows q d v j).IsHomogeneous (degrees d j) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · apply IsHomogeneous.rename_isHomogeneous
    apply ((isHomogeneous_X (Polynomial R) none).C_mul Polynomial.X).sub
    exact IsHomogeneous.sum Finset.univ _ 1 (fun i _ => (isHomogeneous_X (Polynomial R) (some i)).C_mul (Polynomial.C (v i)))
  · have hw : WeightedHomogenization.weights (fun _ : Fin n => 1) = 1 := by
      funext i
      cases i <;> rfl
    have h := WeightedHomogenization.homogeneous (fun _ : Fin n => 1) (d j) ((q j).map Polynomial.C)
    exact (show (nativeRow q d v (some j)).IsHomogeneous (d j) by
      simpa only [nativeRow, MvPolynomial.IsHomogeneous, hw] using h).rename_isHomogeneous

theorem coefficient_degree (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (v : Fin n → R) (j : Fin (n + 1)) (e : Fin (n + 1) →₀ ℕ) :
    ((rows q d v j).coeff e).natDegree ≤ 1 := by
  have hn (j : Option (Fin n)) (e : Option (Fin n) →₀ ℕ) :
      ((nativeRow q d v j).coeff e).natDegree ≤ 1 := by
    cases j with
    | none =>
      rw [nativeRow, coeff_sub, coeff_sum, C_mul_X_eq_monomial, coeff_monomial]
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · split_ifs
        · exact Polynomial.natDegree_X_le
        · simp
      · apply Polynomial.natDegree_sum_le_of_forall_le
        intro i _
        rw [C_mul_X_eq_monomial, coeff_monomial]
        split_ifs <;> simp
    | some j =>
      rw [nativeRow, WeightedHomogenization.coefficient]
      split_ifs <;> simp [MvPolynomial.coeff_map]
  refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [rows, Fin.cons_zero, Fin.cons_succ, rename_coefficient] <;> exact hn _ _

omit [CommRing R] in
theorem coefficient_mass (q : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (v : Fin n → ℤ) (b w : ℕ) (hq : ∀ j e, ((q j).coeff e).natAbs ≤ 2 ^ b)
    (hv : ∀ i, (v i).natAbs ≤ 2 ^ w) (j : Fin (n + 1)) (e : Fin (n + 1) →₀ ℕ) :
    coefficientMass ((rows q d v j).coeff e) ≤ 2 ^ b + 1 + n * 2 ^ w := by
  have hn (j : Option (Fin n)) (e : Option (Fin n) →₀ ℕ) :
      coefficientMass ((nativeRow q d v j).coeff e) ≤ 2 ^ b + 1 + n * 2 ^ w := by
    cases j with
    | none =>
      rw [nativeRow, coeff_sub, coeff_sum, C_mul_X_eq_monomial, coeff_monomial]
      have hX : coefficientMass (Polynomial.X : Polynomial ℤ) = 1 := by
        change coefficientMass (Polynomial.monomial 1 (1 : ℤ)) = 1
        rw [coefficientMass_monomial]
        rfl
      have hh : coefficientMass (if Finsupp.single none 1 = e then Polynomial.X else (0 : Polynomial ℤ)) ≤ 1 := by
        split_ifs <;> simp only [hX, coefficientMass_zero, le_refl, zero_le]
      have hs : coefficientMass (∑ i, (C (Polynomial.C (v i)) * X (some i)).coeff e) ≤ n * 2 ^ w := by
        apply (coefficientMass_sum_le _ _).trans
        calc
          ∑ i, coefficientMass ((C (Polynomial.C (v i)) * X (some i)).coeff e) ≤ ∑ _i : Fin n, 2 ^ w := by
            apply Finset.sum_le_sum
            intro i _
            rw [C_mul_X_eq_monomial, coeff_monomial]
            split_ifs
            · simpa only [coefficientMass_C] using hv i
            · simp
          _ = n * 2 ^ w := by simp
      calc
        _ ≤ 1 + n * 2 ^ w := (coefficientMass_sub_le _ _).trans (Nat.add_le_add hh hs)
        _ ≤ 2 ^ b + 1 + n * 2 ^ w := Nat.add_le_add_right (Nat.le_add_left 1 (2 ^ b)) _
    | some j =>
      rw [nativeRow, WeightedHomogenization.coefficient]
      split_ifs
      · rw [MvPolynomial.coeff_map, coefficientMass_C]
        exact (hq j _).trans (by omega)
      · simp
  refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [rows, Fin.cons_zero, Fin.cons_succ, rename_coefficient] <;> exact hn _ _

end LeanCanny.Algebra.LinearProjectionSystem
