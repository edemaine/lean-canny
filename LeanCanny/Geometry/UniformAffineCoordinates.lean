/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.AffineCoordinateEliminant

/-! # Bounded coordinate certificates and a uniform specialization factor

For a square integer polynomial family, the explicit Macaulay numerator gives
coordinate equations at every regular real root. The product of their leading
coefficients is a nonzero integer exceptional factor. Degrees, scalar
coefficient bits, and the factor's coefficient mass have explicit budgets.
This does not yet bound the separate factor ensuring root regularity.
-/

@[expose] public section

namespace LeanCanny.Geometry.UniformAffineCoordinates
open Polynomial
open LeanCanny.Algebra
open scoped BigOperators Classical

variable {n : ℕ}

def width (d : Fin n → ℕ) : ℕ := (Macaulay.level (AffineCoordinateSystem.degrees d)).size

def count (d : Fin n → ℕ) : ℕ := FixedWidthPolynomial.count (n + 1) (width d)

def bitBudget (d : Fin n → ℕ) (b : ℕ) : ℕ := (count d).size * count d + count d * (b + 3) + 1

theorem exists_bounded (q : Fin n → MvPolynomial (Fin n) (Polynomial ℤ)) (d : Fin n → ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ d j) (hd : ∀ j, 0 < d j) (E b : ℕ)
    (hdegree : ∀ j e, ((q j).coeff e).natDegree ≤ E)
    (hmass : ∀ j e, coefficientMass ((q j).coeff e) ≤ 2 ^ b) :
    ∃ P : Fin n → Polynomial (Polynomial ℤ), ∃ r : Polynomial ℤ,
      r ≠ 0 ∧ r.natDegree ≤ n * (count d * E) ∧
      coefficientMass r ≤ ((count d * E + 1) * 2 ^ bitBudget d b) ^ n ∧
      (∀ i, P i ≠ 0 ∧ (P i).natDegree ≤ count d ∧
        (∀ k, ((P i).coeff k).natDegree ≤ count d * E) ∧
        ∀ k l, (((P i).coeff k).coeff l).natAbs.size ≤ bitBudget d b) ∧
      ∀ t : ℝ, r.eval₂ (Int.castRingHom ℝ) t ≠ 0 →
        let φ := Polynomial.eval₂RingHom (Int.castRingHom ℝ) t
        (∀ i, (P i).map φ ≠ 0) ∧
        ∀ x : Fin n → ℝ, (∀ j, (q j).eval₂ φ x = 0) →
          (fderiv ℝ (fun y => fun j => (q j).eval₂ φ y) x).IsInvertible →
            ∀ i, ((P i).map φ).eval (x i) = 0 := by
  let P := fun i => AffineCoordinateEliminant.polynomial q d i (width d)
  have hP (i : Fin n) : P i ≠ 0 := AffineCoordinateEliminant.ne_zero q d i (width d)
  have hcoord (i : Fin n) : (P i).natDegree ≤ count d := AffineCoordinateEliminant.degree_le q d i (width d)
  have hparam (i : Fin n) (k : ℕ) : ((P i).coeff k).natDegree ≤ count d * E :=
    AffineCoordinateEliminant.parameter_degree_le q d i (width d) E hdegree k
  have hbits (i : Fin n) (k l : ℕ) : (((P i).coeff k).coeff l).natAbs.size ≤ bitBudget d b :=
    AffineCoordinateEliminant.parameter_coefficient_size_le q d i (width d) E b hdegree hmass k l
  let r := ∏ i, (P i).leadingCoeff
  have hr : r ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => Polynomial.leadingCoeff_ne_zero.mpr (hP i))
  have hleading (i : Fin n) : coefficientMass (P i).leadingCoeff ≤
      (count d * E + 1) * 2 ^ bitBudget d b := by
    apply coefficientMass_le _ _ _ (hparam i (P i).natDegree)
    intro k
    exact (Nat.lt_size_self _).le.trans
      (Nat.pow_le_pow_right (by decide) (hbits i (P i).natDegree k))
  refine ⟨P, r, hr, ?_, ?_, (fun i => ⟨hP i, hcoord i, hparam i, hbits i⟩), ?_⟩
  · exact (Polynomial.natDegree_prod_le _ _).trans (by
      have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hparam i (P i).natDegree)
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        Polynomial.coeff_natDegree] using h)
  · exact (coefficientMass_prod_le _ _).trans (by
      have h := Finset.prod_le_prod (fun i (_ : i ∈ Finset.univ) => hleading i)
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h)
  · intro t ht
    let φ := Polynomial.eval₂RingHom (Int.castRingHom ℝ) t
    have hnonzero (i : Fin n) : φ (P i).leadingCoeff ≠ 0 := by
      have he : ∏ i, φ (P i).leadingCoeff ≠ 0 := by
        change φ r ≠ 0 at ht
        simpa only [r, map_prod] using ht
      exact Finset.prod_ne_zero_iff.mp he i (Finset.mem_univ i)
    refine ⟨?_, ?_⟩
    · intro i hz
      have hc := congrArg (fun f : Polynomial ℝ => f.coeff (P i).natDegree) hz
      exact hnonzero i (by simpa only [Polynomial.coeff_map, Polynomial.coeff_natDegree,
        Polynomial.coeff_zero] using hc)
    · intro x hx hJac i
      rw [Polynomial.eval_map]
      exact AffineCoordinateEliminant.eval_eq_zero φ q d hD hd i (width d)
        (Nat.lt_size_self _) x hx hJac

end LeanCanny.Geometry.UniformAffineCoordinates
