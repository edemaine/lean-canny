/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PseudoRemainder
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring

/-! # Pseudo-remainder coefficients as scalar matrix-power moments

The matrix reads coefficients of the original head polynomial. Its dimension
is a degree bound plus one; a fixed even power applied to the original seed
coefficient vector produces the reduced, positively scaled seed.
-/

@[expose] public section

namespace LeanCanny.Algebra.PseudoRemainder
open Polynomial Matrix
open scoped BigOperators Classical

variable {R : Type*} [CommRing R]

theorem high_add (d : ℕ) (f g : R[X]) : high d (f + g) = high d f + high d g := by
  ext i
  simp only [high_coeff, coeff_add]

theorem high_C_mul (d : ℕ) (a : R) (g : R[X]) :
    high d (C a * g) = C a * high d g := by
  ext i
  simp only [high_coeff, coeff_C_mul]

theorem low_add (d : ℕ) (f g : R[X]) : low d (f + g) = low d f + low d g := by
  simp only [low, high_add]
  ring

theorem low_C_mul (d : ℕ) (a : R) (g : R[X]) :
    low d (C a * g) = C a * low d g := by
  simp only [low, high_C_mul]
  ring

theorem step_add (p f g : R[X]) (d : ℕ) :
    step p d (f + g) = step p d f + step p d g := by
  simp only [step, low_add, high_add]
  ring

theorem step_C_mul (p g : R[X]) (d : ℕ) (a : R) :
    step p d (C a * g) = C a * step p d g := by
  simp only [step, low_C_mul, high_C_mul]
  ring

noncomputable def stepLinear (p : R[X]) (d : ℕ) : R[X] →ₗ[R] R[X] where
  toFun := step p d
  map_add' f g := step_add p f g d
  map_smul' a g := by simpa only [smul_eq_C_mul, RingHom.id_apply] using step_C_mul p g d a

noncomputable def matrix (p : R[X]) (d D : ℕ) :
    Matrix (Fin (D + 1)) (Fin (D + 1)) R :=
  fun i j => (step p d (monomial j.val 1)).coeff i.val

/-- A matrix entry needs the head's bound coefficient and at most one shifted coefficient. -/
theorem matrix_apply (p : R[X]) (d D : ℕ) (hp : p.natDegree ≤ d)
    (i j : Fin (D + 1)) :
    matrix p d D i j =
      (if i = j then p.coeff d else 0) -
      (if d ≤ j.val ∧ j.val - d ≤ i.val then p.coeff (i.val - (j.val - d)) else 0) := by
  have hh : high d (monomial j.val (1 : R)) =
      if d ≤ j.val then monomial (j.val - d) 1 else 0 := by
    ext k
    rw [high_coeff]
    by_cases hj : d ≤ j.val
    · simp only [ite_eq_left hj, coeff_monomial]
      have he : j.val = k + d ↔ j.val - d = k := by omega
      simp only [he]
    · simp only [ite_eq_right hj, coeff_zero, coeff_monomial]
      rw [ite_eq_right (by omega)]
  rw [matrix, step_identity p d hp, coeff_sub, coeff_C_mul, hh]
  have he : j.val = i.val ↔ i = j :=
    ⟨fun h => Fin.ext h.symm, fun h => congrArg Fin.val h.symm⟩
  simp only [coeff_monomial, mul_ite, mul_one, mul_zero, he]
  by_cases hj : d ≤ j.val
  · simp only [hj, ↓reduceIte, monomial_one_right_eq_X_pow, coeff_mul_X_pow', true_and]
  · simp only [hj, ↓reduceIte, coeff_zero, false_and]

/-- Each entry is zero, one original coefficient, or its negation. -/
theorem matrix_apply_sparse (p : R[X]) (d D : ℕ) (hp : p.natDegree ≤ d)
    (i j : Fin (D + 1)) :
    matrix p d D i j =
      if i = j ∧ j.val < d then p.coeff d
      else if i.val < j.val ∧ d ≤ j.val ∧ j.val - d ≤ i.val then
        -p.coeff (i.val - (j.val - d)) else 0 := by
  rw [matrix_apply p d D hp]
  by_cases hij : i = j
  · subst i
    by_cases hj : d ≤ j.val
    · have hs : j.val - (j.val - d) = d := by omega
      simp [hj, hs, show ¬ j.val < d by omega]
    · simp [hj, show j.val < d by omega]
  · by_cases hlt : i.val < j.val
    · by_cases hc : d ≤ j.val ∧ j.val - d ≤ i.val <;>
        simp only [hij, hlt, hc, false_and, true_and, ↓reduceIte, zero_sub, neg_zero]
    · by_cases hc : d ≤ j.val ∧ j.val - d ≤ i.val
      · have hne : i.val ≠ j.val := by simpa only [Fin.ext_iff] using hij
        have hz : p.coeff (i.val - (j.val - d)) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by omega)
        simp [hij, hlt, hc, hz]
      · simp only [hij, hlt, hc, false_and, ↓reduceIte, sub_self]

theorem matrix_action (p : R[X]) (d D : ℕ) (v : Fin (D + 1) → R) :
    toFn (D + 1) (step p d (ofFn (D + 1) v)) = matrix p d D *ᵥ v := by
  classical
  funext i
  change (step p d (ofFn (D + 1) v)).coeff i.val = ∑ j, matrix p d D i j * v j
  rw [ofFn_eq_sum_monomial]
  change ((stepLinear p d) (∑ j, monomial j.val (v j))).coeff i.val = _
  rw [map_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  change (step p d (monomial j.val (v j))).coeff i.val = _
  rw [show monomial j.val (v j) = C (v j) * monomial j.val 1 by
      rw [monomial_one_right_eq_X_pow, C_mul_X_pow_eq_monomial],
    step_C_mul, coeff_C_mul]
  exact mul_comm _ _

theorem iterate_natDegree_le_bound (p g : R[X]) (d D n : ℕ) (hd : 0 < d)
    (hdD : d ≤ D) (hg : g.natDegree ≤ D) :
    ((step p d)^[n] g).natDegree ≤ D := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (step_natDegree_le p _ d (D - d) hd (by omega)).trans (by omega)

/-- The full reduction iterate is represented by one scalar matrix power. -/
theorem iterate_toFn (p g : R[X]) (d D n : ℕ) (hd : 0 < d)
    (hdD : d ≤ D) (hg : g.natDegree ≤ D) :
    toFn (D + 1) ((step p d)^[n] g) =
      matrix p d D ^ n *ᵥ toFn (D + 1) g := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    have hdeg : ((step p d)^[n] g).natDegree < D + 1 :=
      Nat.lt_succ_of_le (iterate_natDegree_le_bound p g d D n hd hdD hg)
    have hrepr : ofFn (D + 1) (toFn (D + 1) ((step p d)^[n] g)) = (step p d)^[n] g :=
      ofFn_comp_toFn_eq_id_of_natDegree_lt hdeg
    rw [Function.iterate_succ_apply', ← hrepr, matrix_action, ih, pow_succ',
      ← Matrix.mulVec_mulVec]

/-- A selected reduced-seed coefficient is a streamed matrix-power moment. -/
theorem seed_coeff (p f : R[X]) (d D : ℕ) (hd : 0 < d) (hdD : d ≤ D)
    (hD : (f * p.derivative).natDegree ≤ D) (i : Fin (D + 1)) :
    (seed p f d D).coeff i.val =
      ∑ j : Fin (D + 1), (matrix p d D ^ (2 * (D + 1))) i j *
        (f * p.derivative).coeff j.val := by
  have h := congrFun (iterate_toFn p (f * p.derivative) d D (2 * (D + 1)) hd hdD hD) i
  exact h

end LeanCanny.Algebra.PseudoRemainder
