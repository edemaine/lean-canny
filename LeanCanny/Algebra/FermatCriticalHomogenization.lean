/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCriticalInfinity
public import LeanCanny.Algebra.HomogenizationAdditive
public import LeanCanny.Algebra.CoerciveCriticalHomogenization
public import LeanCanny.Algebra.ProjectionCriticalFamily
public import LeanCanny.Algebra.PartialDerivativeDegree

/-! # Homogenized critical equations for pure-power leading polynomials

The lower-degree part is arbitrary. Homogenization agrees with the original
critical equations in the affine chart, while its restriction to infinity is
exactly the pure-power critical system.
-/

@[expose] public section
namespace LeanCanny.Algebra.FermatCriticalHomogenization
open MvPolynomial WeightedHomogenization
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

noncomputable def polynomial (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ) :
    MvPolynomial (Fin (n + 1)) R := low + C a * ∑ j : Fin (n + 1), X j ^ N

noncomputable def spatial (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ) (v : Fin n → R) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) R :=
  Fin.cons (polynomial low a N)
    (fun i => pderiv i.succ (polynomial low a N) - C (v i) * pderiv 0 (polynomial low a N))

noncomputable def rows (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ) (v : Fin n → R)
    (j : Fin (n + 1)) : MvPolynomial (Option (Fin (n + 1))) R :=
  homogenize (fun _ => 1) (FermatCriticalInfinity.degrees n N j) (spatial low a N v j)

theorem spatial_eq (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ) (v : Fin n → R) :
    spatial low a N v = ProjectionCriticalFamily.spatialEquation (polynomial low a N) 0 (Fin.cons 1 v) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;>
    simp [spatial, ProjectionCriticalFamily.spatialEquation]

theorem map_polynomial (φ : R →+* S) (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ) :
    (polynomial low a N).map φ = polynomial (low.map φ) (φ a) N := by
  simp [polynomial, map_sum]

theorem map_spatial (φ : R →+* S) (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ)
    (v : Fin n → R) (j : Fin (n + 1)) :
    (spatial low a N v j).map φ = spatial (low.map φ) (φ a) N (fun i => φ (v i)) j := by
  refine Fin.cases ?_ (fun _ => ?_) j <;>
    simp only [spatial, Fin.cons_zero, Fin.cons_succ, map_sub, map_mul, map_C,
      ← pderiv_map, map_polynomial]

theorem map_rows (φ : R →+* S) (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ)
    (v : Fin n → R) (j : Fin (n + 1)) :
    (rows low a N v j).map φ = rows (low.map φ) (φ a) N (fun i => φ (v i)) j := by
  rw [rows, map_homogenize, map_spatial]
  rfl

theorem pderiv_polynomial (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ) (i : Fin (n + 1)) :
    pderiv i (polynomial low a N) = pderiv i low + C (a * (N : R)) * X i ^ (N - 1) := by
  have hs : pderiv i (∑ j : Fin (n + 1), (X j : MvPolynomial (Fin (n + 1)) R) ^ N) =
      C (N : R) * X i ^ (N - 1) := by
    rw [map_sum, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [pderiv_pow, pderiv_X_of_ne hji, mul_zero]
    · simp
  rw [polynomial, map_add, pderiv_C_mul, hs, ← mul_assoc, ← map_mul]

theorem polynomial_degree [Nontrivial R] (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ)
    (hlow : low.totalDegree < N) : (polynomial low a N).totalDegree ≤ N := by
  apply (totalDegree_add _ _).trans
  apply max_le hlow.le
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, Nat.zero_add]
  apply totalDegree_finsetSum_le
  intro j _
  simpa only [totalDegree_X, Nat.mul_one] using totalDegree_pow (X j : MvPolynomial (Fin (n + 1)) R) N

theorem spatial_degree [Nontrivial R] (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ)
    (hlow : low.totalDegree < N) (v : Fin n → R) (j : Fin (n + 1)) :
    (spatial low a N v j).totalDegree ≤ FermatCriticalInfinity.degrees n N j := by
  have hp := polynomial_degree low a N hlow
  refine Fin.cases hp (fun i => ?_) j
  change (pderiv i.succ (polynomial low a N) - C (v i) * pderiv 0 (polynomial low a N)).totalDegree ≤ N - 1
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (PartialDerivativeDegree.degree_le _ _).trans (Nat.sub_le_sub_right hp 1)
  · apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, Nat.zero_add]
    exact (PartialDerivativeDegree.degree_le _ _).trans (Nat.sub_le_sub_right hp 1)

theorem rows_homogeneous (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ) (v : Fin n → R)
    (j : Fin (n + 1)) : (rows low a N v j).IsHomogeneous (FermatCriticalInfinity.degrees n N j) := by
  have hw : weights (fun _ : Fin (n + 1) => 1) = 1 := by funext i; cases i <;> rfl
  simpa only [rows, IsHomogeneous, hw] using homogeneous (fun _ => 1)
    (FermatCriticalInfinity.degrees n N j) (spatial low a N v j)

theorem eval_chart [Nontrivial R] (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ)
    (hlow : low.totalDegree < N) (v : Fin n → R) (x : Fin (n + 1) → R) (j : Fin (n + 1)) :
    eval (fun i => i.elim 1 x) (rows low a N v j) = eval x (spatial low a N v j) := by
  apply WeightedHomogenization.eval_chart
  intro e he
  exact (weight_le_degree (fun _ => 1) (by simp) e).trans
    ((le_totalDegree he).trans (spatial_degree low a N hlow v j))

theorem eval_infinity_polynomial (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ)
    (hlow : low.totalDegree < N) (x : Fin (n + 1) → R) :
    eval (fun i => i.elim 0 x) (homogenize (fun _ => 1) N (polynomial low a N)) =
      a * ∑ j : Fin (n + 1), x j ^ N := by
  rw [polynomial, homogenize_add, homogenize_C_mul, homogenize_sum]
  simp only [homogenize_X_pow, map_add, map_mul, eval_C, map_sum, map_pow, eval_X, Option.elim_some]
  rw [CoerciveCriticalHomogenization.homogenize_eval_infinity low N hlow _ rfl, zero_add]

theorem eval_infinity_partial (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ)
    (hlow : low.totalDegree < N) (hN : 1 < N) (x : Fin (n + 1) → R) (i : Fin (n + 1)) :
    eval (fun j => j.elim 0 x) (homogenize (fun _ => 1) (N - 1) (pderiv i (polynomial low a N))) =
      (a * (N : R)) * x i ^ (N - 1) := by
  have hd : (pderiv i low).totalDegree < N - 1 := (PartialDerivativeDegree.degree_le low i).trans_lt (by omega)
  rw [pderiv_polynomial, homogenize_add, homogenize_C_mul, homogenize_X_pow]
  simp only [map_add, map_mul, eval_C, map_pow, eval_X, Option.elim_some]
  rw [CoerciveCriticalHomogenization.homogenize_eval_infinity _ _ hd _ rfl, zero_add]

theorem eval_infinity (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ)
    (hlow : low.totalDegree < N) (hN : 1 < N) (v : Fin n → R) (x : Fin (n + 1) → R) (j : Fin (n + 1)) :
    eval (fun i => i.elim 0 x) (rows low a N v j) = eval x (FermatCriticalInfinity.native a N v j) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa only [rows, spatial, FermatCriticalInfinity.native, FermatCriticalInfinity.degrees,
      Fin.cons_zero, map_mul, eval_C, map_sum, map_pow, eval_X] using eval_infinity_polynomial low a N hlow x
  · simp only [rows, spatial, FermatCriticalInfinity.native, FermatCriticalInfinity.degrees, Fin.cons_succ,
      homogenize_sub, homogenize_C_mul, map_sub, map_mul, eval_C, map_pow, eval_X]
    rw [eval_infinity_partial low a N hlow hN x i.succ, eval_infinity_partial low a N hlow hN x 0]
    ring

end LeanCanny.Algebra.FermatCriticalHomogenization
