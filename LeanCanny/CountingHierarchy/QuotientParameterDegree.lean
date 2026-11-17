/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ParameterDegree
public import LeanCanny.CountingHierarchy.NewtonDegreeBounds
public import LeanCanny.CountingHierarchy.QuotientCharacteristicEvaluation

/-! # Parameter-degree bounds without quotient matrix entries -/

public section

namespace LeanCanny.CountingHierarchy.PurePowerResidue

open Polynomial MvPolynomial
open scoped BigOperators Classical

variable {n : ℕ}

theorem jacobian_hasParameterDegree (ell H : ℕ)
    (r : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (hr : ∀ i, HasParameterDegree (r i) H) :
    HasParameterDegree (jacobian ell r) (n * H) := by
  have he (i j : Fin n) :
      HasParameterDegree (pderiv j (MvPolynomial.X i ^ ell - r i)) H := by
    have hx := ((HasParameterDegree.X i).pow ell).mono (show ell * 0 ≤ H by simp)
    simpa only [max_self] using (hx.sub (hr i)).pderiv j
  simpa only [jacobian, Fintype.card_fin] using
    HasParameterDegree.det (fun i j : Fin n => pderiv j (MvPolynomial.X i ^ ell - r i)) he

theorem truncated_parameterDegree_le (ell B H K : ℕ)
    (r : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (hr : ∀ i, HasParameterDegree (r i) H)
    (v : MvPolynomial (Fin n) (Polynomial ℤ)) (hv : HasParameterDegree v K) :
    (truncated ell r B v).natDegree ≤ K + n * (B * H) := by
  change (∑ j ∈ indices n B, term ell r v j).natDegree ≤ _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hp := HasParameterDegree.prod Finset.univ (fun i => r i ^ j i) (fun i _ =>
    ((hr i).pow (j i)).mono (Nat.mul_le_mul_right H (mem_indices.mp hj i)))
  have hh := hv.mul hp
  simpa only [term, Finset.card_univ, Fintype.card_fin] using hh (target ell j)

theorem residue_parameterDegree_le {ell : ℕ} (hell : 1 ≤ ell) (B H K : ℕ)
    (r : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (hr : ∀ i, (r i).totalDegree < ell) (hparam : ∀ i, HasParameterDegree (r i) H)
    (v : MvPolynomial (Fin n) (Polynomial ℤ)) (hv : HasParameterDegree v K)
    (hB : v.totalDegree ≤ B) : (residue ell r v).natDegree ≤ K + n * (B * H) := by
  rw [residue_eq_truncated hell r hr v hB]
  exact truncated_parameterDegree_le ell B H K r hparam v hv

/-- The degree in the independent parameter of every characteristic coefficient
 is bounded by a short expression in the source degrees. -/
theorem multiplicationMatrix_charpoly_parameterDegree_le (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) (Polynomial ℤ))
    (Ω H K : ℕ) (hvdeg : v.totalDegree ≤ Ω)
    (hparam : ∀ i, HasParameterDegree (r i) H) (hv : HasParameterDegree v K) (k : ℕ) :
    (((multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly).coeff k).natDegree ≤
        (d + 1) ^ n * ((d + 1) ^ n * K + n * H + n * (((d + 1) ^ n * Ω + n * d) * H)) := by
  let D := (d + 1) ^ n
  let B := D * Ω + n * d
  have hJ := jacobian_hasParameterDegree (d + 1) H r hparam
  have ht (j : ℕ) (_hj : 1 ≤ j) (hle : j ≤ D) :
      ((((multiplicationMatrix (by omega : 1 ≤ d + 1) r
        (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v) ^ j).trace)).natDegree ≤
          D * K + n * H + n * (B * H) := by
    rw [multiplicationMatrix_trace_pow d hd r hr v j]
    apply (residue_parameterDegree_le (by omega : 1 ≤ d + 1) B H (j * K + n * H) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) hparam _ ((hv.pow j).mul hJ)
      (quotient_trace_numerator_degree d r hr v Ω D j hvdeg hle)).trans
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right K hle) _) _
  simpa only [card_normalIndex, D, B] using charpoly_coefficient_parameterDegree_le
    (multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v)
    (D * K + n * H + n * (B * H))
    (fun j hj hle => ht j hj (by simpa only [card_normalIndex, D] using hle)) k

end LeanCanny.CountingHierarchy.PurePowerResidue
