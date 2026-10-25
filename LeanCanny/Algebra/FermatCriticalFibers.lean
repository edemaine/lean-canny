/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCriticalHomogenization
public import LeanCanny.Algebra.CoerciveCriticalFibers

/-! # Finite gradient fibers for arbitrary pure-power leading polynomials -/

@[expose] public section
namespace LeanCanny.Algebra.FermatCriticalHomogenization
open MvPolynomial
open scoped Classical

variable {n : ℕ} {K : Type*} [Field K] [CharZero K]

theorem gradient_quotient_finite (low : MvPolynomial (Fin (n + 1)) K) (a : K)
    (N : ℕ) (hlow : low.totalDegree < N) (ha : a ≠ 0) (hN : 1 < N)
    (v : Fin (n + 1) → K) :
    Module.Finite K (MvPolynomial (Fin (n + 1)) K ⧸
      CoerciveCriticalFibers.generated (fun i => pderiv i (polynomial low a N) - C (v i))) := by
  have hl (i : Fin (n + 1)) : (pderiv i low - C (v i)).totalDegree < N - 1 := by
    apply (totalDegree_sub _ _).trans_lt
    apply max_lt
    · exact (PartialDerivativeDegree.degree_le low i).trans_lt (by omega)
    · simp only [totalDegree_C]
      omega
  have he : (fun i => pderiv i (polynomial low a N) - C (v i)) =
      CoerciveCriticalFibers.powerSystem (N - 1) (fun _ => a * (N : K))
        (fun i => pderiv i low - C (v i)) := by
    funext i
    rw [pderiv_polynomial, X_pow_eq_monomial, C_mul_monomial]
    simp only [CoerciveCriticalFibers.powerSystem, mul_one]
    abel
  rw [he]
  exact CoerciveCriticalFibers.quotient_finite _ _ _
    (fun _ => mul_ne_zero ha (Nat.cast_ne_zero.mpr (by omega))) hl

theorem finite_gradient_fiber (low : MvPolynomial (Fin (n + 1)) K) (a : K)
    (N : ℕ) (hlow : low.totalDegree < N) (ha : a ≠ 0) (hN : 1 < N)
    (v : Fin (n + 1) → K) :
    {x : Fin (n + 1) → K | ∀ i, eval x (pderiv i (polynomial low a N)) = v i}.Finite := by
  have h := CoerciveCriticalFibers.finite_zero_set
    (fun i => pderiv i (polynomial low a N) - C (v i))
    (gradient_quotient_finite low a N hlow ha hN v)
  simpa only [eval_sub, eval_C, sub_eq_zero] using h

theorem finite_critical_points (low : MvPolynomial (Fin (n + 1)) K) (a : K)
    (N : ℕ) (hlow : low.totalDegree < N) (ha : a ≠ 0) (hN : 1 < N) :
    {x : Fin (n + 1) → K | ∀ i, eval x (pderiv i (polynomial low a N)) = 0}.Finite :=
  finite_gradient_fiber low a N hlow ha hN (fun _ => 0)

end LeanCanny.Algebra.FermatCriticalHomogenization
