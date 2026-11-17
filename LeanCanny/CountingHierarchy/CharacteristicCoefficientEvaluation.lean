/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.TraceExponentialNewton
public import LeanCanny.CountingHierarchy.TraceCoefficients

/-! # Correct indexed characteristic coefficients from modular power traces -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial Matrix
open scoped Classical BigOperators

/-- The existing uniform evaluator returns actual characteristic
 coefficients, with the canonical zero default above the dimension. -/
theorem traceExponentialCoefficient_eq_charpoly {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod p))
    (hD : Fintype.card ι < p - 1) (hdegree : Fintype.card ι * Fintype.card ι < p - 1)
    (d : ℕ) (t : ℕ → ℕ)
    (ht : ∀ k ≤ Fintype.card ι, (t k : ZMod p) = (M ^ k).trace) :
    traceExponentialCoefficient p (Fintype.card ι) d t = (M.charpoly.coeff d).val := by
  by_cases hd : d ≤ Fintype.card ι
  · have hK : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → (j : ZMod p) ≠ 0 := by
      intro j hj hle hz
      have hdiv := (ZMod.natCast_eq_zero_iff j p).mp hz
      have hpj := Nat.le_of_dvd (by omega : 0 < j) hdiv
      omega
    have hpoly : coefficientPolynomial (Fintype.card ι)
        (fun k => -(t k : ZMod p) / (k : ZMod p)) =
        coefficientPolynomial (Fintype.card ι)
          (fun k => -(M ^ k).trace / (k : ZMod p)) := by
      unfold coefficientPolynomial
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only
      rw [ht k (by have := Finset.mem_range.mp hk; omega)]
    have hexp : truncatedExponential (Fintype.card ι)
        (fun k => -(t k : ZMod p) / (k : ZMod p)) =
        truncatedExponential (Fintype.card ι)
          (fun k => -(M ^ k).trace / (k : ZMod p)) := by
      simp only [truncatedExponential, hpoly]
    rw [traceExponentialCoefficient_eq hD hdegree hd, hexp,
      trace_exponential_coeff_eq_charpoly M hK d hd]
  · rw [traceExponentialCoefficient, ite_eq_right hd,
      coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim]; omega),
      ZMod.val_zero]

end LeanCanny.CountingHierarchy
