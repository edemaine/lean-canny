/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.TraceExponentialNewton
public import LeanCanny.CountingHierarchy.QuotientTraceSpecialization

/-! # Characteristic polynomials determined by power traces -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial Matrix
open scoped Classical BigOperators

/-- Matrices of equal dimension with equal power traces have equal
 characteristic polynomials whenever the necessary integer multipliers
 are nonzero in the field. -/
theorem charpoly_eq_of_power_traces {K ι κ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι ι K) (N : Matrix κ κ K) (hdim : Fintype.card κ = Fintype.card ι)
    (hK : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → (j : K) ≠ 0)
    (htrace : ∀ j ≤ Fintype.card ι, (M ^ j).trace = (N ^ j).trace) :
    M.charpoly = N.charpoly := by
  have hQ (k : ℕ) (_hk : k < Fintype.card ι) :
      (k + 1 : ℕ) * N.charpolyRev.coeff (k + 1) =
        -(∑ j ∈ Finset.range (k + 1), N.charpolyRev.coeff (k - j) * (M ^ (j + 1)).trace) := by
    rw [charpolyRev_newton]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [htrace (j + 1) (by have := Finset.mem_range.mp hj; omega)]
  have hrev (k : ℕ) (hk : k ≤ Fintype.card ι) : M.charpolyRev.coeff k = N.charpolyRev.coeff k := by
    apply coefficients_eq_of_newton (Fintype.card ι) (fun j => (M ^ j).trace)
      M.charpolyRev N.charpolyRev hK _ (fun j _ => charpolyRev_newton M j) hQ k hk
    simp only [coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  apply Polynomial.ext
  intro k
  by_cases hk : k ≤ Fintype.card ι
  · have h := hrev (Fintype.card ι - k) (Nat.sub_le _ _)
    rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly, coeff_reverse, coeff_reverse,
      Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim, hdim,
      revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hk] at h
    exact h
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim]; omega),
      coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim, hdim]; omega)]

namespace PurePowerResidue

open MvPolynomial

/-- Specializing the source characteristic polynomial agrees with the
 characteristic polynomial of the specialized quotient. This applies both
 in characteristic zero and at primes larger than the quotient dimension. -/
theorem multiplicationMatrix_charpoly_map {S K : Type*} [CommRing S] [Field K]
    {n : ℕ} (φ : S →+* K) (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) S)
    (hK : ∀ j, 1 ≤ j → j ≤ (d + 1) ^ n → (j : K) ≠ 0) :
    ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly).map φ =
      (multiplicationMatrix (by omega : 1 ≤ d + 1) (fun i => (r i).map φ)
        (fun i => (map_degree_le φ _).trans_lt ((hr i).trans_lt (Nat.lt_succ_self d)))
        (v.map φ)).charpoly := by
  rw [← Matrix.charpoly_map]
  apply charpoly_eq_of_power_traces _ _ rfl
    (fun j hj hle => hK j hj (by simpa only [card_normalIndex] using hle))
  intro k _
  rw [multiplicationMatrix_map_trace_pow φ d hd r hr v k]
  have hr' (i : Fin n) : ((r i).map φ).totalDegree ≤ d := (map_degree_le φ _).trans (hr i)
  exact (multiplicationMatrix_trace_pow d hd (fun i => (r i).map φ) hr' (v.map φ) k).symm

end PurePowerResidue
end LeanCanny.CountingHierarchy
