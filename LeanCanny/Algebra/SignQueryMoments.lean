/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignQueryTarskiSpace

/-! # Product Tarski queries are moments of root-sign evaluations -/

@[expose] public section
namespace LeanCanny.Algebra.SignQueryBits
open Polynomial
open scoped Classical BigOperators

theorem Family.value_eq_sum (F : Family) (c : List Bool) :
    F.value c = ∑ x ∈ ((F.root c).map (algebraMap ℤ ℝ)).roots.toFinset,
      ∏ i ∈ Finset.range (Nat.fromBitsLE (F.count c)),
        (SignType.sign (((F.polynomial c i).map (algebraMap ℤ ℝ)).eval x) : ℤ) ^ (F.exponent c i).val := by
  unfold Family.value RootSignQueries.tarskiQuery RootSignQueries.signSum
  apply Finset.sum_congr rfl
  intro x _
  let ψ : ℝ →*₀ ℤ := SignType.castHom.comp signHom
  change ψ (((F.product c).map (algebraMap ℤ ℝ)).eval x) =
    ∏ i ∈ Finset.range (Nat.fromBitsLE (F.count c)),
      ψ (((F.polynomial c i).map (algebraMap ℤ ℝ)).eval x) ^ (F.exponent c i).val
  simp only [Family.product, Polynomial.map_prod, Polynomial.map_pow, Polynomial.eval_prod,
    Polynomial.eval_pow, map_prod, map_pow]

end LeanCanny.Algebra.SignQueryBits
