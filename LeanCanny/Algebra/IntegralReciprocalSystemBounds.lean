/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMacaulayGramBounds
public import LeanCanny.Algebra.IntegralFrozenConstantBounds

/-! # Integer block heights of the literal reciprocal value equation

The reciprocal row is linear in its independent value variable. Its
constant chart monomial and the original test coefficient are bounded
explicitly, including at zero divisors and degree drops.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralReciprocalSystemBounds
open Polynomial MvPolynomial
open scoped Classical
variable {A : Type*} [CommRing A] {M n : ℕ}

theorem coefficient_height (b : Module.Basis (Fin M) ℤ A)
    (rows : Fin n → MvPolynomial (Fin (n + 1)) A) (p : MvPolynomial (Fin (n + 1)) A)
    (D HC HP : ℕ)
    (hc : ∀ j e u v, (Algebra.leftMulMatrix b ((rows j).coeff e) u v).natAbs ≤ 2 ^ HC)
    (hp : ∀ e u v, (Algebra.leftMulMatrix b (p.coeff e) u v).natAbs ≤ 2 ^ HP)
    (j : Fin (n + 1)) (e : Fin (n + 1) →₀ ℕ) (k : ℕ) (u v : Fin M) :
    (Algebra.leftMulMatrix b (((RelativeValueSystemMap.reciprocal rows p D j).coeff e).coeff k) u v).natAbs ≤
      2 ^ (HC + HP + 1) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · have HT : (Algebra.leftMulMatrix b ((Polynomial.X * Polynomial.C (p.coeff e)).coeff k) u v).natAbs ≤ 2 ^ HP := by
      rw [mul_comm, ← pow_one (Polynomial.X : Polynomial A), Polynomial.C_mul_X_pow_eq_monomial,
        Polynomial.coeff_monomial]
      split_ifs
      · exact hp e u v
      · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
        exact Nat.zero_le _
    have HU : (Algebra.leftMulMatrix b
        ((if Finsupp.single (0 : Fin (n + 1)) D = e then (1 : Polynomial A) else 0).coeff k) u v).natAbs ≤ 2 ^ 0 := by
      split_ifs
      · rw [Polynomial.coeff_one]
        split_ifs
        · rw [map_one, Matrix.one_apply]
          split_ifs <;> norm_num
        · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
          exact Nat.zero_le _
      · rw [Polynomial.coeff_zero, map_zero, Matrix.zero_apply, Int.natAbs_zero]
        exact Nat.zero_le _
    rw [RelativeValueSystemMap.reciprocal, Fin.cases_zero, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, MvPolynomial.coeff_X_pow,
      Polynomial.coeff_sub, map_sub, Matrix.sub_apply]
    exact (IntegralFrozenConstantBounds.subtract_bound _ _ _ _ HT HU).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
  · rw [RelativeValueSystemMap.reciprocal, Fin.cases_succ, MvPolynomial.coeff_map, Polynomial.coeff_C]
    split_ifs
    · exact (hc j e u v).trans (Nat.pow_le_pow_right (by decide) (by omega))
    · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
      exact Nat.zero_le _

end LeanCanny.Algebra.IntegralReciprocalSystemBounds
