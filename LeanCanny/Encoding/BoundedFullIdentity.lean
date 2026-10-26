/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexBoundedFullEncoding
public import LeanCanny.Geometry.BoundedRegularSource

/-! # The variable-coordinate circuit is the full geometric source

The polynomial identity holds before choosing a sample. Evaluation works over
any commutative ring, and the old zero energy is identified on its own wire.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullIdentity
open MvPolynomial LeanCanny.Algebra LeanCanny.Geometry LeanCanny.ETR LeanCanny.ETR.ComplexCircuit
open scoped Classical BigOperators

def inputs {K : Type*} (a : K) (x : ℕ → K) (i : ℕ) : K := if i = 0 then a else x (i - 1)

theorem inputs_cons {K : Type*} (a : K) (x : ℕ → K) (k : ℕ) :
    Fin.cons a (fun j : Fin k => x j.val) = (fun j : Fin (k + 1) => inputs a x j.val) := by
  funext j
  refine Fin.cases (by simp [inputs]) (fun i => by simp [inputs]) j

theorem sum_inputs {K : Type*} [CommRing K] (a : K) (x : ℕ → K) (k N : ℕ) :
    (∑ j : Fin (k + 1), inputs a x j.val ^ N) = a ^ N + ∑ i ∈ Finset.range k, x i ^ N := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, inputs, ite_true, Fin.val_succ, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel_right]
  exact congrArg (a ^ N + ·) (Fin.sum_univ_eq_sum_range (fun i => x i ^ N) k)

theorem term_eval {n : ℕ} {K : Type*} [CommRing K] (t : Term) (q : MvPolynomial (Fin n) ℤ)
    (ht : t.toPolynomial = rename Fin.val q) (parameter : ℕ) (x : ℕ → K) :
    (CircuitFreeze.substitution parameter t.toPolynomial).eval₂ (Int.castRingHom K) x =
      q.eval₂ (Int.castRingHom K) (fun j => inputs (x parameter) x j.val) := by
  rw [CircuitFreeze.eval_substitution, ht, eval₂_rename]
  rfl

theorem polynomial_eval {n : ℕ} {K : Type*} [CommRing K] (t : Term) (q : MvPolynomial (Fin n) ℤ)
    (ht : t.toPolynomial = rename Fin.val q) (D b R parameter : ℕ) (x : ℕ → K) :
    (BoundedFullSource.polynomial parameter (n + 1) t (2 * R).bits
      (BoundedZeroSource.perturbationExponent n D b R).bits (BoundedZeroSource.penaltyExponent n D R).bits
      (BoundedZeroSource.powerDegree D - 1).bits (BoundedRegularSource.regularizationExponent n D b R).bits).eval₂
        (Int.castRingHom K) x =
      (BoundedRegularSource.polynomial q D b R).eval₂ (Int.castRingHom K)
        (Fin.cons (x parameter) (fun j : Fin (n + 3) => x j.val)) := by
  have hN : BoundedZeroSource.powerDegree D - 1 + 1 = BoundedZeroSource.powerDegree D := by
    have := BoundedRegularSource.powerDegree_gt_one D
    omega
  rw [inputs_cons]
  conv_rhs => rw [BoundedRegularSource.polynomial, IntegerRegularSource.polynomial_eq]
  simp only [FermatCriticalHomogenization.polynomial, BoundedRegularSource.lower, BoundedZeroSource.polynomial,
    BoundedZeroSource.sphere, BoundedZeroSource.radiusSquared, eval₂_sub, eval₂_add, eval₂_mul, eval₂_rename,
    Function.comp_def, eval₂_C, eval₂_one, eval₂_pow, eval₂_sum, eval₂_X, Fin.val_castAdd,
    Int.coe_castRingHom, IntegerRegularSource.scale, BoundedRegularSource.regularizationExponent,
    Int.cast_pow, Int.cast_ofNat, Int.cast_one, one_mul]
  simp only [BoundedFullSource.polynomial, BoundedTail.polynomial, BoundedLow.polynomial,
    eval₂_sub, eval₂_add, eval₂_mul, eval₂_C, eval₂_pow, eval₂_sum, eval₂_X, eval₂_one,
    Nat.fromBitsLE_bits, hN, Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat, term_eval t q ht]
  rw [sum_inputs (x parameter) x (n + 1) 2, sum_inputs (x parameter) x (n + 3) (BoundedZeroSource.powerDegree D)]

theorem energy_eval {n : ℕ} {K : Type*} [CommRing K] (t : Term) (q : MvPolynomial (Fin n) ℤ)
    (ht : t.toPolynomial = rename Fin.val q) (R parameter : ℕ) (x : ℕ → K) :
    (BoundedFullSource.energy parameter (n + 1) t (2 * R).bits).eval₂ (Int.castRingHom K) x =
      (BoundedZeroSource.polynomial q R).eval₂ (Int.castRingHom K)
        (Fin.cons (x parameter) (fun j : Fin (n + 1) => x j.val)) := by
  rw [inputs_cons]
  simp only [BoundedFullSource.energy, BoundedTail.energy, BoundedZeroSource.polynomial, BoundedZeroSource.sphere,
    BoundedZeroSource.radiusSquared, eval₂_add, eval₂_pow, eval₂_sub, eval₂_C, eval₂_sum, eval₂_X,
    eval₂_rename, Function.comp_def, Fin.val_castAdd, Nat.fromBitsLE_bits, Int.coe_castRingHom,
    Int.cast_pow, Int.cast_ofNat, term_eval t q ht]
  rw [sum_inputs (x parameter) x (n + 1) 2]

theorem polynomial_identity {n : ℕ} (t : Term) (q : MvPolynomial (Fin n) ℤ)
    (ht : t.toPolynomial = rename Fin.val q) (D b R parameter : ℕ) :
    BoundedFullSource.polynomial parameter (n + 1) t (2 * R).bits
      (BoundedZeroSource.perturbationExponent n D b R).bits (BoundedZeroSource.penaltyExponent n D R).bits
      (BoundedZeroSource.powerDegree D - 1).bits (BoundedRegularSource.regularizationExponent n D b R).bits =
        CircuitFreeze.substitution parameter (rename Fin.val (BoundedRegularSource.polynomial q D b R)) := by
  apply Differential.eq_of_eval_complex
  intro x
  rw [polynomial_eval t q ht, CircuitFreeze.eval_substitution, eval₂_rename]
  exact congrArg ((BoundedRegularSource.polynomial q D b R).eval₂ (Int.castRingHom ℂ))
    (inputs_cons (x parameter) x (n + 3))

theorem energy_identity {n : ℕ} (t : Term) (q : MvPolynomial (Fin n) ℤ)
    (ht : t.toPolynomial = rename Fin.val q) (R parameter : ℕ) :
    BoundedFullSource.energy parameter (n + 1) t (2 * R).bits = CircuitFreeze.substitution parameter
      (rename Fin.val (rename (Fin.castAdd 2) (BoundedZeroSource.polynomial q R))) := by
  apply Differential.eq_of_eval_complex
  intro x
  rw [energy_eval t q ht, CircuitFreeze.eval_substitution, eval₂_rename, eval₂_rename]
  exact congrArg ((BoundedZeroSource.polynomial q R).eval₂ (Int.castRingHom ℂ))
    (inputs_cons (x parameter) x (n + 1))

end LeanCanny.Encoding.BoundedFullIdentity
