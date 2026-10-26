/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexBoundedEncoding
public import LeanCanny.Encoding.FermatSampledIdentity
public import LeanCanny.Geometry.BoundedRegularSource

/-! # Exact sampled semantics of the bounded regular source

The shared circuit is identified with the coordinate slice of the actual
integer polynomial, before transferring derivatives or critical kernels.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedSampledIdentity
open MvPolynomial LeanCanny.Algebra LeanCanny.Geometry LeanCanny.ETR LeanCanny.ETR.ComplexCircuit
open scoped Classical BigOperators

theorem inputs_cons (sample : ℤ) (x : ℕ → ℂ) (k : ℕ) :
    Fin.cons (sample : ℂ) (fun j : Fin k => x j.val) =
      (fun j : Fin (k + 1) => FrozenSource.inputs sample x j.val) := by
  funext j
  refine Fin.cases (by simp [FrozenSource.inputs]) (fun i => by simp [FrozenSource.inputs]) j

theorem sum_inputs (sample : ℤ) (x : ℕ → ℂ) (k N : ℕ) :
    (∑ j : Fin (k + 1), FrozenSource.inputs sample x j.val ^ N) =
      (sample : ℂ) ^ N + ∑ i ∈ Finset.range k, x i ^ N := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, FrozenSource.inputs, ite_true, Fin.val_succ, Nat.add_one_ne_zero,
    ite_false, Nat.add_sub_cancel_right]
  exact congrArg ((sample : ℂ) ^ N + ·) (Fin.sum_univ_eq_sum_range (fun i => x i ^ N) k)

theorem polynomial_eval {n : ℕ} (t : Term) (q : MvPolynomial (Fin n) ℤ)
    (ht : t.toPolynomial = rename Fin.val q) (D b R : ℕ) (sample : ℤ) (x : ℕ → ℂ) :
    (BoundedSource.polynomial (n + 1) sample t (2 * R).bits
      (BoundedZeroSource.perturbationExponent n D b R).bits (BoundedZeroSource.penaltyExponent n D R).bits
      (BoundedZeroSource.powerDegree D - 1).bits (BoundedRegularSource.regularizationExponent n D b R).bits).eval₂
        (Int.castRingHom ℂ) x =
      (BoundedRegularSource.polynomial q D b R).eval₂ (Int.castRingHom ℂ)
        (Fin.cons (sample : ℂ) (fun j : Fin (n + 3) => x j.val)) := by
  have hN : BoundedZeroSource.powerDegree D - 1 + 1 = BoundedZeroSource.powerDegree D := by
    have := BoundedRegularSource.powerDegree_gt_one D
    omega
  have hq : t.eval (FrozenSource.inputs sample x) =
      q.eval₂ (Int.castRingHom ℂ) (fun j => FrozenSource.inputs sample x j.val) := by
    rw [← Term.eval₂_toPolynomial, ht, eval₂_rename]
    rfl
  rw [inputs_cons]
  conv_rhs => rw [BoundedRegularSource.polynomial, IntegerRegularSource.polynomial_eq]
  simp only [FermatCriticalHomogenization.polynomial, BoundedRegularSource.lower, BoundedZeroSource.polynomial,
    BoundedZeroSource.sphere, BoundedZeroSource.radiusSquared, eval₂_sub, eval₂_add, eval₂_mul,
    eval₂_rename, Function.comp_def, eval₂_C, eval₂_one, eval₂_pow, eval₂_sum, eval₂_X,
    Fin.val_castAdd, Int.coe_castRingHom, IntegerRegularSource.scale, BoundedRegularSource.regularizationExponent,
    Int.cast_pow, Int.cast_ofNat, Int.cast_one, one_mul]
  simp only [BoundedSource.polynomial, BoundedLow.polynomial, eval₂_sub, eval₂_add, eval₂_mul,
    eval₂_C, eval₂_pow, eval₂_sum, eval₂_X, eval₂_one, FrozenSource.polynomial_eval,
    Nat.fromBitsLE_bits, hN, Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat, hq]
  rw [sum_inputs sample x (n + 1) 2, sum_inputs sample x (n + 3) (BoundedZeroSource.powerDegree D)]

theorem source_identity {n : ℕ} (t : Term) (q : MvPolynomial (Fin n) ℤ)
    (ht : t.toPolynomial = rename Fin.val q) (D b R : ℕ) (sample : ℤ) :
    (BoundedSource.polynomial (n + 1) sample t (2 * R).bits
      (BoundedZeroSource.perturbationExponent n D b R).bits (BoundedZeroSource.penaltyExponent n D R).bits
      (BoundedZeroSource.powerDegree D - 1).bits (BoundedRegularSource.regularizationExponent n D b R).bits).map
        (Int.castRingHom ℂ) = rename Fin.val
          ((CoordinateSlicePolynomial.family (BoundedRegularSource.polynomial q D b R)).map
            (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (sample : ℂ))) := by
  apply MvPolynomial.funext
  intro x
  simp only [eval_map, eval_rename, Function.comp_def, CoordinateSlicePolynomial.eval_family]
  exact polynomial_eval t q ht D b R sample x

theorem slice_fermat_eq {n : ℕ} (low : MvPolynomial (Fin (n + 2)) ℤ) (a : ℤ) (N : ℕ) (record : List Bool) :
    (CoordinateSlicePolynomial.family (FermatCriticalHomogenization.polynomial low a N)).map
      (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (FermatSweepCertificate.sample n N record : ℂ)) =
        FermatSweepCertificate.sampledPolynomial (low.map (Int.castRingHom ℚ)) (a : ℚ) N record := by
  apply MvPolynomial.funext
  intro x
  rw [eval_map, CoordinateSlicePolynomial.eval_family, FermatSweepCertificate.sampledPolynomial_eval]
  have hc : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := RingHom.ext_int _ _
  simp only [FermatCriticalHomogenization.polynomial, eval₂_add, eval₂_mul, eval₂_C, eval₂_sum,
    eval₂_pow, eval₂_X, eval₂_map, hc, Int.coe_castRingHom, Rat.cast_intCast]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

end LeanCanny.Encoding.BoundedSampledIdentity
