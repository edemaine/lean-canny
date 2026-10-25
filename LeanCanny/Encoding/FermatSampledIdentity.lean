/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FermatAffineKernelBridge
public import LeanCanny.ETR.ComplexFrozenSlice
public import LeanCanny.ETR.ComplexSampledSource
public import LeanCanny.Geometry.IntegerRegularSource
public import LeanCanny.Algebra.PolynomialMapDegree

/-! # The computed sampled source is the actual finite Fermat polynomial

Evaluation identifies the shared circuit's polynomial with the coefficient-
specialized dyadic regular source. The original low term supplies its own
polynomial identity; values, gradients, and Hessians then transfer together.
-/

@[expose] public section
namespace LeanCanny.Encoding.FermatSweepCertificate
open MvPolynomial LeanCanny.Algebra LeanCanny.ETR LeanCanny.ETR.ComplexCircuit
open scoped Classical BigOperators

variable {n : ℕ}

theorem sampledPolynomial_eval (low : MvPolynomial (Fin (n + 2)) ℚ) (a : ℚ)
    (N : ℕ) (record : List Bool) (x : Fin (n + 1) → ℂ) :
    (sampledPolynomial low a N record).eval x =
      low.eval₂ (algebraMap ℚ ℂ) (Fin.cons (sample n N record : ℂ) x) +
        (a : ℂ) * ((sample n N record : ℂ) ^ N + ∑ j : Fin (n + 1), x j ^ N) := by
  rw [sampledPolynomial, eval_map]
  simp only [FermatCriticalHomogenization.polynomial, FermatBoundedSweepSample.lower,
    eval₂_add, eval₂_mul, eval₂_C, eval₂_sum, eval₂_pow, eval₂_X, sampleMap,
    CoordinateSlicePolynomial.eval_family, Polynomial.coe_eval₂RingHom, map_mul, map_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, eq_ratCast]
  ring

theorem term_eval_slice (t : Term) (low : MvPolynomial (Fin (n + 2)) ℤ)
    (ht : t.toPolynomial = rename Fin.val low) (s : ℤ) (x : ℕ → ℂ) :
    t.eval (FrozenSource.inputs s x) = low.eval₂ (Int.castRingHom ℂ) (Fin.cons (s : ℂ) (fun j => x j.val)) := by
  have h := congrArg (fun p : MvPolynomial ℕ ℂ => p.eval x) (FrozenSource.polynomial_map_slice t low ht s)
  simpa only [eval_map, eval_rename, Function.comp_def, CoordinateSlicePolynomial.eval_family,
    FrozenSource.polynomial_eval] using h

noncomputable def dyadicLow (low : MvPolynomial (Fin (n + 2)) ℤ) (E : ℕ) : MvPolynomial (Fin (n + 2)) ℚ :=
  (C ((2 : ℤ) ^ E) * low - 1).map (Int.castRingHom ℚ)

def dyadicLeading (a : ℤ) (E : ℕ) : ℚ := ((2 : ℤ) ^ E * a : ℤ)

theorem dyadicLeading_ne_zero (a : ℤ) (ha : a ≠ 0) (E : ℕ) : dyadicLeading a E ≠ 0 := by
  unfold dyadicLeading
  exact_mod_cast (mul_ne_zero (pow_ne_zero E (by norm_num : (2 : ℤ) ≠ 0)) ha)

theorem dyadicLow_degree (low : MvPolynomial (Fin (n + 2)) ℤ) (E N : ℕ) (hlow : low.totalDegree < N) :
    (dyadicLow low E).totalDegree < N := by
  apply (PolynomialMapDegree.degree_le _ _).trans_lt
  apply (totalDegree_sub _ _).trans_lt
  apply max_lt
  · apply (totalDegree_mul _ _).trans_lt
    simpa only [totalDegree_C, Nat.zero_add] using hlow
  · rw [totalDegree_one]
    omega

theorem sampled_source_identity (t : Term) (low : MvPolynomial (Fin (n + 2)) ℤ)
    (ht : t.toPolynomial = rename Fin.val low) (a : ℤ) (N : ℕ) (record : List Bool)
    (bits exponent : List Bool) (hN : Nat.fromBitsLE bits + 1 = N) :
    (SampledSource.polynomial (n + 1) (sample n N record : ℤ) a t bits exponent).map (Int.castRingHom ℂ) =
      rename Fin.val (sampledPolynomial (dyadicLow low (Nat.fromBitsLE exponent))
        (dyadicLeading a (Nat.fromBitsLE exponent)) N record) := by
  apply MvPolynomial.funext
  intro x
  simp only [eval_map, eval_rename, Function.comp_def]
  rw [SampledSource.polynomial_eval, sampledPolynomial_eval, term_eval_slice t low ht, hN]
  have hcast : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := RingHom.ext_int _ _
  simp only [dyadicLow, dyadicLeading, eval₂_map, hcast, eval₂_sub, eval₂_mul, eval₂_C,
    eval₂_one, Int.coe_castRingHom, Int.cast_natCast, Int.cast_pow, Int.cast_mul, Int.cast_ofNat,
    Rat.cast_intCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  rw [Fin.sum_univ_eq_sum_range (fun i => x i ^ N) (n + 1)]
  ring

theorem integer_regular_source_identity (t : Term) (low : MvPolynomial (Fin (n + 2)) ℤ)
    (ht : t.toPolynomial = rename Fin.val low) (a : ℤ) (N b : ℕ) (record : List Bool)
    (hN : 0 < N) :
    (SampledSource.polynomial (n + 1) (sample n N record : ℤ) a t (N - 1).bits
      (LeanCanny.Geometry.IntegerRegularSource.exponent (n + 1) N b).bits).map (Int.castRingHom ℂ) =
        rename Fin.val (sampledPolynomial
          ((LeanCanny.Geometry.IntegerRegularSource.lower low N b).map (Int.castRingHom ℚ))
          (LeanCanny.Geometry.IntegerRegularSource.leading (n + 1) a N b : ℚ) N record) := by
  have h := sampled_source_identity t low ht a N record (N - 1).bits
    (LeanCanny.Geometry.IntegerRegularSource.exponent (n + 1) N b).bits (by rw [Nat.fromBitsLE_bits]; omega)
  simpa only [Nat.fromBitsLE_bits, dyadicLow, dyadicLeading, LeanCanny.Geometry.IntegerRegularSource.lower,
    LeanCanny.Geometry.IntegerRegularSource.leading, LeanCanny.Geometry.IntegerRegularSource.scale] using h

end LeanCanny.Encoding.FermatSweepCertificate
