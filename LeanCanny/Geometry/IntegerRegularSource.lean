/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FermatRegularSource

/-! # Integer equations for the constructed regular dyadic hypersurface

Multiplication by the dyadic denominator gives an integer polynomial with the
same zero set. The degree and leading form are preserved, and coefficient
mass is controlled by the binary dyadic exponent.
-/

@[expose] public section
namespace LeanCanny.Geometry.IntegerRegularSource
open MvPolynomial
open LeanCanny.Algebra FermatCriticalHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def exponent (n N b : ℕ) : ℕ :=
  CriticalRegularLevel.exponent (n + 1) N (FermatRegularSource.width n N) b

def scale (n N b : ℕ) : ℤ := 2 ^ exponent n N b

noncomputable def lower (low : MvPolynomial (Fin (n + 1)) ℤ) (N b : ℕ) :
    MvPolynomial (Fin (n + 1)) ℤ := C (scale n N b) * low - 1

def leading (n : ℕ) (a : ℤ) (N b : ℕ) : ℤ := scale n N b * a

theorem leading_ne_zero (a : ℤ) (N b : ℕ) (ha : a ≠ 0) : leading n a N b ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num)) ha

theorem polynomial_eq (low : MvPolynomial (Fin (n + 1)) ℤ) (a : ℤ) (N b : ℕ) :
    polynomial (lower low N b) (leading n a N b) N =
      C (scale n N b) * polynomial low a N - 1 := by
  simp only [polynomial, lower, leading, map_mul]
  ring

theorem lower_degree (low : MvPolynomial (Fin (n + 1)) ℤ) (N b : ℕ)
    (hlow : low.totalDegree < N) : (lower low N b).totalDegree < N := by
  apply (totalDegree_sub _ _).trans_lt
  apply max_lt
  · apply (totalDegree_mul _ _).trans_lt
    simpa only [totalDegree_C, Nat.zero_add] using hlow
  · rw [totalDegree_one]
    omega

theorem mass_le (low : MvPolynomial (Fin (n + 1)) ℤ) (a : ℤ) (N b : ℕ)
    (hp : MvMass.mass (polynomial low a N) ≤ 2 ^ b) :
    MvMass.mass (polynomial (lower low N b) (leading n a N b) N) ≤
      2 ^ (exponent n N b + b + 1) := by
  rw [polynomial_eq]
  apply (MvMass.sub_le _ _).trans
  have hm := (MvMass.mul_le (C (scale n N b)) (polynomial low a N)).trans
    (Nat.mul_le_mul_left _ hp)
  simp only [MvMass.C, scale, Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl, ← pow_add] at hm
  simp only [MvMass.one]
  rw [pow_succ]
  have hpos : 1 ≤ 2 ^ (exponent n N b + b) := Nat.one_le_two_pow
  dsimp only [scale] at *
  omega

/-- Clearing the denominator preserves the actual zero set, over every
rational field extension. -/
theorem eval_eq_zero_iff {K : Type*} [Field K] [Algebra ℚ K]
    (low : MvPolynomial (Fin (n + 1)) ℤ) (a : ℤ) (N b : ℕ) (x : Fin (n + 1) → K) :
    (polynomial (lower low N b) (leading n a N b) N).eval₂ (Int.castRingHom K) x = 0 ↔
      aeval x (polynomial (FermatRegularSource.lower low N b) (a : ℚ) N) = 0 := by
  let : CharZero K := algebraRat.charZero K
  let s : K := (2 : K) ^ exponent n N b
  have hs : s ≠ 0 := pow_ne_zero _ (by norm_num)
  have hscale : (Int.castRingHom K) (scale n N b) = s := by simp [scale, s]
  have hlevel : algebraMap ℚ K (CriticalRegularLevel.level (n + 1) N (FermatRegularSource.width n N) b) = s⁻¹ := by
    simp [CriticalRegularLevel.level, s, exponent]
  have hm : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K := RingHom.ext_int _ _
  have heval : aeval x ((polynomial low a N).map (Int.castRingHom ℚ)) =
      (polynomial low a N).eval₂ (Int.castRingHom K) x := by
    change eval₂ (algebraMap ℚ K) x ((polynomial low a N).map (Int.castRingHom ℚ)) = _
    rw [eval₂_map, hm]
  rw [polynomial_eq, eval₂_sub, eval₂_mul, eval₂_C, eval₂_one, hscale,
    FermatRegularSource.polynomial_eq, map_sub, aeval_C, heval, hlevel]
  constructor
  · intro h
    apply sub_eq_zero.mpr
    apply mul_left_cancel₀ hs
    rw [mul_inv_cancel₀ hs]
    exact sub_eq_zero.mp h
  · intro h
    rw [sub_eq_zero.mp h, mul_inv_cancel₀ hs, sub_self]

theorem regular {K : Type*} [Field K] [Algebra ℚ K]
    (low : MvPolynomial (Fin (n + 1)) ℤ) (a : ℤ) (N b : ℕ)
    (hlow : low.totalDegree < N) (ha : a ≠ 0) (hN : 1 < N)
    (hp : MvMass.mass (polynomial low a N) ≤ 2 ^ b) (x : Fin (n + 1) → K)
    (hx : (polynomial (lower low N b) (leading n a N b) N).eval₂ (Int.castRingHom K) x = 0) :
    ∃ j, (pderiv j (polynomial (lower low N b) (leading n a N b) N)).eval₂ (Int.castRingHom K) x ≠ 0 := by
  let : CharZero K := algebraRat.charZero K
  let s : K := (2 : K) ^ exponent n N b
  have hs : s ≠ 0 := pow_ne_zero _ (by norm_num)
  have hscale : (Int.castRingHom K) (scale n N b) = s := by simp [scale, s]
  have hlevel : algebraMap ℚ K (CriticalRegularLevel.level (n + 1) N (FermatRegularSource.width n N) b) = s⁻¹ := by
    simp [CriticalRegularLevel.level, s, exponent]
  rw [polynomial_eq, eval₂_sub, eval₂_mul, eval₂_C, eval₂_one, hscale] at hx
  have hvalue : (polynomial low a N).eval₂ (Int.castRingHom K) x =
      algebraMap ℚ K (CriticalRegularLevel.level (n + 1) N (FermatRegularSource.width n N) b) := by
    rw [hlevel]
    apply mul_left_cancel₀ hs
    rw [mul_inv_cancel₀ hs]
    exact sub_eq_zero.mp hx
  obtain ⟨j, hj⟩ := CriticalRegularLevel.regular low a N (FermatRegularSource.width n N) b
    hlow ha hN (Nat.lt_size_self _) hp x hvalue
  refine ⟨j, ?_⟩
  rw [polynomial_eq, map_sub, pderiv_one, sub_zero, pderiv_C_mul,
    eval₂_mul, eval₂_C, hscale]
  exact mul_ne_zero hs hj

/-- The integer source has exactly the coefficient-field regularity required
by the generic slice and bounded direction theorems. -/
theorem rational_regular {K : Type*} [Field K] [Algebra ℚ K]
    (low : MvPolynomial (Fin (n + 1)) ℤ) (a : ℤ) (N b : ℕ)
    (hlow : low.totalDegree < N) (ha : a ≠ 0) (hN : 1 < N)
    (hp : MvMass.mass (polynomial low a N) ≤ 2 ^ b) (x : Fin (n + 1) → K)
    (hx : aeval x (polynomial ((lower low N b).map (Int.castRingHom ℚ))
      (leading n a N b : ℚ) N) = 0) :
    ∃ j, aeval x (pderiv j (polynomial ((lower low N b).map (Int.castRingHom ℚ))
      (leading n a N b : ℚ) N)) ≠ 0 := by
  have hm : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K := RingHom.ext_int _ _
  have heval (q : MvPolynomial (Fin (n + 1)) ℤ) :
      aeval x (q.map (Int.castRingHom ℚ)) = q.eval₂ (Int.castRingHom K) x := by
    change eval₂ (algebraMap ℚ K) x (q.map (Int.castRingHom ℚ)) = _
    rw [eval₂_map, hm]
  have hpoly : polynomial ((lower low N b).map (Int.castRingHom ℚ)) (leading n a N b : ℚ) N =
      (polynomial (lower low N b) (leading n a N b) N).map (Int.castRingHom ℚ) := by
    rw [map_polynomial]
    rfl
  rw [hpoly, heval] at hx
  obtain ⟨j, hj⟩ := regular low a N b hlow ha hN hp x hx
  refine ⟨j, ?_⟩
  rwa [hpoly, pderiv_map, heval]

end LeanCanny.Geometry.IntegerRegularSource
