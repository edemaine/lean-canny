/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CriticalValueBounds
public import LeanCanny.Algebra.EffectiveInfinitesimalSign

/-! # An explicit dyadic level avoiding every complex critical value

The integer critical-value annihilator has bounded coefficient mass. A dyadic
below that mass bound avoids its nonzero roots, including over extension fields.
-/

@[expose] public section
namespace LeanCanny.Geometry.CriticalRegularLevel
open MvPolynomial
open LeanCanny.Algebra
open scoped Classical

variable {n : ℕ}

def coefficientBits (n D W b : ℕ) : ℕ :=
  let C := FixedWidthPolynomial.count (n + 2) W
  C.size * C + C * (b + D.size + 1 + 3) + 1

def massBits (n D W b : ℕ) : ℕ :=
  coefficientBits n D W b + (FixedWidthPolynomial.count (n + 2) W + 1).size

def exponent (n D W b : ℕ) : ℕ := massBits n D W b + 1

def level (n D W b : ℕ) : ℚ := ((2 : ℚ) ^ exponent n D W b)⁻¹

private theorem size_add_le (a b : ℕ) : (a + b).size ≤ a.size + b.size + 1 := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ (a.size + b.size) := (Nat.lt_size_self a).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hb : b < 2 ^ (a.size + b.size) := (Nat.lt_size_self b).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  rw [pow_succ]
  omega

private theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left a (Nat.lt_size_self b).le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity))

/-- The dyadic exponent itself needs only polynomially many bits, even when
the source degree and coefficient-mass exponent are given in binary. -/
theorem exponent_size_le (n D W b : ℕ) :
    (exponent n D W b).size ≤ 4 * ((n + 2) * W) + b.size + D.size + 24 := by
  let C := FixedWidthPolynomial.count (n + 2) W
  have hsmall (z : ℕ) : z.size ≤ z := Nat.size_le.mpr Nat.lt_two_pow_self
  have hC : C.size = (n + 2) * W + 1 := by
    simp only [C, FixedWidthPolynomial.count, ← pow_mul, Nat.size_pow, Nat.mul_comm W]
  have h1 := size_mul_le C.size C
  have h2 := size_add_le b D.size
  have h3 := size_add_le (b + D.size) 1
  have h4 := size_add_le (b + D.size + 1) 3
  have h5 := size_mul_le C (b + D.size + 1 + 3)
  have h6 := size_add_le (C.size * C) (C * (b + D.size + 1 + 3))
  have h7 := size_add_le (C.size * C + C * (b + D.size + 1 + 3)) 1
  have h8 := size_add_le C 1
  have h9 := size_add_le (coefficientBits n D W b) (C + 1).size
  have h10 := size_add_le (massBits n D W b) 1
  have hsC := hsmall C.size
  have hsD := hsmall D.size
  have hsC1 := hsmall (C + 1).size
  norm_num only [show (1 : ℕ).size = 1 from rfl, show (3 : ℕ).size = 2 from rfl] at *
  dsimp only [coefficientBits, massBits, exponent, C] at *
  omega

theorem mass_le (p : MvPolynomial (Fin n) ℤ) (D W b : ℕ)
    (hD : p.totalDegree ≤ D) (hp : MvMass.mass p ≤ 2 ^ b) :
    coefficientMass (CriticalValueBounds.polynomial p D W) ≤ 2 ^ massBits n D W b := by
  let C := FixedWidthPolynomial.count (n + 2) W
  have hc (k : ℕ) :
      ((CriticalValueBounds.polynomial p D W).coeff k).natAbs ≤ 2 ^ coefficientBits n D W b := by
    have hs := CriticalValueBounds.coefficient_size_le p D W (b + D.size + 1)
      (CriticalValueSystem.coefficient_bound p D b hD hp) k
    exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hs)
  apply (coefficientMass_le _ C _ (CriticalValueBounds.degree_le p D W) hc).trans
  calc
    (C + 1) * 2 ^ coefficientBits n D W b ≤
        2 ^ (C + 1).size * 2 ^ coefficientBits n D W b :=
      Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
    _ = 2 ^ massBits n D W b := by rw [← pow_add, Nat.add_comm]; rfl

theorem eval_level_ne_zero_real (p : MvPolynomial (Fin n) ℤ) (D W b : ℕ)
    (hD : p.totalDegree ≤ D) (hp : MvMass.mass p ≤ 2 ^ b) :
    (CriticalValueBounds.polynomial p D W).eval₂ (Int.castRingHom ℝ)
      (InfinitesimalSign.dyadic (exponent n D W b)) ≠ 0 := by
  have hs := InfinitesimalSign.integer_sign_eval_dyadic _ (massBits n D W b)
    (exponent n D W b) (mass_le p D W b hD hp) (by simp [exponent])
  intro hz
  rw [hz, sign_zero] at hs
  exact (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (CriticalValueBounds.ne_zero p D W))
    (sign_eq_zero_iff.mp hs.symm)

theorem eval_level_ne_zero (p : MvPolynomial (Fin n) ℤ) (D W b : ℕ)
    (hD : p.totalDegree ≤ D) (hp : MvMass.mass p ≤ 2 ^ b) :
    (CriticalValueBounds.polynomial p D W).eval₂ (Int.castRingHom ℚ) (level n D W b) ≠ 0 := by
  intro hz
  apply eval_level_ne_zero_real p D W b hD hp
  have he := congrArg (algebraMap ℚ ℝ) hz
  rw [Polynomial.hom_eval₂, map_zero] at he
  have hm : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ :=
    RingHom.ext_int _ _
  rw [hm] at he
  simpa [level, InfinitesimalSign.dyadic] using he

theorem level_pos (n D W b : ℕ) : 0 < level n D W b := by
  unfold level
  positivity

/-- Every root on the selected rational level is regular, over every field
extension of the rationals. -/
theorem regular {K : Type*} [Field K] [Algebra ℚ K]
    (low : MvPolynomial (Fin (n + 1)) ℤ) (a : ℤ) (N W b : ℕ)
    (hlow : low.totalDegree < N) (ha : a ≠ 0) (hN : 1 < N)
    (hW : Macaulay.level (AffineCoordinateSystem.degrees
      (CriticalValueSystem.degrees (n + 1) N)) < 2 ^ W)
    (hp : MvMass.mass (FermatCriticalHomogenization.polynomial low a N) ≤ 2 ^ b)
    (x : Fin (n + 1) → K)
    (hx : (FermatCriticalHomogenization.polynomial low a N).eval₂ (Int.castRingHom K) x =
      algebraMap ℚ K (level (n + 1) N W b)) :
    ∃ j, (pderiv j (FermatCriticalHomogenization.polynomial low a N)).eval₂ (Int.castRingHom K) x ≠ 0 := by
  let : CharZero K := algebraRat.charZero K
  let p := FermatCriticalHomogenization.polynomial low a N
  have hD : p.totalDegree ≤ N := FermatCriticalHomogenization.polynomial_degree low a N hlow
  have hnonzero := eval_level_ne_zero p N W b hD hp
  by_contra hn
  have hgrad (j : Fin (n + 1)) : (pderiv j p).eval₂ (Int.castRingHom K) x = 0 := by
    by_contra hj
    exact hn ⟨j, hj⟩
  have he := CriticalValueBounds.eval_eq_zero_fermat_extension (Int.castRingHom K)
    low a N W hlow (Int.cast_ne_zero.mpr ha) hN hW x hgrad
  rw [hx] at he
  apply hnonzero
  apply (algebraMap ℚ K).injective
  rw [map_zero, Polynomial.hom_eval₂]
  have hm : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K :=
    RingHom.ext_int _ _
  rw [hm]
  exact he

end LeanCanny.Geometry.CriticalRegularLevel
