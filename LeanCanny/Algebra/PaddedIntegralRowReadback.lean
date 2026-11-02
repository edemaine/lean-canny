/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MonicParameterRowCoefficients
public import LeanCanny.Algebra.PaddedIntegralEquationReadback

/-! # Literal powered sampler rows read their actual creating companion

Canonical lower coefficients are the negative entries of the creating
companion. The new coordinate uses its fixed birth power; old coordinates
keep their own powers. No selected leading or regularity premise is used.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralParameterExtension
open IntegralCoordinateBasis FixedWidthPolynomial MonicParameterRows
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] [Nontrivial A] {m B : ℕ}

theorem powered_row_coefficient (b : IntegralCoordinateBasis A m (2^B))
    (p : Polynomial A) (d : ℕ) (w : Fin m→ℕ) (hw : ∀ i,0<w i)
    (W : ℕ) (hW : 0<W) (r : Fin (count m B)) (k : Fin (2^B)) :
    (MonicParameterRows.row (equation b p d) (2^B) w W).coeff
      (appendExponent (CoordinatePowerSubstitution.exponent w (vector m B r)) (k.val*W)) =
      -Algebra.leftMulMatrix (coordinateBasis b p d).finBasis (AdjoinRoot.root _)
        (pairIndex m B (r,k)) (pairIndex m B (zeroFin m B,lastDigit B)) := by
  have HE := equation_monic b p d (Nat.two_pow_pos B)
  rw [coefficient_monic_row_powers (equation b p d) (2^B) HE.1 HE.2 w hw W hW _ k.val k.isLt]
  exact equation_coefficient_companion b p d r k

theorem powered_row_top (b : IntegralCoordinateBasis A m (2^B))
    (p : Polynomial A) (d : ℕ) (w : Fin m→ℕ) (W : ℕ) (hW : 0<W) :
    (MonicParameterRows.row (equation b p d) (2^B) w W).coeff
      (appendExponent (0 : Fin m→₀ℕ) (2^B*W))=1 := by
  have HE := equation_monic b p d (Nat.two_pow_pos B)
  rw [coefficient_monic_row (equation b p d) (2^B) HE.1 HE.2 w W hW]
  simp only [ite_true,lt_self_iff_false,ite_false,add_zero]

theorem powered_row_above (b : IntegralCoordinateBasis A m (2^B))
    (p : Polynomial A) (d : ℕ) (w : Fin m→ℕ) (W : ℕ) (hW : 0<W)
    (e : Fin m→₀ℕ) (k : ℕ) (hk : 2^B<k) :
    (MonicParameterRows.row (equation b p d) (2^B) w W).coeff (appendExponent e (k*W))=0 := by
  have HE := equation_monic b p d (Nat.two_pow_pos B)
  rw [coefficient_monic_row (equation b p d) (2^B) HE.1 HE.2 w W hW]
  rw [ite_eq_right (by omega : k≠2^B),ite_eq_right (by omega : ¬k<2^B),add_zero]

omit [Nontrivial A] in
theorem powered_row_off_power (b : IntegralCoordinateBasis A m (2^B))
    (p : Polynomial A) (d : ℕ) (w : Fin m→ℕ) (W : ℕ)
    (e : Fin m→₀ℕ) (l : ℕ) (hl : ¬W∣l) :
    (MonicParameterRows.row (equation b p d) (2^B) w W).coeff (appendExponent e l)=0 :=
  coefficient_off_power (equation b p d) (2^B) w W e l hl

end LeanCanny.Algebra.PaddedIntegralParameterExtension
