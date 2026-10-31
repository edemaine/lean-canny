/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralDerivativeClearingSpace
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Original derivative heights under additive integer extraction

A nonzero shifted coefficient lies in the original spatial support. Its
selected exponent is below the original block bound. Differentiation thus
adds only that block width to the coefficient-height exponent, without
any multiplicativity assumption on an old matrix-entry extraction.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralDerivativeHeightBounds
open LeanCanny.Encoding LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] {n M : ℕ}

theorem support_bounds (p : MvPolynomial (Fin n) A) (W : ℕ)
    (hs : ∀ e ∈ p.support, ∀ i, e i < 2 ^ W) (selected : Fin n) :
    ∀ e ∈ (MvPolynomial.pderiv selected p).support, ∀ i, e i < 2 ^ W := by
  intro e he i
  have H : p.coeff (e + Finsupp.single selected 1) ≠ 0 := by
    intro hz
    apply MvPolynomial.mem_support_iff.mp he
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
  have HB := hs _ (MvPolynomial.mem_support_iff.mpr H) i
  have HE : e i ≤ (e + Finsupp.single selected 1 : Fin n →₀ ℕ) i := by
    rw [Finsupp.add_apply]
    exact Nat.le_add_right _ _
  exact HE.trans_lt HB

theorem coefficient_height (f : A →+ ℤ) (p : MvPolynomial (Fin n) A) (W C : ℕ)
    (hs : ∀ e ∈ p.support, ∀ i, e i < 2 ^ W)
    (hc : ∀ e, (f (p.coeff e)).natAbs ≤ 2 ^ C) (selected : Fin n) (e : Fin n →₀ ℕ) :
    (f ((MvPolynomial.pderiv selected p).coeff e)).natAbs ≤ 2 ^ (C + W) := by
  by_cases hz : p.coeff (e + Finsupp.single selected 1) = 0
  · rw [MvPolynomial.coeff_pderiv, hz, zero_mul, map_zero, Int.natAbs_zero]
    exact Nat.zero_le _
  · have HB := hs _ (MvPolynomial.mem_support_iff.mpr hz) selected
    have HN : e selected + 1 < 2 ^ W := by
      simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using HB
    have HE : p.coeff (e + Finsupp.single selected 1) * ((e selected + 1 : ℕ) : A) =
        (e selected + 1) • p.coeff (e + Finsupp.single selected 1) := by
      rw [nsmul_eq_mul, mul_comm]
    simp only [Nat.cast_add, Nat.cast_one] at HE
    rw [MvPolynomial.coeff_pderiv, HE, map_nsmul, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
    calc
      _ ≤ 2 ^ W * 2 ^ C := Nat.mul_le_mul HN.le (hc _)
      _ = _ := by rw [← pow_add, Nat.add_comm]

theorem matrix_coefficient_height (b : Module.Basis (Fin M) ℤ A) (p : MvPolynomial (Fin n) A) (W C : ℕ)
    (hs : ∀ e ∈ p.support, ∀ i, e i < 2 ^ W)
    (hc : ∀ e r t, (Algebra.leftMulMatrix b (p.coeff e) r t).natAbs ≤ 2 ^ C)
    (selected : Fin n) (e : Fin n →₀ ℕ) (r t : Fin M) :
    (Algebra.leftMulMatrix b ((MvPolynomial.pderiv selected p).coeff e) r t).natAbs ≤ 2 ^ (C + W) :=
  coefficient_height (IntegralPurePowerReductionBits.coefficientHom b r t) p W C hs (fun e => hc e r t) selected e

end LeanCanny.Algebra.IntegralDerivativeHeightBounds
