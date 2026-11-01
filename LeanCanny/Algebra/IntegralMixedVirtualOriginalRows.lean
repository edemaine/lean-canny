/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedVirtualSweepSource
public import LeanCanny.Algebra.IntegralMixedSweepRows

/-! # Actual original Gram rows from virtual low rows and Fermat terms

The value test uses the full original equation at the objective and the
full original derivatives elsewhere. The native virtual lower readers
omit the free Fermat monomials. These identities restore precisely those
terms, with integer scale `a*Q^D` for the equation and `a*Q^D*D` for a
derivative. No division by the degree is used modulo the caller modulus.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualOriginalRows
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial Polynomial MvPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource IntegralMixedVirtualSweepSource
open scoped Classical

noncomputable def originalScale (F : Family) (q : List Bool) : ℤ :=
  (F.spatial q).leading * denominator F q ^ (F.spatial q).degree

noncomputable def row (F : Family) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) :
    MvPolynomial (Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) (Coefficient F q) :=
  (IntegralMixedSweepRows.row (F.state q) (F.birth_bound q) (F.rule q) j).map
    (AdjoinRoot.mk (Polynomial.X ^ (2 ^ F.width q)))

theorem row_specialization (F : Family) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) :
    row F q j = ClearedCoordinateBlock.specialize (F.spatial q).degree (denominator F q : Coefficient F q)
      (height F q) (F.rule q).critical.offset.val (F.ambient q - (F.rule q).critical.offset.val + 1)
      ((IntegralMixedSweepRows.integerRow (F.spatial q) (F.rule q) j).map (Int.castRingHom (Coefficient F q))) := by
  unfold row IntegralMixedSweepRows.row
  rw [ClearedCoordinateMap.specialize, MvPolynomial.map_map]
  simp only [map_intCast]
  congr 1

noncomputable def frozen (F : Family) (I : Indices F) (q : List Bool) :
    MvPolynomial (Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) (Coefficient F q) :=
  (euler F I).toGradient.toFrozen.lowerPolynomial q

noncomputable def gradient (F : Family) (I : Indices F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) :
    MvPolynomial (Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) (Coefficient F q) :=
  IntegralCriticalGradientBits.polynomial (euler F I).toGradient q j

theorem frozen_lower (F : Family) (I : Indices F) (q : List Bool) :
    frozen F I q =
      ClearedCoordinateBlock.lower (F.spatial q).degree (denominator F q : Coefficient F q)
        (height F q) (F.rule q).critical.offset.val (F.ambient q - (F.rule q).critical.offset.val + 1)
        ((F.spatial q).low.map (Int.castRingHom (Coefficient F q)))
        ((F.spatial q).leading : Coefficient F q) := rfl

theorem gradient_lower (F : Family) (I : Indices F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) :
    gradient F I q j =
      ClearedCoordinateCritical.gradientLower (F.spatial q).degree (denominator F q : Coefficient F q)
        (height F q) (F.rule q).critical.offset.val (fit (F.rule q)).le
        ((F.spatial q).low.map (Int.castRingHom (Coefficient F q))) j := rfl

theorem frozen_degree (F : Family) (I : Indices F) (q : List Bool) :
    (frozen F I q).totalDegree < (F.spatial q).degree := by
  rw [frozen_lower]
  exact ClearedCoordinateBlock.lower_degree _ _ _ _ _ _ _
    ((PolynomialMapDegree.degree_le _ _).trans_lt (F.spatial q).low_degree)

theorem gradient_degree (F : Family) (I : Indices F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) :
    (gradient F I q j).totalDegree < (F.spatial q).degree - 1 := by
  rw [gradient_lower]
  exact ClearedCoordinateCritical.gradient_degree _ _ _ _ _ _ (F.spatial q).degree_two
    ((PolynomialMapDegree.degree_le _ _).trans_lt (F.spatial q).low_degree) j

theorem full_row (F : Family) (I : Indices F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) :
    row F q j = if j = objective (F.rule q) then
      FermatCriticalHomogenization.polynomial (frozen F I q)
        (originalScale F q : Coefficient F q) (F.spatial q).degree
    else PurePowerEulerReduction.gradient (originalScale F q : Coefficient F q) (F.spatial q).degree
      (gradient F I q) j := by
  rw [row_specialization]
  have HS : (originalScale F q : Coefficient F q) =
      ((F.spatial q).leading : Coefficient F q) * (denominator F q : Coefficient F q) ^ (F.spatial q).degree := by
    simp only [originalScale, Int.cast_mul, Int.cast_pow]
  rw [HS]
  by_cases H : j = objective (F.rule q)
  · rw [ite_eq_left H, frozen_lower, IntegralMixedSweepRows.integerRow, ite_eq_left H,
      FermatCriticalHomogenization.map_polynomial, Int.coe_castRingHom]
    exact ClearedCoordinateBlock.source _ _ _ _ _ _ (fit (F.rule q)).le
  · rw [ite_eq_right H, IntegralMixedSweepRows.integerRow, ite_eq_right H, ← MvPolynomial.pderiv_map,
      FermatCriticalHomogenization.map_polynomial, Int.coe_castRingHom]
    have HG : gradient F I q =
        ClearedCoordinateCritical.gradientLower (F.spatial q).degree (denominator F q : Coefficient F q)
          (height F q) (F.rule q).critical.offset.val (fit (F.rule q)).le
          ((F.spatial q).low.map (Int.castRingHom (Coefficient F q))) := by
      funext k
      exact gradient_lower F I q k
    rw [HG]
    exact ClearedCoordinateCritical.gradient_eq _ _ _ _ (fit (F.rule q)).le _ _ j

theorem equation_coefficient (F : Family) (I : Indices F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) (hj : j = objective (F.rule q))
    (e : Fin (F.ambient q - (F.rule q).critical.offset.val + 1) →₀ ℕ) :
    (row F q j).coeff e = (frozen F I q).coeff e + (originalScale F q : Coefficient F q) *
      ∑ k, if Finsupp.single k (F.spatial q).degree = e then 1 else 0 := by
  rw [full_row F I q j, ite_eq_left hj]
  simp only [FermatCriticalHomogenization.polynomial, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_X_pow]

theorem derivative_coefficient (F : Family) (I : Indices F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) (hj : j ≠ objective (F.rule q))
    (e : Fin (F.ambient q - (F.rule q).critical.offset.val + 1) →₀ ℕ) :
    (row F q j).coeff e = (gradient F I q j).coeff e +
      if Finsupp.single j ((F.spatial q).degree - 1) = e then
        ((originalScale F q * (F.spatial q).degree : ℤ) : Coefficient F q) else 0 := by
  rw [full_row F I q j, ite_eq_right hj]
  simp only [PurePowerEulerReduction.gradient, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X_pow, Int.cast_mul, Int.cast_natCast]
  split_ifs <;> ring

end LeanCanny.Algebra.IntegralMixedVirtualOriginalRows
