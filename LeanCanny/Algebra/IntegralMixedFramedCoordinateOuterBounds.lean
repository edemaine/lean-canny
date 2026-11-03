/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiHead
/-! # Native declared outer bounds remain valid through the actual head pipeline

These are bounds on the actual stored test polynomial for every input. They
do not identify a truncation with the full annihilator after selection.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateOuterBounds
open LeanCanny.Encoding IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

private theorem lift_outer_degree {A : Type*} [CommRing A] {m : ℕ}
    (p : Polynomial (Polynomial A)) (rep : A→MvPolynomial (Fin m) ℤ) (d e : ℕ) :
    (SelectedMultivariatePolynomialLift.lift p rep d e).natDegree≤d :=by
  unfold SelectedMultivariatePolynomialLift.lift
  apply Polynomial.natDegree_map_le.trans
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro y hy
  rw [SelectedParameterPolynomialLift.lift,SelectedPolynomialLift.coefficient,ite_eq_right (by omega)]

theorem packed_outer_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (d e : List Bool→ℕ) (c : List Bool) :
    (IntegralMixedFramedCoordinatePackedBits.head P D H parent d e c).natDegree≤d c :=by
  unfold IntegralMixedFramedCoordinatePackedBits.head
  exact lift_outer_degree _ _ _ _

theorem terminal_outer_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d e : List Bool→ℕ) (c : List Bool) :
    (IntegralMixedFramedTerminalCoordinateHeadBits.polynomial P D H parent terminal d e c).natDegree≤d c :=by
  unfold IntegralMixedFramedTerminalCoordinateHeadBits.polynomial
  split_ifs
  · unfold IntegralMixedFramedTerminalCoordinateHeadBits.castHead
    apply Polynomial.natDegree_map_le.trans
    unfold IntegralMixedFramedCoordinateParameterSuffixBits.polynomial FixedWidthBivariateParameterSuffixBits.head
    apply Polynomial.natDegree_map_le.trans
    unfold IntegralMixedFramedCoordinatePackedBits.guardedHead
    split_ifs
    · exact packed_outer_degree P D H parent d e c
    · simp
  · simp

theorem shifted_outer_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (parent terminal : List Bool→List Bool) (d e index : List Bool→ℕ) (negative : Bool) (c : List Bool) :
    (IntegralMixedFramedTerminalTarskiHeadBits.head P D H L F C hs parent terminal d e index negative c).natDegree≤d c :=
  (RationalMonomialBivariateShift.outer_degree _ negative _ _ c).trans (terminal_outer_degree P D H parent terminal d e c)

end LeanCanny.Algebra.IntegralMixedFramedCoordinateOuterBounds
