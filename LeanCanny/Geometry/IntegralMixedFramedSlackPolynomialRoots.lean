/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFramedSlackJointInterpretation
public import LeanCanny.Algebra.ScaledGradedReductionAnnihilator
public import Mathlib.Algebra.Polynomial.Expand

/-! # The prescribed real slacks are roots of the actual integer polynomials

The two expanded characteristic polynomials use multiplication matrices on
one old algebra. Their roots follow from the same interpreting hom, without
selecting unrelated scalar roots.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedSlackPolynomialRoots
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedSlackMatrixBits
open IntegralMixedFramedClearedMatrixBits (family rank)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem root_of_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (φ : ((family P D H).state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (a : ((family P D H).state key).sampler.scalarPrefix.carrier)
    (M : Matrix (Fin (rank P D H key)) (Fin (rank P D H key)) ℤ)
    (hM : M=Algebra.leftMulMatrix ((family P D H).state key).sampler.scalarPrefix.basis.finBasis a)
    (c : ℤ) (e : ℕ) (z : ℝ) (hz : φ a=(c : ℝ)*z^e) :
    (Polynomial.expand ℤ e (ScaledGradedReductionAnnihilator.polynomial M c 1)).eval₂ (Int.castRingHom ℝ) z=0 := by
  simp only [Polynomial.expand_eq_comp_X_pow,Polynomial.eval₂_comp,Polynomial.eval₂_X_pow]
  apply ScaledGradedReductionAnnihilator.root M c 1 (Int.castRingHom ℝ) (z^e)
  rw [pow_one]
  simp only [Int.coe_castRingHom]
  rw [←hz,hM]
  exact IntegralParameterInverse.charpoly_root ((family P D H).state key).sampler.scalarPrefix.basis.finBasis a φ

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (N R : List Bool→ℕ) (key : List Bool)
  (φ : ((family P D H).state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
  (q : MvPolynomial (Fin (N key)) ℤ) (a : BoundedZeroSource.Bounded q (R key))
  (ha : ∀ i : Fin (N key),φ (elementAt P D H key (N key-i.val))=(commonAt P D H key : ℝ)*a.val i)
include ha

theorem sphere_root :
    (Polynomial.expand ℤ 2 (ScaledGradedReductionAnnihilator.polynomial (sphere P D H N R key)
      (commonAt P D H key^2) 1)).eval₂ (Int.castRingHom ℝ) (BoundedRegularSource.sphereSlack q (R key) a)=0 := by
  apply root_of_value P D H key φ (sphereElement P D H N R key) _ (sphere_algebra P D H N R key)
  simpa only [Int.cast_pow] using IntegralMixedFramedSlackInterpretation.sphere_marked P D H N R key φ q a ha

theorem regular_root (E b : ℕ) (d L K : List Bool→ℕ) (hd : d key=BoundedZeroSource.powerDegree E)
    (hL : L key=BoundedRegularSource.regularizationExponent (N key) E b (R key))
    (hK : K key=BoundedZeroSource.penaltyExponent (N key) E (R key)) :
    (Polynomial.expand ℤ (d key) (ScaledGradedReductionAnnihilator.polynomial (regular P D H N d R L K key)
      ((2 : ℤ)^L key*commonAt P D H key^d key) 1)).eval₂ (Int.castRingHom ℝ)
        (BoundedRegularSource.regularSlack q E b (R key) a).re=0 := by
  apply root_of_value P D H key φ (regularElement P D H N d R L K key) _ (regular_algebra P D H N d R L K key)
  simpa only [Int.cast_mul,Int.cast_pow,Int.cast_ofNat] using
    IntegralMixedFramedSlackInterpretation.regular_marked P D H N R key φ q E b a ha d L K hd hL hK

end LeanCanny.Geometry.IntegralMixedFramedSlackPolynomialRoots
