/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedSlackRootSpace
/-! # The slack sources are nonzero with original-rank degree bounds -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedSlackRootBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedClearedMatrixBits (rank)
open IntegralMixedFramedSlackMatrixBits (commonAt sphere regular)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem sphere_polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (n R : List Bool → ℕ) (key : List Bool) :
    (sphereSource P D H s hs n R).polynomial key=Polynomial.expand ℤ 2
      (ScaledGradedReductionAnnihilator.polynomial (sphere P D H n R key) (commonAt P D H key^2) 1) := rfl

theorem regular_polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (n d R L K : List Bool → ℕ) (key : List Bool) :
    (regularSource P D H s hs n d R L K).polynomial key=Polynomial.expand ℤ (d key)
      (ScaledGradedReductionAnnihilator.polynomial (regular P D H n d R L K key) ((2 : ℤ)^L key*commonAt P D H key^d key) 1) := rfl

theorem sphere_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (n R : List Bool → ℕ) (key : List Bool) :
    ((sphereSource P D H s hs n R).polynomial key).natDegree=rank P D H key*2 := by
  rw [sphere_polynomial,Polynomial.natDegree_expand,ScaledCharacteristicIntegerBounds.degree]
  exact pow_ne_zero _ (common_ne_zero P D H key)

theorem regular_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (n d R L K : List Bool → ℕ) (key : List Bool) :
    ((regularSource P D H s hs n d R L K).polynomial key).natDegree=rank P D H key*d key := by
  rw [regular_polynomial,Polynomial.natDegree_expand,ScaledCharacteristicIntegerBounds.degree]
  exact regularScalar_ne_zero P D H d L key

theorem sphere_nonzero (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (n R : List Bool → ℕ) (key : List Bool) :
    (sphereSource P D H s hs n R).polynomial key≠0 := by
  intro h
  have HH := congrArg Polynomial.natDegree h
  rw [sphere_degree,Polynomial.natDegree_zero] at HH
  have HR := IntegralMixedFramedClearedMatrixBits.rank_pos P D H key
  omega

theorem regular_nonzero (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (n d R L K : List Bool → ℕ)
    (key : List Bool) (hd : 0<d key) : (regularSource P D H s hs n d R L K).polynomial key≠0 := by
  intro h
  have HH := congrArg Polynomial.natDegree h
  rw [regular_degree,Polynomial.natDegree_zero] at HH
  have HP := Nat.mul_pos (IntegralMixedFramedClearedMatrixBits.rank_pos P D H key) hd
  omega

end LeanCanny.Algebra.IntegralMixedFramedSlackRootBits
