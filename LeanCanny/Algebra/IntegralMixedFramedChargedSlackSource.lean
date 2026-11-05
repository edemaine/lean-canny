/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedSlackRootProperties
public import LeanCanny.Algebra.IntegralMixedFramedPrefixHeight
/-! # Slack integer sources from charged-source family bounds

Integer leaves remain implicit native sources. No explicit integer Term
word or syntax evaluator is required to define or bound these polynomials.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedChargedSlackSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedClearedMatrixBits (family rank)
open IntegralMixedFramedSlackMatrixBits (commonAt sphere regular)
open IntegralMixedFramedSlackMatrixBounds
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def height (P : Parameters) (L F C : List Bool → ℕ) := IntegralMixedFramedStepHeight.familyHeight P L F C
noncomputable def sphereEntryHeight (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C N R : List Bool → ℕ) (key : List Bool) :=
  sphereHeight ((family P D H).birth key) (N key) (rank P D H key) (height P L F C key) (R key)
noncomputable def sphereScalarHeight (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (key : List Bool) := 2*((family P D H).birth key*height P L F C key)
noncomputable def regularEntryHeight (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C N d R Lam K : List Bool → ℕ) (key : List Bool) :=
  regularHeight ((family P D H).birth key) (N key) (rank P D H key) (height P L F C key) (d key) (R key) (Lam key) (K key)
noncomputable def regularScalarHeight (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C d Lam : List Bool → ℕ) (key : List Bool) := Lam key+d key*((family P D H).birth key*height P L F C key)

noncomputable def rawSphereSource (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (N R : List Bool → ℕ) : IntegerPolynomialRootQueriesBits.Source where
  polynomial := IntegralMixedFramedSlackCharacteristicBits.spherePolynomial P D H N R
  degree := rank P D H
  mass key := ScaledCharacteristicIntegerBounds.massHeight (rank P D H key)
    (sphereEntryHeight P D H L F C N R key) (sphereScalarHeight P D H L F C key)
  degree_bound key := (ScaledCharacteristicIntegerBounds.degree (sphere P D H N R key) (commonAt P D H key^2)
    (pow_ne_zero _ (IntegralMixedFramedSlackRootBits.common_ne_zero P D H key))).le
  mass_bound key := ScaledCharacteristicIntegerBounds.mass_bound (sphere P D H N R key) (commonAt P D H key^2)
    (sphereEntryHeight P D H L F C N R key) (sphereScalarHeight P D H L F C key)
    (pow_ne_zero _ (IntegralMixedFramedSlackRootBits.common_ne_zero P D H key))
    (sphere_bound P D H key (height P L F C key) (IntegralMixedFramedStepHeight.family_bank_bounds P D H L F C h key) N R)
    (sphereScalar_bound P D H key (height P L F C key) (IntegralMixedFramedStepHeight.family_bank_bounds P D H L F C h key))

noncomputable def rawRegularSource (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (N d R Lam K : List Bool → ℕ) : IntegerPolynomialRootQueriesBits.Source where
  polynomial := IntegralMixedFramedSlackCharacteristicBits.regularPolynomial P D H N d R Lam K
  degree := rank P D H
  mass key := ScaledCharacteristicIntegerBounds.massHeight (rank P D H key)
    (regularEntryHeight P D H L F C N d R Lam K key) (regularScalarHeight P D H L F C d Lam key)
  degree_bound key := (ScaledCharacteristicIntegerBounds.degree (regular P D H N d R Lam K key)
    ((2 : ℤ)^Lam key*commonAt P D H key^d key) (IntegralMixedFramedSlackRootBits.regularScalar_ne_zero P D H d Lam key)).le
  mass_bound key := ScaledCharacteristicIntegerBounds.mass_bound (regular P D H N d R Lam K key)
    ((2 : ℤ)^Lam key*commonAt P D H key^d key)
    (regularEntryHeight P D H L F C N d R Lam K key) (regularScalarHeight P D H L F C d Lam key)
    (IntegralMixedFramedSlackRootBits.regularScalar_ne_zero P D H d Lam key)
    (regular_bound P D H key (height P L F C key) (IntegralMixedFramedStepHeight.family_bank_bounds P D H L F C h key) N d R Lam K)
    (regularScalar_bound P D H key (height P L F C key) (IntegralMixedFramedStepHeight.family_bank_bounds P D H L F C h key) d Lam)

noncomputable def sphereSource (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (N R : List Bool → ℕ) :=
  IntegerPolynomialExpandSource.source (rawSphereSource P D H L F C h N R) (fun _ => 2)
noncomputable def regularSource (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (N d R Lam K : List Bool → ℕ) :=
  IntegerPolynomialExpandSource.source (rawRegularSource P D H L F C h N d R Lam K) d

theorem sphere_polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (N R : List Bool → ℕ) (key : List Bool) :
    (sphereSource P D H L F C h N R).polynomial key=Polynomial.expand ℤ 2
      (ScaledGradedReductionAnnihilator.polynomial (sphere P D H N R key) (commonAt P D H key^2) 1) := rfl
theorem regular_polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (N d R Lam K : List Bool → ℕ) (key : List Bool) :
    (regularSource P D H L F C h N d R Lam K).polynomial key=Polynomial.expand ℤ (d key)
      (ScaledGradedReductionAnnihilator.polynomial (regular P D H N d R Lam K key)
        ((2 : ℤ)^Lam key*commonAt P D H key^d key) 1) := rfl

theorem sphere_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (N R : List Bool → ℕ) (key : List Bool) :
    ((sphereSource P D H L F C h N R).polynomial key).natDegree=rank P D H key*2 := by
  rw [sphere_polynomial,Polynomial.natDegree_expand,ScaledCharacteristicIntegerBounds.degree]
  exact pow_ne_zero _ (IntegralMixedFramedSlackRootBits.common_ne_zero P D H key)
theorem regular_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (N d R Lam K : List Bool → ℕ) (key : List Bool) :
    ((regularSource P D H L F C h N d R Lam K).polynomial key).natDegree=rank P D H key*d key := by
  rw [regular_polynomial,Polynomial.natDegree_expand,ScaledCharacteristicIntegerBounds.degree]
  exact IntegralMixedFramedSlackRootBits.regularScalar_ne_zero P D H d Lam key

theorem sphere_nonzero (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (N R : List Bool → ℕ) (key : List Bool) :
    (sphereSource P D H L F C h N R).polynomial key≠0 := by
  intro hz
  have HH := congrArg Polynomial.natDegree hz
  rw [sphere_degree,Polynomial.natDegree_zero] at HH
  have HR := IntegralMixedFramedClearedMatrixBits.rank_pos P D H key
  omega
theorem regular_nonzero (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (N d R Lam K : List Bool → ℕ)
    (key : List Bool) (hd : 0<d key) : (regularSource P D H L F C h N d R Lam K).polynomial key≠0 := by
  intro hz
  have HH := congrArg Polynomial.natDegree hz
  rw [regular_degree,Polynomial.natDegree_zero] at HH
  have HP := Nat.mul_pos (IntegralMixedFramedClearedMatrixBits.rank_pos P D H key) hd
  omega

end LeanCanny.Algebra.IntegralMixedFramedChargedSlackSource
