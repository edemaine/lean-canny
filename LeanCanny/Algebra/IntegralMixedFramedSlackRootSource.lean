/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedSlackCharacteristicCoefficients
public import LeanCanny.Algebra.IntegralMixedFramedSlackMatrixBounds
public import LeanCanny.Algebra.ScaledCharacteristicIntegerBounds
public import LeanCanny.Algebra.IntegerPolynomialExpandSpace
/-! # Native integer sources for the two marked slack coordinates -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedSlackRootBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedClearedMatrixBits (family rank)
open IntegralMixedFramedSlackMatrixBits (commonAt sphere regular)
open IntegralMixedFramedSlackMatrixBounds
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def height (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H) := IntegralMixedFramedStepHeight.familyHeight P s.nodes s.factor s.seed
noncomputable def sphereEntryHeight (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H) (n R : List Bool → ℕ) (key : List Bool) :=
  sphereHeight ((family P D H).birth key) (n key) (rank P D H key) (height P D H s key) (R key)
noncomputable def sphereScalarHeight (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H) (key : List Bool) := 2*((family P D H).birth key*height P D H s key)
noncomputable def regularEntryHeight (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H) (n d R L K : List Bool → ℕ) (key : List Bool) :=
  regularHeight ((family P D H).birth key) (n key) (rank P D H key) (height P D H s key) (d key) (R key) (L key) (K key)
noncomputable def regularScalarHeight (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H) (d L : List Bool → ℕ) (key : List Bool) :=
  L key+d key*((family P D H).birth key*height P D H s key)

theorem common_ne_zero (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    commonAt P D H key≠0 := IntegralMixedHistory.commonDenominator_ne_zero ((family P D H).state key)

theorem regularScalar_ne_zero (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (d L : List Bool → ℕ) (key : List Bool) : (2 : ℤ)^L key*commonAt P D H key^d key≠0 :=
  mul_ne_zero (pow_ne_zero _ (by decide : (2 : ℤ)≠0)) (pow_ne_zero _ (common_ne_zero P D H key))

noncomputable def rawSphereSource (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (n R : List Bool → ℕ) : IntegerPolynomialRootQueriesBits.Source where
  polynomial := IntegralMixedFramedSlackCharacteristicBits.spherePolynomial P D H n R
  degree := rank P D H
  mass key := ScaledCharacteristicIntegerBounds.massHeight (rank P D H key)
    (sphereEntryHeight P D H s n R key) (sphereScalarHeight P D H s key)
  degree_bound key := (ScaledCharacteristicIntegerBounds.degree (sphere P D H n R key) (commonAt P D H key^2)
    (pow_ne_zero _ (common_ne_zero P D H key))).le
  mass_bound key := ScaledCharacteristicIntegerBounds.mass_bound (sphere P D H n R key) (commonAt P D H key^2)
    (sphereEntryHeight P D H s n R key) (sphereScalarHeight P D H s key) (pow_ne_zero _ (common_ne_zero P D H key))
    (sphere_bound P D H key (height P D H s key) (IntegralMixedFramedStepHeight.family_bank_bounds P D H s.nodes s.factor s.seed hs key) n R)
    (sphereScalar_bound P D H key (height P D H s key) (IntegralMixedFramedStepHeight.family_bank_bounds P D H s.nodes s.factor s.seed hs key))

noncomputable def rawRegularSource (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (n d R L K : List Bool → ℕ) : IntegerPolynomialRootQueriesBits.Source where
  polynomial := IntegralMixedFramedSlackCharacteristicBits.regularPolynomial P D H n d R L K
  degree := rank P D H
  mass key := ScaledCharacteristicIntegerBounds.massHeight (rank P D H key)
    (regularEntryHeight P D H s n d R L K key) (regularScalarHeight P D H s d L key)
  degree_bound key := (ScaledCharacteristicIntegerBounds.degree (regular P D H n d R L K key)
    ((2 : ℤ)^L key*commonAt P D H key^d key) (regularScalar_ne_zero P D H d L key)).le
  mass_bound key := ScaledCharacteristicIntegerBounds.mass_bound (regular P D H n d R L K key)
    ((2 : ℤ)^L key*commonAt P D H key^d key) (regularEntryHeight P D H s n d R L K key)
    (regularScalarHeight P D H s d L key) (regularScalar_ne_zero P D H d L key)
    (regular_bound P D H key (height P D H s key) (IntegralMixedFramedStepHeight.family_bank_bounds P D H s.nodes s.factor s.seed hs key) n d R L K)
    (regularScalar_bound P D H key (height P D H s key) (IntegralMixedFramedStepHeight.family_bank_bounds P D H s.nodes s.factor s.seed hs key) d L)

noncomputable def sphereSource (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (n R : List Bool → ℕ) :=
  IntegerPolynomialExpandSource.source (rawSphereSource P D H s hs n R) (fun _=>2)
noncomputable def regularSource (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (n d R L K : List Bool → ℕ) :=
  IntegerPolynomialExpandSource.source (rawRegularSource P D H s hs n d R L K) d

end LeanCanny.Algebra.IntegralMixedFramedSlackRootBits
