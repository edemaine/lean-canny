/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedClearedPowerSum
public import LeanCanny.Algebra.IntegralMixedFramedSlackScalars
/-! # The two marked-slack matrices stay over the same old algebra

Both matrices are ordinary multiplication matrices on one actual old prefix.
No new algebra extension is used while forming their characteristic sources.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedSlackMatrixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedClearedMatrixBits (family rank matrix Active)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def commonAt (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :=
  IntegralMixedHistory.commonDenominator ((family P D H).state key)
noncomputable def sphereCoefficient (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (R : List Bool → ℕ) (key : List Bool) : ℤ := commonAt P D H key^2*((2 : ℤ)^R key)^2
noncomputable def regularCoefficient (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (d L K : List Bool → ℕ) (key : List Bool) : ℤ :=
  (2 : ℤ)^L key*commonAt P D H key^d key*(2 : ℤ)^K key+commonAt P D H key^d key

noncomputable def sphere (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N R : List Bool → ℕ) (key : List Bool) : Matrix (Fin (rank P D H key)) (Fin (rank P D H key)) ℤ :=
  (sphereCoefficient P D H R key : Matrix _ _ ℤ)-
    IntegralMixedFramedClearedPowerSumBits.matrixSum P D H N (fun _=>2) key

noncomputable def regular (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N d R L K : List Bool → ℕ) (key : List Bool) : Matrix (Fin (rank P D H key)) (Fin (rank P D H key)) ℤ :=
  (regularCoefficient P D H d L K key : Matrix _ _ ℤ)-
    (2 : ℤ)^L key • IntegralMixedFramedClearedPowerSumBits.matrixSum P D H N d key-
    (2 : ℤ)^L key • sphere P D H N R key^(d key/2)

noncomputable def elementAt (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : ℕ) : ((family P D H).state key).sampler.scalarPrefix.carrier :=
  if Active P key then if hi : i<(family P D H).birth key then
    IntegralMixedHistory.cleared ((family P D H).state key) ⟨i,hi⟩ else 0 else 0

theorem matrix_algebra (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : ℕ) : matrix P D H key i=
      Algebra.leftMulMatrix ((family P D H).state key).sampler.scalarPrefix.basis.finBasis (elementAt P D H key i) := by
  funext r t
  by_cases ha : Active P key
  · rw [matrix,ite_eq_left ha,elementAt,ite_eq_left ha]
    by_cases hi : i<(family P D H).birth key
    · rw [dite_eq_left hi]
      unfold IntegralMixedFramedOldHeightBankBits.sourceEntry
      rw [dite_eq_left ⟨hi,r.isLt,t.isLt⟩]
      rfl
    · rw [dite_eq_right hi,map_zero]
      unfold IntegralMixedFramedOldHeightBankBits.sourceEntry
      rw [dite_eq_right (fun hv=>hi hv.1)]
      rfl
  · rw [matrix,ite_eq_right ha,elementAt,ite_eq_right ha,map_zero]
    rfl

noncomputable def sphereElement (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N R : List Bool → ℕ) (key : List Bool) : ((family P D H).state key).sampler.scalarPrefix.carrier :=
  (sphereCoefficient P D H R key : ((family P D H).state key).sampler.scalarPrefix.carrier)-
    ∑ i ∈ Finset.range (N key), elementAt P D H key (N key-i)^2

noncomputable def regularElement (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N d R L K : List Bool → ℕ) (key : List Bool) : ((family P D H).state key).sampler.scalarPrefix.carrier :=
  (regularCoefficient P D H d L K key : ((family P D H).state key).sampler.scalarPrefix.carrier)-
    (2 : ℤ)^L key • (∑ i ∈ Finset.range (N key), elementAt P D H key (N key-i)^d key)-
    (2 : ℤ)^L key • sphereElement P D H N R key^(d key/2)

theorem sum_algebra (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N e : List Bool → ℕ) (key : List Bool) :
    IntegralMixedFramedClearedPowerSumBits.matrixSum P D H N e key=
      Algebra.leftMulMatrix ((family P D H).state key).sampler.scalarPrefix.basis.finBasis
        (∑ i ∈ Finset.range (N key), elementAt P D H key (N key-i)^e key) := by
  rw [IntegralMixedFramedClearedPowerSumBits.matrixSum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_pow,←matrix_algebra]

theorem sphere_algebra (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N R : List Bool → ℕ) (key : List Bool) : sphere P D H N R key=
      Algebra.leftMulMatrix ((family P D H).state key).sampler.scalarPrefix.basis.finBasis (sphereElement P D H N R key) := by
  rw [sphere,sphereElement,map_sub,map_intCast,←sum_algebra P D H N (fun _=>2) key]

theorem regular_algebra (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N d R L K : List Bool → ℕ) (key : List Bool) : regular P D H N d R L K key=
      Algebra.leftMulMatrix ((family P D H).state key).sampler.scalarPrefix.basis.finBasis (regularElement P D H N d R L K key) := by
  rw [regular,regularElement,map_sub,map_sub,map_intCast,map_zsmul,map_zsmul,map_pow,←sum_algebra P D H N d key,←sphere_algebra P D H N R key]

end LeanCanny.Algebra.IntegralMixedFramedSlackMatrixBits
