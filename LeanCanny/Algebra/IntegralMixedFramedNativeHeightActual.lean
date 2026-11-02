/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNativeHeightValues
public import LeanCanny.Algebra.IntegralMixedFramedHeightIntegerNatural
public import LeanCanny.Algebra.IntegralMixedFullHeightNaturalOutside
/-! # The native scalar-height model is the actual physical or virtual height entry -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedNativeHeightActualBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedOldHeightBits (bankFamily state)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem physical_word (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (hx : get P .slot15 q = 1) :
    IntegralMixedFramedHeightIntegerBits.word P D J q = IntegralMixedPhysicalNativeLowerBits.height P (IntegralMixedFramedScalarCellsBits.physicalFamily P D J) q := by
  by_cases HB : get P .slot8 q < P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1
  · let i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1) := ⟨get P .slot8 q, HB⟩
    have H := IntegralMixedFramedHeightIntegerNaturalBits.physical P D J q i rfl hx
    have HS := IntegralMixedFullHeightNaturalBridge.physical P (IntegralMixedFramedScalarCellsBits.physicalFamily P D J) q i rfl
    unfold IntegralMixedFramedHeightIntegerBits.word
    exact (congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) H).trans HS.symm
  · rw [IntegralMixedFramedHeightIntegerNaturalBits.invalid P D J q HB]
    exact (IntegralMixedFullHeightNaturalBridge.physical_invalid P (IntegralMixedFramedScalarCellsBits.physicalFamily P D J) q HB).symm

theorem virtual_word (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (hx : 2 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) :
    IntegralMixedFramedHeightIntegerBits.word P D J q = IntegralMixedVirtualNativeLowerBits.height P (bankFamily P D J) q := by
  have HN : get P .slot15 q ≠ 1 := by omega
  have HX : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := ⟨by omega, hx.2⟩
  by_cases HB : get P .slot8 q < (bankFamily P D J).ambient (IntegralMixedVirtualTaskBits.saved P q) + 1
  · let i : Fin ((bankFamily P D J).ambient (IntegralMixedVirtualTaskBits.saved P q) + 1) := ⟨get P .slot8 q, HB⟩
    have H := IntegralMixedFramedHeightIntegerNaturalBits.virtual P D J q i rfl HN HX
    have HS := IntegralMixedFullHeightNaturalBridge.virtual P (bankFamily P D J) q i rfl
    unfold IntegralMixedFramedHeightIntegerBits.word
    exact (congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) H).trans HS.symm
  · rw [IntegralMixedFramedHeightIntegerNaturalBits.invalid P D J q HB]
    exact (IntegralMixedFullHeightNaturalBridge.virtual_invalid P (bankFamily P D J) q HB).symm

theorem physical_model (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) (hx : get P .slot15 q = 1) :
    IntegralMixedFramedNativeHeightBits.model P D J q = IntegralMixedPhysicalNativeLowerBits.height P (IntegralMixedFramedScalarCellsBits.physicalFamily P D J) q :=
  (IntegralMixedFramedNativeHeightBits.model_eq P D J q).trans (physical_word P D J q hx)

theorem virtual_model (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) (hx : 2 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) :
    IntegralMixedFramedNativeHeightBits.model P D J q = IntegralMixedVirtualNativeLowerBits.height P (bankFamily P D J) q :=
  (IntegralMixedFramedNativeHeightBits.model_eq P D J q).trans (virtual_word P D J q hx)

end LeanCanny.Algebra.IntegralMixedFramedNativeHeightActualBits
