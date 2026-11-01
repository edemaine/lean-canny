/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNativeHeightValues
public import LeanCanny.Algebra.IntegralMixedHeightIntegerNatural
public import LeanCanny.Algebra.IntegralMixedFullHeightNaturalOutside
/-! # The native scalar-height model is the actual physical or virtual height entry -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNativeHeightActualBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedOldHeightBits (bankFamily state)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem physical_word (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (hx : get P .slot15 q = 1) :
    IntegralMixedHeightIntegerBits.word P D q = IntegralMixedPhysicalNativeLowerBits.height P (IntegralMixedHeightCellsBits.physicalFamily P D) q := by
  by_cases HB : get P .slot8 q < P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1
  · let i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1) := ⟨get P .slot8 q, HB⟩
    have H := IntegralMixedHeightIntegerNaturalBits.physical P D q i rfl hx
    have HS := IntegralMixedFullHeightNaturalBridge.physical P (IntegralMixedHeightCellsBits.physicalFamily P D) q i rfl
    unfold IntegralMixedHeightIntegerBits.word
    exact (congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) H).trans HS.symm
  · rw [IntegralMixedHeightIntegerNaturalBits.invalid P D q HB]
    exact (IntegralMixedFullHeightNaturalBridge.physical_invalid P (IntegralMixedHeightCellsBits.physicalFamily P D) q HB).symm

theorem virtual_word (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (hx : 2 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) :
    IntegralMixedHeightIntegerBits.word P D q = IntegralMixedVirtualNativeLowerBits.height P (bankFamily P D) q := by
  have HN : get P .slot15 q ≠ 1 := by omega
  have HX : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := ⟨by omega, hx.2⟩
  by_cases HB : get P .slot8 q < (bankFamily P D).ambient (IntegralMixedVirtualTaskBits.saved P q) + 1
  · let i : Fin ((bankFamily P D).ambient (IntegralMixedVirtualTaskBits.saved P q) + 1) := ⟨get P .slot8 q, HB⟩
    have H := IntegralMixedHeightIntegerNaturalBits.virtual P D q i rfl HN HX
    have HS := IntegralMixedFullHeightNaturalBridge.virtual P (bankFamily P D) q i rfl
    unfold IntegralMixedHeightIntegerBits.word
    exact (congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) H).trans HS.symm
  · rw [IntegralMixedHeightIntegerNaturalBits.invalid P D q HB]
    exact (IntegralMixedFullHeightNaturalBridge.virtual_invalid P (bankFamily P D) q HB).symm

theorem physical_model (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (hx : get P .slot15 q = 1) :
    IntegralMixedNativeHeightBits.model P D q = IntegralMixedPhysicalNativeLowerBits.height P (IntegralMixedHeightCellsBits.physicalFamily P D) q :=
  (IntegralMixedNativeHeightBits.model_eq P D q).trans (physical_word P D q hx)

theorem virtual_model (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (hx : 2 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) :
    IntegralMixedNativeHeightBits.model P D q = IntegralMixedVirtualNativeLowerBits.height P (bankFamily P D) q :=
  (IntegralMixedNativeHeightBits.model_eq P D q).trans (virtual_word P D q hx)

end LeanCanny.Algebra.IntegralMixedNativeHeightActualBits
