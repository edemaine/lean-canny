/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQHeightOriginal
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQHeightPost
/-! # Literal unit sweep records obtain their slope without serializing Q

The original record provides only a mode bit and a selected coordinate. Its
semantic slope is current bank Q in sweep mode and one otherwise. The native
leaf reads the original coordinate mask; Q is restored after charged replies.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] modulus IntegralMixedFramedScalarCellsBits.cell IntegralMixedFramedHeightIntegerBits.bank

structure UnitSlope (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) where
  current : List Bool → Bool
  current_FP : (fun q => [current q])∈FP
  height : List Bool → ℕ
  height_binary : BinaryFn height
  height_eq : ∀ q,((IntegralMixedFramedHistoryFamilyBits.family P D J).rule (IntegralMixedVirtualTaskBits.saved P q)).height.val=height q
  slope_eq : ∀ q,((IntegralMixedFramedHistoryFamilyBits.family P D J).rule (IntegralMixedVirtualTaskBits.saved P q)).slope=
    if current q then IntegralMixedFramedHeightIntegerBits.bank P D J q else 1

def unitMultiplier (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : UnitSlope P D J) (q : List Bool) : ℤ :=
  if get P .slot8 q=h.height q then 1 else 0

theorem unitMultiplier_FP (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : UnitSlope P D J) :
    (fun q => residueBits (unitMultiplier P D J h q : ZMod (modulus P q)))∈FP := by
  have HP := (get_binary P a .slot8).eq h.height_binary
  have HO := mem_FP_comp (modulus_binary P a).bits_mem_FP ArithmeticBits.one_mem_FP
  apply mem_FP_of_eq (HP.ite_mem_FP HO (constFn_mem_FP []))
  intro q
  by_cases hi : get P .slot8 q=h.height q
  · simp only [hi,ite_true,Function.comp_apply,unitMultiplier]
    simpa only [Int.cast_one] using ArithmeticBits.one_residueBits (modulus P q)
  · simp only [hi,ite_false,unitMultiplier,Int.cast_zero]
    exact ArithmeticBits.zero_residueBits (modulus P q)

theorem unit_slope (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : UnitSlope P D J) (q : List Bool) :
    IntegralMixedFramedScalarCellsBits.cell P D J q 3 0=
      (if h.current q then IntegralMixedFramedHeightIntegerBits.bank P D J q else 1)*unitMultiplier P D J h q := by
  simp only [IntegralMixedFramedScalarCellsBits.cell,Nat.reduceEqDiff,ite_true,ite_false]
  rw [h.height_eq q,h.slope_eq q]
  unfold unitMultiplier
  split_ifs <;> simp only [mul_one,mul_zero]

noncomputable def ofOriginal (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (cells : OriginalCells P D J) (slope : UnitSlope P D J) :
    Controls P D J where
  low := lowControls P a D J cells
  current := slope.current
  current_FP := slope.current_FP
  multiplier := unitMultiplier P D J slope
  multiplier_space := SpaceFunction.ofFP _ (unitMultiplier_FP P a D J slope)
  slope := unit_slope P D J slope
end LeanCanny.Algebra.IntegralMixedFramedCurrentQHeightBits
