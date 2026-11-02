/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarModel
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQHeightUnit
public import LeanCanny.Algebra.IntegralMixedFramedAffineScalarControls
/-! # All six scalar controls from original affine words and current-Q slopes

Original scale flags are literal one/two cells. Spatial leading is charged by
its own original-source leaf. No primitive reads an interpreted denominator.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedAffineScalarBits (literalScale literal_scale_space selectedDouble selectedDouble_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] modulus IntegralMixedFramedScalarCellsBits.affine

structure OriginalRules (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) where
  word : List Bool → List Bool
  word_space : SpaceFunction word
  word_eq : ∀ q,word q=IntegralMixedAffineCode.encode (IntegralMixedFramedScalarCellsBits.affine P D J q)
  physicalDouble : List Bool → Bool
  virtualDouble : List Bool → Bool
  physical_FP : (fun q => [physicalDouble q])∈FP
  virtual_FP : (fun q => [virtualDouble q])∈FP
  physicalScales : ∀ q (i : Fin (IntegralMixedOriginalRuleBodyBits.arity P q)),
    ((physicalFamily P D J).rule (IntegralMixedVirtualTaskBits.saved P q)).scales i=if physicalDouble q then 2 else 1
  virtualScales : ∀ q (i : Fin (IntegralMixedOriginalRuleBodyBits.arity P q)),
    ((virtualFamily P D J).rule (IntegralMixedVirtualTaskBits.saved P q)).critical.scales i=if virtualDouble q then 2 else 1
  slope : IntegralMixedFramedCurrentQHeightBits.UnitSlope P D J

theorem physical_scale (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : OriginalRules P D J) (q : List Bool) (i : ℕ) :
    IntegralMixedPhysicalDenominatorPostBits.scale P (physicalFamily P D J) q i=literalScale P h.physicalDouble q i := by
  change (if hi : i<IntegralMixedOriginalRuleBodyBits.arity P q then
    ((physicalFamily P D J).rule (IntegralMixedVirtualTaskBits.saved P q)).scales ⟨i,hi⟩ else 1)=_
  unfold literalScale
  by_cases hi : i<IntegralMixedOriginalRuleBodyBits.arity P q
  · rw [dite_eq_left hi,ite_eq_left hi]
    exact h.physicalScales q ⟨i,hi⟩
  · rw [dite_eq_right hi,ite_eq_right hi]

theorem virtual_scale (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : OriginalRules P D J) (q : List Bool) (i : ℕ) :
    IntegralMixedVirtualDenominatorPostBits.scale P (virtualFamily P D J) q i=literalScale P h.virtualDouble q i := by
  change (if hi : i<IntegralMixedOriginalRuleBodyBits.arity P q then
    ((virtualFamily P D J).rule (IntegralMixedVirtualTaskBits.saved P q)).critical.scales ⟨i,hi⟩ else 1)=_
  unfold literalScale
  by_cases hi : i<IntegralMixedOriginalRuleBodyBits.arity P q
  · rw [dite_eq_left hi,ite_eq_left hi]
    exact h.virtualScales q ⟨i,hi⟩
  · rw [dite_eq_right hi,ite_eq_right hi]

theorem selected_scale (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : OriginalRules P D J) (q : List Bool) (i : ℕ) :
    IntegralMixedFramedScalarCellsBits.cell P D J q 2 i=literalScale P (selectedDouble P h.physicalDouble h.virtualDouble) q i := by
  change (if hi : i<IntegralMixedOriginalRuleBodyBits.arity P q then
    (IntegralMixedFramedScalarCellsBits.rule P D J (IntegralMixedVirtualTaskBits.saved P q)).scales ⟨i,hi⟩ else 1)=_
  unfold literalScale
  by_cases hi : i<IntegralMixedOriginalRuleBodyBits.arity P q
  · rw [dite_eq_left hi,ite_eq_left hi]
    by_cases hx : get P .slot15 q=1
    · rw [IntegralMixedFramedScalarCellsBits.rule_physical P D J q hx]
      exact (h.physicalScales q ⟨i,hi⟩).trans (by simp only [selectedDouble,hx,ite_true])
    · rw [IntegralMixedFramedScalarCellsBits.rule_virtual P D J q hx]
      exact (h.virtualScales q ⟨i,hi⟩).trans (by simp only [selectedDouble,hx,ite_false])
  · rw [dite_eq_right hi,ite_eq_right hi]

noncomputable def originalCells (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : OriginalRules P D J) :
    IntegralMixedFramedCurrentQHeightBits.OriginalCells P D J where
  word := h.word
  word_space := h.word_space
  word_eq := h.word_eq
  double := selectedDouble P h.physicalDouble h.virtualDouble
  double_FP := selectedDouble_FP P a h.physicalDouble h.virtualDouble h.physical_FP h.virtual_FP
  scales := selected_scale P D J h

noncomputable def Controls.ofOriginal (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : IntegralMixedHeaderTablesBits.Tables)
    (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (hl : IntegralMixedFramedScalarLeadingBits.Primitive P D J) (h : OriginalRules P D J) : Controls P D J where
  tables := T
  native := ht
  represents := hr
  leading := hl
  physicalScales := by
    apply (literal_scale_space P a h.physicalDouble h.physical_FP).congr
    funext z
    change residueBits (_ : ZMod _) = residueBits ((IntegralMixedPhysicalDenominatorPostBits.scale P (physicalFamily P D J)
      (pairFst z) (Nat.fromBitsLE (pairSnd z)) : ℤ) : ZMod (modulus P (pairFst z)))
    rw [physical_scale P D J h]
  virtualScales := by
    apply (literal_scale_space P a h.virtualDouble h.virtual_FP).congr
    funext z
    change residueBits (_ : ZMod _) = residueBits ((IntegralMixedVirtualDenominatorPostBits.scale P (virtualFamily P D J)
      (pairFst z) (Nat.fromBitsLE (pairSnd z)) : ℤ) : ZMod (modulus P (pairFst z)))
    rw [virtual_scale P D J h]
  height := IntegralMixedFramedCurrentQHeightBits.ofOriginal P a D J (originalCells P a D J h) h.slope
end LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits
