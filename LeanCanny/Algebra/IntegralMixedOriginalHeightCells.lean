/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOriginalHeightSyntax
/-! # All full-history height-cell primitives follow from original syntax access -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOriginalRuleBodyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def selectedScaleCode (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (z : List Bool) :=
  if get P .slot15 (pairFst z) = 1 then scaleCode P D h true z else scaleCode P D h false z

theorem selectedScaleCode_FP (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) :
    selectedScaleCode P D h ∈ FP := by
  have HC : BinaryFn (fun z => get P .slot15 (pairFst z)) := (get_binary P a .slot15).comp pairFst_mem_FP
  exact (HC.eq (BinaryFn.const 1)).ite_mem_FP (scaleCode_FP P a D h true) (scaleCode_FP P a D h false)

theorem selectedScaleCode_eq (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (z : List Bool) :
    selectedScaleCode P D h z = SignStatisticBits.integerCode
      (IntegralMixedHeightCellsBits.cell P D (pairFst z) 2 (Nat.fromBitsLE (pairSnd z))) := by
  unfold selectedScaleCode
  by_cases hx : get P .slot15 (pairFst z) = 1
  · rw [ite_eq_left hx, physical_scaleCode]
    change SignStatisticBits.integerCode _ = SignStatisticBits.integerCode
      (if hi : Nat.fromBitsLE (pairSnd z) < arity P (pairFst z) then
        (IntegralMixedHeightCellsBits.rule P D (IntegralMixedVirtualTaskBits.saved P (pairFst z))).scales ⟨_, hi⟩ else 1)
    rw [IntegralMixedHeightCellsBits.rule_physical P D (pairFst z) hx]
    rfl
  · rw [ite_eq_right hx, virtual_scaleCode]
    change SignStatisticBits.integerCode _ = SignStatisticBits.integerCode
      (if hi : Nat.fromBitsLE (pairSnd z) < arity P (pairFst z) then
        (IntegralMixedHeightCellsBits.rule P D (IntegralMixedVirtualTaskBits.saved P (pairFst z))).scales ⟨_, hi⟩ else 1)
    rw [IntegralMixedHeightCellsBits.rule_virtual P D (pairFst z) hx]
    rfl

def indexPacket (z : List Bool) := pair (pairFst z) (pairSnd (pairSnd z))
theorem indexPacket_FP : indexPacket ∈ FP := mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

attribute [local irreducible] heightSource IntegralMixedHeightCellsBits.affine modulus

theorem constant_cell_space (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) :
    SpaceFunction (fun z => residueBits (IntegralMixedAffineCoefficients.constantCoefficient (IntegralMixedHeightCellsBits.affine P D (pairFst z)) : ZMod (modulus P (pairFst z)))) := by
  have HS := mem_FP_comp (f := pairFst) (g := heightSource P D h) pairFst_mem_FP (heightSource_FP P a D h)
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  have HC := IntegralMixedAffineCode.constant_space
    (fun z => IntegralMixedHeightCellsBits.affine P D (pairFst z))
    (fun z => heightSource P D h (pairFst z)) (fun z => BinaryNatCode.encode (modulus P (pairFst z) - 1))
    HS ((HM.sub (BinaryFn.const 1)).bits_mem_FP) (fun z => heightSource_eq P D h (pairFst z))
  apply HC.congr
  funext z
  exact congrArg (fun m => residueBits (IntegralMixedAffineCoefficients.constantCoefficient (IntegralMixedHeightCellsBits.affine P D (pairFst z)) : ZMod m)) (by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel (Nat.pos_of_ne_zero (modulus_ne_zero P (pairFst z)))])

theorem reference_cell_space (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) :
    SpaceFunction (fun z => residueBits (IntegralMixedAffineCoefficients.referenceCoefficient (IntegralMixedHeightCellsBits.affine P D (pairFst z))
      (Nat.fromBitsLE (pairSnd (pairSnd z))) : ZMod (modulus P (pairFst z)))) := by
  have HS := mem_FP_comp (f := pairFst) (g := heightSource P D h) pairFst_mem_FP (heightSource_FP P a D h)
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  have HJ : BinaryFn (fun z => Nat.fromBitsLE (pairSnd (pairSnd z))) := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have HC := IntegralMixedAffineCode.reference_space
    (fun z => IntegralMixedHeightCellsBits.affine P D (pairFst z))
    (fun z => heightSource P D h (pairFst z)) (fun z => BinaryNatCode.encode (modulus P (pairFst z) - 1))
    (fun z => Nat.fromBitsLE (pairSnd (pairSnd z)))
    HS ((HM.sub (BinaryFn.const 1)).bits_mem_FP) HJ (fun z => heightSource_eq P D h (pairFst z))
  apply HC.congr
  funext z
  exact congrArg (fun m => residueBits (IntegralMixedAffineCoefficients.referenceCoefficient (IntegralMixedHeightCellsBits.affine P D (pairFst z))
    (Nat.fromBitsLE (pairSnd (pairSnd z))) : ZMod m)) (by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel (Nat.pos_of_ne_zero (modulus_ne_zero P (pairFst z)))])

theorem scale_cell_space (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) :
    SpaceFunction (fun z => residueBits (IntegralMixedHeightCellsBits.cell P D (pairFst z) 2 (Nat.fromBitsLE (pairSnd (pairSnd z))) : ZMod (modulus P (pairFst z)))) := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  have HC := residue_space (selectedScaleCode P D h) (selectedScaleCode_FP P a D h) (selectedScaleCode_eq P D h)
    (fun z => modulus P (pairFst z)) HM (fun z => Nat.pos_of_ne_zero (modulus_ne_zero P (pairFst z)))
  apply (HC.precompose indexPacket indexPacket_FP).congr
  funext z
  exact congrArg₂ (fun (q : List Bool) (i : ℕ) => residueBits (IntegralMixedHeightCellsBits.cell P D q 2 i : ZMod (modulus P q)))
    (pairFst_pair _ _) (congrArg Nat.fromBitsLE (pairSnd_pair _ _))

theorem slope_cell_space (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) :
    SpaceFunction (fun z => residueBits (IntegralMixedHeightCellsBits.cell P D (pairFst z) 3 (Nat.fromBitsLE (pairSnd (pairSnd z))) : ZMod (modulus P (pairFst z)))) := by
  have HC := residue_space (slopeCode P D h) (slopeCode_FP P a D h) (slopeCode_eq P D h)
    (modulus P) (modulus_binary P a) (fun q => Nat.pos_of_ne_zero (modulus_ne_zero P q))
  exact HC.precompose pairFst pairFst_mem_FP

theorem height_primitive (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) :
    IntegralMixedHeightCellsBits.Primitive P D := by
  let tag := fun z => Nat.fromBitsLE (pairFst (pairSnd z))
  have HT : BinaryFn tag := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have HZ := SpaceFunction.ofFP (fun _ : List Bool => []) (constFn_mem_FP [])
  have H3 := SpaceFunction.branch (fun z => decide (tag z = 3)) (HT.eq (BinaryFn.const 3)).flag_mem_FP (slope_cell_space P a D h) HZ
  have H2 := SpaceFunction.branch (fun z => decide (tag z = 2)) (HT.eq (BinaryFn.const 2)).flag_mem_FP (scale_cell_space P a D h) H3
  have H1 := SpaceFunction.branch (fun z => decide (tag z = 1)) (HT.eq (BinaryFn.const 1)).flag_mem_FP (reference_cell_space P a D h) H2
  have H0 := SpaceFunction.branch (fun z => decide (tag z = 0)) (HT.eq (BinaryFn.const 0)).flag_mem_FP (constant_cell_space P a D h) H1
  apply H0.congr
  funext z
  unfold IntegralMixedHeightCellsBits.reader
  dsimp only [tag]
  simp only [decide_eq_true_eq]
  split_ifs with h0 h1 h2 h3
  · rw [h0]; rfl
  · rw [h1]; rfl
  · rw [h2]
  · rw [h3]
  · simp only [IntegralMixedHeightCellsBits.cell, h0, h1, h2, h3, ite_false]
    simpa only [ArithmeticBits.zero, Int.cast_zero] using ArithmeticBits.zero_residueBits (modulus P (pairFst z))

theorem controls (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (full : IntegralMixedFullHistoryFamilyBits.Metadata P D)
    (physical : IntegralMixedPhysicalQueryBits.InputMetadata (IntegralMixedFullScalarBits.physicalFamily P D)) (h : Access P D) :
    IntegralMixedFullScalarBits.Controls P D where
  full := full
  physical := physical
  leading := leading_primitive P a D h
  physicalScales := physical_scales_primitive P a D h
  virtualScales := virtual_scales_primitive P a D h
  height := height_primitive P a D h
end LeanCanny.Algebra.IntegralMixedOriginalRuleBodyBits
