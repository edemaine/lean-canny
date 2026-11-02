/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarOriginal
public import LeanCanny.Encoding.BinaryBitFP
/-! # Original indexed scale masks for current-Q scalar controls

Frozen scale2 and free scale1 may occur in the same rule. Native mask lookup
supplies only these immutable literals. Current Q is still restored by the
charged bank-product controller, never by an original cell reader.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQIndexedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedScalarCellsBits (physicalFamily virtualFamily)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] modulus IntegralMixedFramedScalarCellsBits.affine

def scale (P : Parameters) (mask : List Bool→List Bool) (q : List Bool) (i : ℕ) : ℤ :=
  if i<IntegralMixedOriginalRuleBodyBits.arity P q then if (mask q)[i]?.getD false then 2 else 1 else 1

theorem mask_flag_FP {mask : List Bool→List Bool} {index : List Bool→ℕ}
    (hm : mask∈FP) (hi : BinaryFn index) : (fun z => [(mask z)[index z]?.getD false])∈FP := by
  have HF := FPPred.getBit hm (UnaryFn.fromBitsLE_min hi.bits_mem_FP (UnaryFn.length hm))
  exact mem_FP_of_eq HF.flag_mem_FP (fun z => by
    simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits,BinaryNat.getD_min_length,Bool.decide_eq_true])

def scaleCode (P : Parameters) (mask : List Bool→List Bool) (z : List Bool) :=
  SignStatisticBits.integerCode (scale P mask (pairFst z) (Nat.fromBitsLE (pairSnd z)))

theorem scaleCode_FP (P : Parameters) (a : Access P) {mask : List Bool→List Bool} (hm : mask∈FP) : scaleCode P mask∈FP := by
  have HF := FPPred.of_flag (mask_flag_FP (mem_FP_comp pairFst_mem_FP hm) (BinaryFn.fromBits pairSnd_mem_FP))
  have HI := (BinaryFn.fromBits pairSnd_mem_FP).lt
    (BinaryFn.ofUnary ((IntegralMixedOriginalRuleBodyBits.arity_unary P a).comp pairFst_mem_FP))
  apply mem_FP_of_eq (HI.ite_mem_FP
    (HF.ite_mem_FP (constFn_mem_FP (SignStatisticBits.integerCode 2)) (constFn_mem_FP (SignStatisticBits.integerCode 1)))
    (constFn_mem_FP (SignStatisticBits.integerCode 1)))
  intro z
  simp only [Function.comp_apply]
  unfold scaleCode scale
  split_ifs <;> rfl

theorem scale_space (P : Parameters) (a : Access P) {mask : List Bool→List Bool} (hm : mask∈FP) :
    SpaceFunction (fun z => residueBits (scale P mask (pairFst z) (Nat.fromBitsLE (pairSnd z)) : ZMod (modulus P (pairFst z)))) :=
  IntegralMixedOriginalRuleBodyBits.residue_space (scaleCode P mask) (scaleCode_FP P a hm) (fun _ => rfl)
    (fun z => modulus P (pairFst z)) ((modulus_binary P a).comp pairFst_mem_FP)
    (fun z => Nat.pos_of_ne_zero (modulus_ne_zero P (pairFst z)))

structure OriginalRules (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) where
  word : List Bool→List Bool
  word_space : SpaceFunction word
  word_eq : ∀ q,word q=IntegralMixedAffineCode.encode (IntegralMixedFramedScalarCellsBits.affine P D J q)
  physicalMask : List Bool→List Bool
  virtualMask : List Bool→List Bool
  physical_FP : physicalMask∈FP
  virtual_FP : virtualMask∈FP
  physicalScales : ∀ q (i : Fin (IntegralMixedOriginalRuleBodyBits.arity P q)),
    ((physicalFamily P D J).rule (IntegralMixedVirtualTaskBits.saved P q)).scales i=
      if (physicalMask q)[i.val]?.getD false then 2 else 1
  virtualScales : ∀ q (i : Fin (IntegralMixedOriginalRuleBodyBits.arity P q)),
    ((virtualFamily P D J).rule (IntegralMixedVirtualTaskBits.saved P q)).critical.scales i=
      if (virtualMask q)[i.val]?.getD false then 2 else 1
  slope : IntegralMixedFramedCurrentQHeightBits.UnitSlope P D J

def selectedMask (P : Parameters) (physical virtual : List Bool→List Bool) (q : List Bool) :=
  if get P .slot15 q=1 then physical q else virtual q

theorem selectedMask_FP (P : Parameters) (a : Access P) {physical virtual : List Bool→List Bool}
    (hp : physical∈FP) (hv : virtual∈FP) : selectedMask P physical virtual∈FP :=
  mem_FP_of_eq (((get_binary P a .slot15).eq (BinaryFn.const 1)).ite_mem_FP hp hv) (fun _ => rfl)

variable (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
  (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : OriginalRules P D J)

theorem physical_scale (q : List Bool) (i : ℕ) :
    IntegralMixedPhysicalDenominatorPostBits.scale P (physicalFamily P D J) q i=scale P h.physicalMask q i := by
  change (if hi : i<IntegralMixedOriginalRuleBodyBits.arity P q then
    ((physicalFamily P D J).rule (IntegralMixedVirtualTaskBits.saved P q)).scales ⟨i,hi⟩ else 1)=_
  unfold scale
  by_cases hi : i<IntegralMixedOriginalRuleBodyBits.arity P q
  · rw [dite_eq_left hi,ite_eq_left hi]
    exact h.physicalScales q ⟨i,hi⟩
  · rw [dite_eq_right hi,ite_eq_right hi]

theorem virtual_scale (q : List Bool) (i : ℕ) :
    IntegralMixedVirtualDenominatorPostBits.scale P (virtualFamily P D J) q i=scale P h.virtualMask q i := by
  change (if hi : i<IntegralMixedOriginalRuleBodyBits.arity P q then
    ((virtualFamily P D J).rule (IntegralMixedVirtualTaskBits.saved P q)).critical.scales ⟨i,hi⟩ else 1)=_
  unfold scale
  by_cases hi : i<IntegralMixedOriginalRuleBodyBits.arity P q
  · rw [dite_eq_left hi,ite_eq_left hi]
    exact h.virtualScales q ⟨i,hi⟩
  · rw [dite_eq_right hi,ite_eq_right hi]

theorem selected_scale (q : List Bool) (i : ℕ) :
    IntegralMixedFramedScalarCellsBits.cell P D J q 2 i=scale P (selectedMask P h.physicalMask h.virtualMask) q i := by
  change (if hi : i<IntegralMixedOriginalRuleBodyBits.arity P q then
    (IntegralMixedFramedScalarCellsBits.rule P D J (IntegralMixedVirtualTaskBits.saved P q)).scales ⟨i,hi⟩ else 1)=_
  unfold scale
  by_cases hi : i<IntegralMixedOriginalRuleBodyBits.arity P q
  · rw [dite_eq_left hi,ite_eq_left hi]
    by_cases hx : get P .slot15 q=1
    · rw [IntegralMixedFramedScalarCellsBits.rule_physical P D J q hx,h.physicalScales]
      simp only [selectedMask,hx,ite_true]
    · rw [IntegralMixedFramedScalarCellsBits.rule_virtual P D J q hx,h.virtualScales]
      simp only [selectedMask,hx,ite_false]
  · rw [dite_eq_right hi,ite_eq_right hi]

include a h in
theorem lowControls : IntegralMixedFramedCurrentQHeightBits.LowControls P D J := by
  let Q := fun p => pairFst (pairFst p)
  have HQ : Q∈FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HM : BinaryFn (fun p => modulus P (Q p)) := (modulus_binary P a).comp HQ
  have HB := h.word_space.precompose Q HQ
  have HC := IntegralMixedAffineCode.constant_space_fromSpace
    (fun p => IntegralMixedFramedScalarCellsBits.affine P D J (Q p)) (h.word ∘ Q)
    (fun p => BinaryNatCode.encode (modulus P (Q p)-1)) HB ((HM.sub (BinaryFn.const 1)).bits_mem_FP) (fun p => h.word_eq (Q p))
  have HR := IntegralMixedAffineCode.reference_space_fromSpace
    (fun p => IntegralMixedFramedScalarCellsBits.affine P D J (Q p)) (h.word ∘ Q)
    (fun p => BinaryNatCode.encode (modulus P (Q p)-1)) (fun p => Nat.fromBitsLE (pairSnd p)) HB
    ((HM.sub (BinaryFn.const 1)).bits_mem_FP) (BinaryFn.fromBits pairSnd_mem_FP) (fun p => h.word_eq (Q p))
  have Hmod : ∀ p,Nat.fromBitsLE (BinaryNatCode.encode (modulus P (Q p)-1))+1=modulus P (Q p) := by
    intro p
    simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits]
    have H := modulus_ne_zero P (Q p)
    omega
  constructor
  intro tag htag
  interval_cases tag
  · apply HC.congr
    funext p
    rw [Hmod,IntegralMixedFramedCurrentQHeightBits.read_eq]
    simp only [Q,IntegralMixedFramedScalarCellsBits.cell,Nat.reduceEqDiff,ite_true,ite_false]
  · apply HR.congr
    funext p
    rw [Hmod,IntegralMixedFramedCurrentQHeightBits.read_eq]
    simp only [Q,IntegralMixedFramedScalarCellsBits.cell,Nat.reduceEqDiff,ite_true,ite_false]
  · have HS := (scale_space P a (selectedMask_FP P a h.physical_FP h.virtual_FP)).precompose
      (fun p => pair (Q p) (pairSnd p)) (mem_FP_pair HQ pairSnd_mem_FP)
    apply HS.congr
    funext p
    rw [IntegralMixedFramedCurrentQHeightBits.read_eq,selected_scale P D J h]
    exact congrArg₂ (fun (q : List Bool) (i : ℕ) => residueBits
      (scale P (selectedMask P h.physicalMask h.virtualMask) q i : ZMod (modulus P q)))
      (pairFst_pair _ _) (congrArg Nat.fromBitsLE (pairSnd_pair _ _))

noncomputable def heightControls : IntegralMixedFramedCurrentQHeightBits.Controls P D J where
  low := lowControls P a D J h
  current := h.slope.current
  current_FP := h.slope.current_FP
  multiplier := IntegralMixedFramedCurrentQHeightBits.unitMultiplier P D J h.slope
  multiplier_space := SpaceFunction.ofFP _ (IntegralMixedFramedCurrentQHeightBits.unitMultiplier_FP P a D J h.slope)
  slope := IntegralMixedFramedCurrentQHeightBits.unit_slope P D J h.slope

noncomputable def controls (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D J T) (hl : IntegralMixedFramedScalarLeadingBits.Primitive P D J) :
    IntegralMixedFramedCurrentQScalarBits.Controls P D J where
  tables := T
  native := ht
  represents := hr
  leading := hl
  physicalScales := by
    apply (scale_space P a h.physical_FP).congr
    funext z
    change residueBits (_ : ZMod _) = residueBits ((IntegralMixedPhysicalDenominatorPostBits.scale P (physicalFamily P D J)
      (pairFst z) (Nat.fromBitsLE (pairSnd z)) : ℤ) : ZMod (modulus P (pairFst z)))
    rw [physical_scale P D J h]
  virtualScales := by
    apply (scale_space P a h.virtual_FP).congr
    funext z
    change residueBits (_ : ZMod _) = residueBits ((IntegralMixedVirtualDenominatorPostBits.scale P (virtualFamily P D J)
      (pairFst z) (Nat.fromBitsLE (pairSnd z)) : ℤ) : ZMod (modulus P (pairFst z)))
    rw [virtual_scale P D J h]
  height := heightControls P a D J h

end LeanCanny.Algebra.IntegralMixedFramedCurrentQIndexedBits
