/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSourceIntegerSnapshot
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQIndexedOriginal
/-! # Total zero/unit original scalar rules for integer-only framed plans -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
  (hdegree : ∀root,(Q root).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
  (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,count root+2≤P.cap root+1)
  (hn : ∀root,0<P.ambient root) (hSW : ∀root,(P.degree root).size≤P.sourceWidth root)

local notation "D" => plan P Q hdegree hcap S count hz hd hroom
local notation "J" => data P Q hdegree hcap S count hz hd hroom hn hSW

theorem physical_rule (key : List Bool) : IntegralMixedFramedPhysicalBits.rule P D key=IntegralMixedFullPhysicalBits.defaultRule _ := by
  obtain ⟨p,hp,hb,hc⟩:=instruction_integer P Q hdegree hcap S count hz hd hroom key
  unfold IntegralMixedFramedPhysicalBits.rule
  rw [hc]

theorem virtual_rule (key : List Bool) : (IntegralMixedFramedHistoryFamilyBits.family P D J).rule key=
    IntegralMixedCanonicalUnitRuleBits.virtual (P.ambient (pairFst key)) (hn (pairFst key))
      (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) [] := by
  obtain ⟨p,hp,hb,hc⟩:=instruction_integer P Q hdegree hcap S count hz hd hroom key
  change (IntegralMixedFramedHistoryFamilyBits.selection P D J key).rule=_
  unfold IntegralMixedFramedHistoryFamilyBits.selection
  rw [hc]
  rfl

theorem affine_zero (q : List Bool) : IntegralMixedFramedScalarCellsBits.affine P D J q=.constant 0 := by
  unfold IntegralMixedFramedScalarCellsBits.affine
  by_cases hi : get P .slot8 q<P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q))+1
  · rw [dite_eq_left hi]
    unfold IntegralMixedFramedScalarCellsBits.rule
    split_ifs
    · change (IntegralMixedFramedPhysicalBits.rule P D (IntegralMixedVirtualTaskBits.saved P q)).heights ⟨get P .slot8 q,hi⟩=_
      rw [physical_rule]
      rfl
    · rw [virtual_rule]
      simp [IntegralMixedCanonicalUnitRuleBits.virtual,IntegralMixedUnitRecordCode.field,
        IntegralMixedUnitRowCode.expression,IntegralMixedUnitRowCode.active,WordList.get,pairFst]
  · rw [dite_eq_right hi]

noncomputable def originalRules : IntegralMixedFramedCurrentQIndexedBits.OriginalRules P D J where
  word _:=IntegralMixedAffineCode.encode (.constant 0)
  word_space:=SpaceFunction.ofFP _ (constFn_mem_FP _)
  word_eq q:=congrArg IntegralMixedAffineCode.encode (affine_zero P Q hdegree hcap S count hz hd hroom hn hSW q).symm
  physicalMask _:=[]
  virtualMask _:=[]
  physical_FP:=constFn_mem_FP []
  virtual_FP:=constFn_mem_FP []
  physicalScales q i:=by
    change (IntegralMixedFramedPhysicalBits.rule P D (IntegralMixedVirtualTaskBits.saved P q)).scales i=_
    rw [physical_rule]
    simp only [IntegralMixedFullPhysicalBits.defaultRule,List.getElem?_nil,Option.getD_none,Bool.false_eq_true,ite_false]
  virtualScales q i:=by
    rw [virtual_rule]
    simp only [IntegralMixedCanonicalUnitRuleBits.virtual,List.getElem?_nil,Option.getD_none,Bool.false_eq_true,ite_false]
  slope:={
    current _:=false
    current_FP:=constFn_mem_FP [false]
    height _:=0
    height_binary:=BinaryFn.const 0
    height_eq q:=by
      rw [virtual_rule]
      simp [IntegralMixedCanonicalUnitRuleBits.virtual,IntegralMixedUnitRecordCode.height,
        IntegralMixedUnitRecordCode.virtualOffset,IntegralMixedUnitRecordCode.field,WordList.get,pairFst]
      simp only [show Nat.fromBitsLE ([] : List Bool)=0 from rfl,Nat.zero_mod]
    slope_eq q:=by rw [virtual_rule]; rfl }

end LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
