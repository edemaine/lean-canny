/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCausalRecordSnapshot
/-! # Original records construct actual current-Q scalar controls

Only the original source-leading residue cost is separate. Header provenance,
original affine syntax, per-index scale masks and current-mode metadata all
come from the literal raw record table, including malformed/default keys.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCausalRecordPlanBits
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
open IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀ root,0<P.ambient root) (hd : ∀ root b,(S root b).degree=P.degree root)
  (hcap : ∀ root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (hroom : ∀ root,count root+2≤P.cap root+1)
  (hW : ∀ root,(P.degree root).size≤P.sourceWidth root)

noncomputable def slopeAdapter (a : Access P) :
    IntegralMixedFramedCurrentQHeightBits.UnitSlope P (plan P S hn hd hcap hroom) (data P S hn hd hcap hroom hW) :=
  IntegralMixedCausalPlanBits.unitSlope P (base P S hd hcap hroom)
    (originalRecords P S hn hd hcap) (fun root => (originalRecords_length P S hn hd hcap root) ▸ hroom root)
    hn (originalRecords_degree P S hn hd hcap) hW a (metadata P S hn hd hcap a)

theorem represents : IntegralMixedFramedHeaderBits.Represents P (plan P S hn hd hcap hroom)
    (data P S hn hd hcap hroom hW) (IntegralMixedCausalPlanBits.tables P (originalRecords P S hn hd hcap)) :=
  IntegralMixedCausalPlanBits.tables_represent P (base P S hd hcap hroom) (originalRecords P S hn hd hcap)
    (fun root => (originalRecords_length P S hn hd hcap root) ▸ hroom root) hn (originalRecords_degree P S hn hd hcap) hW

attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralMixedVirtualTaskBits.saved plan data base originalRecords

theorem word_eq (q : List Bool) : word P q=IntegralMixedAffineCode.encode
    (IntegralMixedFramedScalarCellsBits.affine P (plan P S hn hd hcap hroom) (data P S hn hd hcap hroom hW) q) := by
  unfold word
  by_cases hi : get P .slot8 q<IntegralMixedOriginalRuleBodyBits.arity P q
  · rw [ite_eq_left hi]
    unfold rowSyntax rowQuery
    simp only [pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    apply congrArg IntegralMixedAffineCode.encode
    unfold IntegralMixedFramedScalarCellsBits.affine
    dsimp only
    change get P .slot8 q<P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q))+1 at hi
    rw [dite_eq_left hi]
    by_cases hx : get P .slot15 q=1
    · rw [IntegralMixedFramedScalarCellsBits.rule_physical P _ _ q hx]
      simp only [hx,decide_true]
      exact (physical_row P S hn hd hcap hroom (IntegralMixedVirtualTaskBits.saved P q) ⟨get P .slot8 q,hi⟩).symm
    · rw [IntegralMixedFramedScalarCellsBits.rule_virtual P _ _ q hx]
      simp only [hx,decide_false]
      exact (virtual_row P S hn hd hcap hroom hW (IntegralMixedVirtualTaskBits.saved P q) ⟨get P .slot8 q,hi⟩).symm
  · rw [ite_eq_right hi]
    apply congrArg IntegralMixedAffineCode.encode
    unfold IntegralMixedFramedScalarCellsBits.affine
    dsimp only
    change ¬get P .slot8 q<P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q))+1 at hi
    rw [dite_eq_right hi]

noncomputable def originalRules (a : Access P) :
    IntegralMixedFramedCurrentQIndexedBits.OriginalRules P (plan P S hn hd hcap hroom) (data P S hn hd hcap hroom hW) where
  word := word P
  word_space := SpaceFunction.ofFP _ (word_FP P a)
  word_eq := word_eq P S hn hd hcap hroom hW
  physicalMask q := mask P true (IntegralMixedVirtualTaskBits.saved P q)
  virtualMask q := mask P false (IntegralMixedVirtualTaskBits.saved P q)
  physical_FP := mem_FP_comp (IntegralMixedVirtualTaskBits.saved_FP P a) (mask_FP P a true)
  virtual_FP := mem_FP_comp (IntegralMixedVirtualTaskBits.saved_FP P a) (mask_FP P a false)
  physicalScales q i := physical_mask P S hn hd hcap hroom (IntegralMixedVirtualTaskBits.saved P q) i
  virtualScales q i := virtual_mask P S hn hd hcap hroom hW (IntegralMixedVirtualTaskBits.saved P q) i
  slope := slopeAdapter P S hn hd hcap hroom hW a

noncomputable def scalarControls (a : Access P)
    (hl : IntegralMixedFramedScalarLeadingBits.Primitive P (plan P S hn hd hcap hroom) (data P S hn hd hcap hroom hW)) :
    IntegralMixedFramedCurrentQScalarBits.Controls P (plan P S hn hd hcap hroom) (data P S hn hd hcap hroom hW) :=
  IntegralMixedFramedCurrentQIndexedBits.controls P a (plan P S hn hd hcap hroom) (data P S hn hd hcap hroom hW)
    (originalRules P S hn hd hcap hroom hW a)
    (IntegralMixedCausalPlanBits.tables P (originalRecords P S hn hd hcap)) (tables_native P S hn hd hcap a)
    (represents P S hn hd hcap hroom hW) hl

end LeanCanny.Encoding.IntegralMixedCausalRecordPlanBits
