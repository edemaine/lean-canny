/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordSnapshot
public import LeanCanny.Algebra.BoundedRegularFramedOriginal
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeSpace
/-! # Original record cells close the causal continuation scalar backend -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
open IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ)
  (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (S root 0).degree≤2^P.width root)
  (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
  (hW : ∀root,(P.degree root).size≤P.sourceWidth root)

attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralMixedVirtualTaskBits.saved plan data base originalRecords

theorem word_eq (q : List Bool) : word P N q=IntegralMixedAffineCode.encode
    (IntegralMixedFramedScalarCellsBits.affine P (plan P S hn hd hcap N T hz hT hroom) (data P S hn hd hcap N hq T hz hT hroom hW) q) := by
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
      exact (physical_row P S hn hd hcap N hq T hz hT hroom (IntegralMixedVirtualTaskBits.saved P q) ⟨get P .slot8 q,hi⟩).symm
    · rw [IntegralMixedFramedScalarCellsBits.rule_virtual P _ _ q hx]
      simp only [hx,decide_false]
      exact (virtual_row P S hn hd hcap N hq T hz hT hroom hW (IntegralMixedVirtualTaskBits.saved P q) ⟨get P .slot8 q,hi⟩).symm
  · rw [ite_eq_right hi]
    apply congrArg IntegralMixedAffineCode.encode
    unfold IntegralMixedFramedScalarCellsBits.affine
    dsimp only
    change ¬get P .slot8 q<P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q))+1 at hi
    rw [dite_eq_right hi]

noncomputable def originalRules (a : Access P) (hN : UnaryFn N) :
    IntegralMixedFramedCurrentQIndexedBits.OriginalRules P (plan P S hn hd hcap N T hz hT hroom) (data P S hn hd hcap N hq T hz hT hroom hW) where
  word := word P N
  word_space := SpaceFunction.ofFP _ (word_FP P a N hN)
  word_eq := word_eq P S hn hd hcap N hq T hz hT hroom hW
  physicalMask q := mask P N true (IntegralMixedVirtualTaskBits.saved P q)
  virtualMask q := mask P N false (IntegralMixedVirtualTaskBits.saved P q)
  physical_FP := mem_FP_comp (IntegralMixedVirtualTaskBits.saved_FP P a) (mask_FP P a N hN true)
  virtual_FP := mem_FP_comp (IntegralMixedVirtualTaskBits.saved_FP P a) (mask_FP P a N hN false)
  physicalScales q i := physical_mask P S hn hd hcap N hq T hz hT hroom (IntegralMixedVirtualTaskBits.saved P q) i
  virtualScales q i := virtual_mask P S hn hd hcap N hq T hz hT hroom hW (IntegralMixedVirtualTaskBits.saved P q) i
  slope := slopeAdapter P S hn hd hcap N hq T hz hT hroom a hN hW

noncomputable def scalarControls (a : Access P) (hN : UnaryFn N)
    (hl : IntegralMixedFramedScalarLeadingBits.Primitive P (plan P S hn hd hcap N T hz hT hroom) (data P S hn hd hcap N hq T hz hT hroom hW)) :
    IntegralMixedFramedCurrentQScalarBits.Controls P (plan P S hn hd hcap N T hz hT hroom) (data P S hn hd hcap N hq T hz hT hroom hW) :=
  IntegralMixedFramedCurrentQIndexedBits.controls P a (plan P S hn hd hcap N T hz hT hroom) (data P S hn hd hcap N hq T hz hT hroom hW)
    (originalRules P S hn hd hcap N hq T hz hT hroom hW a hN)
    (IntegralMixedCausalPlanBits.tables P (originalRecords P S hn hd hcap N hq T hz hT)) (tables_native P S hn hd hcap N hq T hz hT a hN)
    (tables_represent P S hn hd hcap N hq T hz hT hroom hW) hl

noncomputable def currentQControls (a : Access P) (hN : UnaryFn N) (hA : IntegerPolynomialRootQueriesBits.Access T)
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime)
    (scope : ∀key,(ETR.TermView.term (R.source key)).arity≤R.dim key)
    (snapshot : BoundedRegularFramedOriginalBits.Snapshot P (plan P S hn hd hcap N T hz hT hroom) R)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) :
    IntegralMixedFramedCurrentQNativeBits.Controls P (plan P S hn hd hcap N T hz hT hroom)
      (data P S hn hd hcap N hq T hz hT hroom hW) where
  scalar := scalarControls P S hn hd hcap N hq T hz hT hroom hW a hN
    (BoundedRegularFramedOriginalBits.leading P a (plan P S hn hd hcap N T hz hT hroom)
      (data P S hn hd hcap N hq T hz hT hroom hW) R hR snapshot)
  critical := BoundedRegularFramedOriginalBits.controls P a (plan P S hn hd hcap N T hz hT hroom)
    (data P S hn hd hcap N hq T hz hT hroom hW)
    (IntegralMixedCausalPlanBits.tables P (originalRecords P S hn hd hcap N hq T hz hT))
    (tables_native P S hn hd hcap N hq T hz hT a hN) (tables_represent P S hn hd hcap N hq T hz hT hroom hW)
    R hR scope snapshot
  normalization := {
    tables:=IntegralMixedCausalPlanBits.tables P (originalRecords P S hn hd hcap N hq T hz hT)
    native:=tables_native P S hn hd hcap N hq T hz hT a hN
    represents:=tables_represent P S hn hd hcap N hq T hz hT hroom hW
    nodes:=L
    factor:=F
    seed:=C
    nodes_native:=hL
    factor_native:=hF
    seed_native:=hC }
  producer := {
    tables:=IntegralMixedCausalPlanBits.tables P (originalRecords P S hn hd hcap N hq T hz hT)
    native:=tables_native P S hn hd hcap N hq T hz hT a hN
    represents:=tables_represent P S hn hd hcap N hq T hz hT hroom hW
    integer:=integerOriginal P S hn hd hcap N T hz hT hroom a hA hN }

theorem fallback_bounds (L C : List Bool→ℕ) (hL : ∀root,1≤L root) (key : List Bool) :
    IntegralMixedFramedOriginalBounds.FallbackBounds P (plan P S hn hd hcap N T hz hT hroom)
      (data P S hn hd hcap N hq T hz hT hroom hW) L C key := by
  have HB : IntegralMixedFullHeightBits.RuleBounds (C (pairFst key)+1) (L (pairFst key))
      (IntegralMixedCausalPlanBits.fallbackRule (P.ambient (pairFst key)) (hn (pairFst key))) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro i
      exact hL (pairFst key)
    · intro i
      exact Nat.zero_le _
    · intro i
      simpa only [IntegralMixedCausalPlanBits.fallbackRule,Int.natAbs_one,Nat.size_one] using
        Nat.succ_le_succ (Nat.zero_le (C (pairFst key)))
    · simpa only [IntegralMixedCausalPlanBits.fallbackRule,Int.natAbs_one,Nat.size_one] using
        Nat.succ_le_succ (Nat.zero_le (C (pairFst key)))
  unfold IntegralMixedFramedOriginalBounds.FallbackBounds
  cases (instruction P (plan P S hn hd hcap N T hz hT hroom) key).command <;>
    first | trivial | simpa only [data,IntegralMixedCausalPlanBits.data,IntegralMixedCausalPlanBits.fallback] using HB

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
