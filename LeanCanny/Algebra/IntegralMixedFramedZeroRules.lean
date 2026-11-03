/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQIndexedOriginal
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackUnit
public import LeanCanny.Algebra.IntegralMixedFramedNormalizationPlanned
/-! # Literal zero/unit scalar rules survive planning and full-root pullback -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedZeroRulesBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def CriticalZero {n : ℕ} (r : CriticalRule n) : Prop :=
  (∀i,r.heights i=.constant 0) ∧ ∀i,r.scales i=1
def SweepZero {n : ℕ} (r : IntegralMixedCriticalSweep.Rule n) : Prop :=
  CriticalZero r.critical ∧ r.height.val=0 ∧ r.slope=1
structure Rules (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) : Prop where
  physical : ∀key,CriticalZero (IntegralMixedFramedPhysicalBits.rule P D key)
  virtual : ∀key,SweepZero ((IntegralMixedFramedHistoryFamilyBits.family P D J).rule key)

theorem affine_zero (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Rules P D J) (q : List Bool) : IntegralMixedFramedScalarCellsBits.affine P D J q=.constant 0 := by
  unfold IntegralMixedFramedScalarCellsBits.affine
  by_cases hi : get P .slot8 q<P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q))+1
  · rw [dite_eq_left hi]
    unfold IntegralMixedFramedScalarCellsBits.rule
    split_ifs
    · exact (h.physical _).1 _
    · exact (h.virtual _).1.1 _
  · rw [dite_eq_right hi]

noncomputable def originalRules (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Rules P D J) : IntegralMixedFramedCurrentQIndexedBits.OriginalRules P D J where
  word _:=IntegralMixedAffineCode.encode (.constant 0)
  word_space:=SpaceFunction.ofFP _ (constFn_mem_FP _)
  word_eq q:=congrArg IntegralMixedAffineCode.encode (affine_zero P D J h q).symm
  physicalMask _:=[]
  virtualMask _:=[]
  physical_FP:=constFn_mem_FP []
  virtual_FP:=constFn_mem_FP []
  physicalScales q i:=by
    change (IntegralMixedFramedPhysicalBits.rule P D (IntegralMixedVirtualTaskBits.saved P q)).scales i=_
    rw [(h.physical _).2 i]
    simp only [List.getElem?_nil,Option.getD_none,Bool.false_eq_true,ite_false]
  virtualScales q i:=by
    rw [(h.virtual _).1.2 i]
    simp only [List.getElem?_nil,Option.getD_none,Bool.false_eq_true,ite_false]
  slope:={
    current _:=false
    current_FP:=constFn_mem_FP [false]
    height _:=0
    height_binary:=BinaryFn.const 0
    height_eq q:=(h.virtual _).2.1
    slope_eq q:=by rw [(h.virtual _).2.2]; rfl }

private theorem physical_planned (P : Parameters) (D : Plan P) (L F C : List Bool → ℕ) (key : List Bool) :
    IntegralMixedFramedPhysicalBits.rule (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C) key=IntegralMixedFramedPhysicalBits.rule P D key := by
  cases hc : (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;>
    simp only [IntegralMixedFramedPhysicalBits.rule,IntegralMixedFramedNormalizationBits.planned_instruction,hc] <;> rfl
private theorem virtual_planned (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D J L F C)).rule key=
      ((IntegralMixedFramedHistoryFamilyBits.family P D J).rule key) := by
  cases hc : (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;>
    simp only [IntegralMixedFramedHistoryFamilyBits.family,IntegralMixedFramedHistoryFamilyBits.selection,
      IntegralMixedFramedNormalizationBits.planned_instruction,IntegralMixedFramedNormalizationBits.plannedData,hc]

theorem Rules.planned {P : Parameters} {D : Plan P} {J : IntegralMixedFramedHistoryFamilyBits.Data P D}
    (h : Rules P D J) (L F C : List Bool → ℕ) :
    Rules (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D J L F C) where
  physical key:=by rw [physical_planned]; exact h.physical key
  virtual key:=by rw [virtual_planned]; exact h.virtual key

theorem Rules.pullback {P : Parameters} {D : Plan P} {J : IntegralMixedFramedHistoryFamilyBits.Data P D}
    (h : Rules P D J) (project : List Bool → List Bool) (extra : List Bool → ℕ) :
    Rules (IntegralMixedFramedRootPullback.parameters P project extra)
      (IntegralMixedFramedRootPullback.plan P D project extra)
      (IntegralMixedFramedRootPullback.data P D J project extra) where
  physical key:=IntegralMixedFramedRootPullback.critical_pred (fun _ r=>CriticalZero r) _ _
    (congrArg P.ambient (IntegralMixedFramedRootPullback.key_root project key).symm)
    (IntegralMixedFramedRootPullback.physical_rule_heq P D project extra key) (h.physical _)
  virtual key:=IntegralMixedFramedRootPullback.sweep_pred (fun _ r=>SweepZero r) _ _
    (congrArg P.ambient (IntegralMixedFramedRootPullback.key_root project key).symm)
    (IntegralMixedFramedRootPullback.virtual_rule_heq P D J project extra key) (h.virtual _)

theorem fallback_bounds (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Rules P D J) (L C : List Bool → ℕ) (hL : ∀root,1≤L root) (key : List Bool) :
    IntegralMixedFramedOriginalBounds.FallbackBounds P D J L C key := by
  have H:=h.virtual key
  have HB : IntegralMixedFullHeightBits.RuleBounds (C (pairFst key)+1) (L (pairFst key))
      ((IntegralMixedFramedHistoryFamilyBits.family P D J).rule key) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro i; rw [H.1.1 i]; exact hL _
    · intro i; rw [H.1.1 i]; exact Nat.zero_le _
    · intro i; rw [H.1.2 i]; simpa only [Int.natAbs_one,Nat.size_one] using Nat.le_add_left 1 (C (pairFst key))
    · rw [H.2.2]; simpa only [Int.natAbs_one,Nat.size_one] using Nat.le_add_left 1 (C (pairFst key))
  cases hc : (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command with
  | integer => simpa only [IntegralMixedFramedOriginalBounds.FallbackBounds,IntegralMixedFramedHistoryFamilyBits.family,
      IntegralMixedFramedHistoryFamilyBits.selection,hc] using HB
  | critical => simpa only [IntegralMixedFramedOriginalBounds.FallbackBounds,IntegralMixedFramedHistoryFamilyBits.family,
      IntegralMixedFramedHistoryFamilyBits.selection,hc] using HB
  | cut => simp only [IntegralMixedFramedOriginalBounds.FallbackBounds,hc]

end LeanCanny.Algebra.IntegralMixedFramedZeroRulesBits
