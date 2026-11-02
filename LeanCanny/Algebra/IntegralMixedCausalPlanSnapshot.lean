/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalPlanData
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQHeightUnit
/-! # Actual causal-plan sweep fields agree with original metadata and current Q -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalPlanBits
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def templateCurrent {n B : ℕ} {S : SpatialSource n} : Template S B → Bool
  | .cut c => c.current
  | _ => false
noncomputable def templateHeight {n B : ℕ} {S : SpatialSource n} : Template S B → ℕ
  | .cut c => c.height.val
  | _ => 0

noncomputable def current (P : Parameters) (R : ∀ root,List (Record (P.ambient root) (P.width root))) (key : List Bool) :=
  ((R (pairFst key)).reverse[IntegralMixedFramedHistoryFamilyBits.prefixLength P key]?.map (fun r => templateCurrent r.template)).getD false
noncomputable def height (P : Parameters) (R : ∀ root,List (Record (P.ambient root) (P.width root))) (key : List Bool) :=
  ((R (pairFst key)).reverse[IntegralMixedFramedHistoryFamilyBits.prefixLength P key]?.map (fun r => templateHeight r.template)).getD 0

variable (P : Parameters) (base : Plan P) (R : ∀ root,List (Record (P.ambient root) (P.width root)))
  (hroom : ∀ root,(R root).length+2≤P.cap root+1) (hn : ∀ root,0<P.ambient root)
  (hd : ∀ root,∀ r∈R root,r.source.degree=P.degree root) (hW : ∀ root,(P.degree root).size≤P.sourceWidth root)

noncomputable def ruleOfInstruction {n B : ℕ} (c : Instruction n B) (fallback : IntegralMixedCriticalSweep.Rule n) : IntegralMixedCriticalSweep.Rule n :=
  match c.command with
  | .cut r _ _ _ _ => r
  | _ => fallback

private theorem rule_match (key : List Bool) :
    ((IntegralMixedFramedHistoryFamilyBits.family P (plan P base R hroom) (data P base R hroom hn hd hW)).rule key)=
      ruleOfInstruction (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P base R hroom) key)
        (fallbackRule (P.ambient (pairFst key)) (hn (pairFst key))) := by
  change (IntegralMixedFramedHistoryFamilyBits.selection P _ _ key).rule=_
  unfold IntegralMixedFramedHistoryFamilyBits.selection ruleOfInstruction
  cases hc : (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P base R hroom) key).command <;> rfl

theorem fields (key : List Bool) :
    let F:=IntegralMixedFramedHistoryFamilyBits.family P (plan P base R hroom) (data P base R hroom hn hd hW)
    (F.rule key).height.val=height P R key ∧
      (F.rule key).slope=if current P R key then commonDenominator (F.state key) else 1 := by
  dsimp only
  rw [rule_match P base R hroom hn hd hW key]
  let rs := R (pairFst key)
  let b := IntegralMixedFramedHistoryFamilyBits.prefixLength P key
  let initial := IntegralMixedFramedHistoryFamilyBits.initial P base (pairFst key)
  let fallbackI := IntegralMixedFramedHistoryFamilyBits.defaultInstruction P (plan P base R hroom) (pairFst key)
  by_cases hb : b<rs.length
  · have HR := List.getElem?_eq_getElem (l:=rs.reverse) (i:=b) (by rw [List.length_reverse]; exact hb)
    have HI := chronological_instantiate initial rs (records_bound P R hroom _) fallbackI ⟨b,hb⟩
    have HE : IntegralMixedFramedHistoryFamilyBits.instruction P (plan P base R hroom) key=
        instantiate (run initial (paddedPast fallbackI (commands initial rs (records_bound P R hroom _)) b)
          (by rw [paddedPast_length]; exact hb.le.trans (records_bound P R hroom _))) (rs.reverse[b]'(by rw [List.length_reverse]; exact hb)) := by
      change (chronological (commands initial rs (records_bound P R hroom _)) b).getD fallbackI=_
      rw [HI]
      rfl
    have Hcurrent : current P R key=templateCurrent (rs.reverse[b]'(by rw [List.length_reverse]; exact hb)).template := by
      change (rs.reverse[b]?.map (fun r => templateCurrent r.template)).getD false=_
      rw [HR]
      rfl
    have Hheight : height P R key=templateHeight (rs.reverse[b]'(by rw [List.length_reverse]; exact hb)).template := by
      change (rs.reverse[b]?.map (fun r => templateHeight r.template)).getD 0=_
      rw [HR]
      rfl
    rw [HE,Hcurrent,Hheight]
    cases ht : (rs.reverse[b]'(by rw [List.length_reverse]; exact hb)).template with
    | integer =>
      simp only [ruleOfInstruction,instantiate,Template.command,ht,templateCurrent,templateHeight,fallbackRule]
      exact ⟨trivial,rfl⟩
    | critical =>
      simp only [ruleOfInstruction,instantiate,Template.command,ht,templateCurrent,templateHeight,fallbackRule]
      exact ⟨trivial,rfl⟩
    | cut c =>
      simp only [ruleOfInstruction,instantiate,Template.command,ht,Cut.rule,templateCurrent,templateHeight]
      constructor
      · trivial
      · rfl
  · have HB : (commands initial rs (records_bound P R hroom _)).length≤b := by rw [commands_length]; exact Nat.le_of_not_gt hb
    have HI : chronological (commands initial rs (records_bound P R hroom _)) b=none := by
      unfold chronological
      exact List.getElem?_eq_none (by rw [List.length_reverse]; exact HB)
    have HE : IntegralMixedFramedHistoryFamilyBits.instruction P (plan P base R hroom) key=fallbackI := by
      change (chronological (commands initial rs (records_bound P R hroom _)) b).getD fallbackI=fallbackI
      rw [HI]
      rfl
    have HR : rs.reverse[b]?=none := List.getElem?_eq_none (by rw [List.length_reverse]; exact Nat.le_of_not_gt hb)
    have Hcurrent : current P R key=false := by
      change (rs.reverse[b]?.map (fun r => templateCurrent r.template)).getD false=false
      rw [HR]
      rfl
    have Hheight : height P R key=0 := by
      change (rs.reverse[b]?.map (fun r => templateHeight r.template)).getD 0=0
      rw [HR]
      rfl
    rw [HE,Hcurrent,Hheight]
    constructor <;> rfl

structure Metadata : Prop where
  current_FP : (fun key => [current P R key])∈FP
  height_binary : BinaryFn (height P R)

noncomputable def unitSlope (a : Access P) (h : Metadata P R) :
    IntegralMixedFramedCurrentQHeightBits.UnitSlope P (plan P base R hroom) (data P base R hroom hn hd hW) where
  current q := current P R (IntegralMixedVirtualTaskBits.saved P q)
  current_FP := mem_FP_comp (IntegralMixedVirtualTaskBits.saved_FP P a) h.current_FP
  height q := height P R (IntegralMixedVirtualTaskBits.saved P q)
  height_binary := h.height_binary.comp (IntegralMixedVirtualTaskBits.saved_FP P a)
  height_eq _q := (fields P base R hroom hn hd hW _).1
  slope_eq _q := (fields P base R hroom hn hd hW _).2
end LeanCanny.Algebra.IntegralMixedCausalPlanBits
