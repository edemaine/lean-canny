/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordSource
public import LeanCanny.Algebra.IntegralMixedCausalUnitBounds
public import LeanCanny.Algebra.IntegralMixedFramedPrefixHeight
/-! # Original source bounds charge the entire causal continuation

Current-Q slopes are bounded by the causal bank induction. The hypotheses
bound original sources and original integer coefficients only; no current
bank, matrix or stage evaluator bound is assumed.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedCausalRecordBits IntegralMixedFramedHistoryScript
open IntegralMixedFramedStepHeight IntegralMixedCausalPlanBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem core_mono {n B C E L : ℕ} {Q : SpatialSource n} (h : C≤E)
    (r : Template Q B) (hr : Template.core C L r) : Template.core E L r := by
  cases r with
  | integer p hp hd => exact fun k=>(hr k).trans (Nat.pow_le_pow_right (by decide) h)
  | critical r => exact ⟨hr.1,fun i=>expression_coefficients_mono h _ (hr.2.1 i),fun i=>(hr.2.2 i).trans h⟩
  | cut r => exact ⟨hr.1,fun i=>expression_coefficients_mono h _ (hr.2.1 i),fun i=>(hr.2.2 i).trans h⟩

private theorem original_mono {n B G H F W D L : ℕ} (hg : G≤H) (r : Record n B)
    (h : OriginalBounds G F W D L r) : OriginalBounds H F W D L r where
  low e:=(h.low e).trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right (Nat.mul_le_mul_left F hg) 1))
  leading:=h.leading.trans (Nat.add_le_add_right (Nat.mul_le_mul_left F hg) 1)
  width:=h.width
  degree:=h.degree
  auxiliary:=h.auxiliary
  command:=core_mono (Nat.add_le_add_right (Nat.mul_le_mul_left F hg) 1) r.template h.command

private theorem uniform_original {n S B W D L F C : ℕ} (rs : List (Record n B))
    (h : ∀r∈rs,OriginalBounds (C+1) F W D L r) : OriginalScript S W D L F C rs := by
  induction rs with
  | nil => trivial
  | cons r rs ih =>
    refine ⟨ih (fun s hs=>h s (List.mem_cons_of_mem r hs)),?_⟩
    exact original_mono (source_le_height n S B W D L F C rs.length) r (h r List.mem_cons_self)

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ)
  (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (S root 0).degree≤2^P.width root)
  (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
  (L F C : List Bool→ℕ)

/-- The source-only portion of an original instruction; the default X branch
has no dependence on any interpreted bank. -/
theorem original_records_bounds
    (hb : ∀root b,InstructionBounds (C root+1) (F root) (P.sourceWidth root) (P.degree root) (L root)
      (⟨S root b,by rw [hd]; exact (by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K; omega :
        PurePowerReductionBounds.dimension (P.ambient root+1) (P.degree root)≤
          IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)).trans (hcap root),
        IntegralMixedFullHistoryScript.defaultCommand⟩ : Instruction (P.ambient root) (P.width root)))
    (hm : ∀root i,i<N root→T.mass (pair root (BinaryNatCode.encode i))≤F root*(C root+1)+1)
    (hC : ∀root,2≤F root*(C root+1)+1) (hL : ∀root,3≤L root) (root : List Bool) :
    ∀r∈originalRecords P S hn hd hcap N hq T hz hT root,
      OriginalBounds (C root+1) (F root) (P.sourceWidth root) (P.degree root) (L root) r := by
  intro r hr
  rw [originalRecords,List.mem_append] at hr
  rcases hr with hr|hr
  · rw [later,List.mem_reverse] at hr
    obtain ⟨b,_,rfl⟩:=List.mem_map.mp hr
    unfold step
    exact IntegralMixedCausalUnitRecordBits.original_bounds _ (hn root) _ _ _ _ _ _ _ _
      (hb root (N root+b)).low (hb root (N root+b)).leading (hb root (N root+b)).width
      (hb root (N root+b)).degree (hC root) (hL root)
  · obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hr
    refine ⟨(hb root 0).low,(hb root 0).leading,(hb root 0).width,(hb root 0).degree,(hb root 0).auxiliary,?_⟩
    intro k
    exact ((coeff_natAbs_le_coefficientMass _ k).trans (T.mass_bound _)).trans
      (Nat.pow_le_pow_right (by decide) (hm root (N root-1-i.val) (by have H:=i.isLt; omega)))

include hq in
theorem familyInputs
    (hF : ∀root,P.cap root+1≤F root)
    (hb : ∀root b,InstructionBounds (C root+1) (F root) (P.sourceWidth root) (P.degree root) (L root)
      (⟨S root b,by rw [hd]; exact (by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K; omega :
        PurePowerReductionBounds.dimension (P.ambient root+1) (P.degree root)≤
          IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)).trans (hcap root),
        IntegralMixedFullHistoryScript.defaultCommand⟩ : Instruction (P.ambient root) (P.width root)))
    (hm : ∀root i,i<N root→T.mass (pair root (BinaryNatCode.encode i))≤F root*(C root+1)+1)
    (hC : ∀root,2≤F root*(C root+1)+1) (hL : ∀root,3≤L root) :
    FamilyInputs P (plan P S hn hd hcap N T hz hT hroom) L F C := by
  rw [plan_as_causal P S hn hd hcap N hq T hz hT hroom]
  apply IntegralMixedCausalPlanBits.familyInputs P (base P S hd hcap N T hz hT hroom)
    (originalRecords P S hn hd hcap N hq T hz hT) (records_room P S hn hd hcap N hq T hz hT hroom) L F C hF
  · intro root
    exact uniform_original _ (original_records_bounds P S hn hd hcap N hq T hz hT L F C hb hm hC hL root)
  · intro root
    exact hb root 0

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
