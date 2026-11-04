/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedConstructedPrefix
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackInstruction
/-! # Each constructed local birth is the actual marked creating instruction -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedConstructedPrefix
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem appended_chronological {n B :ℕ} (Q :SpatialSource n)
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (cs :List (IntegralMixedFullHistoryScript.Command Q B)) (older :List (Instruction n B)) (i :Fin cs.length) :
    chronological (cs.map (IntegralMixedFramedFixedContinuation.wrap Q hQ)++older) (older.length+i.val)=
      some (IntegralMixedFramedFixedContinuation.wrap Q hQ
        (cs.reverse.get ⟨i.val,by rw [List.length_reverse];exact i.isLt⟩)):=by
  unfold chronological
  rw [List.reverse_append,←List.map_reverse,List.getElem?_append_right (by rw [List.length_reverse];omega),
    List.length_reverse,Nat.add_sub_cancel_left,List.getElem?_map,
    List.getElem?_eq_getElem (by rw [List.length_reverse];exact i.isLt)]
  rfl

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root
local notation "positive" root=>IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha root
local notation "cap" root=>IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 root
local notation "count" root=>IntegralMixedCausalRecordPlanBits.count root
local notation "code" root=>IntegralMixedCausalRecordPlanBits.code root
attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap

theorem instruction_receipt (root :List Bool) (j :ℕ) (jgood :j≤count root) (codes :List (List Bool))
    (hj :j+codes.length≤count root)
    (hw :∀i,i<codes.length→(code root) (j+i)=(codes.reverse[i]?).getD [])
    (cs :List (IntegralMixedFullHistoryScript.Command (Q root) ((P).width root)))
    (hc :(IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root j jgood).length+
      cs.length≤(P).cap root+1+1)
    (HD :IntegralMixedOptionalEndpoints.Decodes (state hn ht ha hR0 root j jgood)
      (positive root) (cap root) cs hc codes)
    (i :Fin cs.length) :
    IntegralMixedFramedRootPullback.instructionAt P D root
      ((IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root j jgood).length+i.val)=
      (show Instruction ((P).ambient root) ((P).width root) from
        IntegralMixedFramedFixedContinuation.wrap (Q root) (IntegralMixedStaticRecordPrefix.cap (Q root) (cap root))
          (cs.reverse.get ⟨i.val,by rw [List.length_reverse];exact i.isLt⟩)):=by
  let older:=IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root j jgood
  have HL:=IntegralMixedCausalUnitContinuation.decode_length (state hn ht ha hR0 root j jgood)
    (positive root) (cap root) cs hc codes HD
  have HB :older.length+i.val<number n root+8+j+codes.length:=by
    dsimp only [older]
    rw [IntegralMixedMarkedRecordContinuation.oldCommands_length]
    have HI:=i.isLt
    omega
  have HC:=compiled_commands hn ht ha hR0 root j jgood codes hj hw cs hc HD
  have HE:=congrArg (fun ds=>chronological ds (older.length+i.val)) HC
  rw [appended_chronological] at HE
  have HP:=paddedPast_chronological (defaultInstruction P D root) ((D).rules root)
    (number n root+8+j+codes.length) (older.length+i.val) HB
  exact Option.some.inj (HP.symm.trans HE)

end LeanCanny.Encoding.IntegralMixedMarkedConstructedPrefix
