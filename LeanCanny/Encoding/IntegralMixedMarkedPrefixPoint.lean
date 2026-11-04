/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixFieldReadback
public import LeanCanny.Geometry.IntegralMixedFramedCriticalQuotients
/-! # Every chronological prefix reads its bank from the same full natural tuple -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPrefixPoint
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex (arity slotNumber)
open IntegralMixedFramedRunObservation (ofCommands)
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem point_congr {n S B :ℕ} {Q :SpatialSource n} (x :State Q S B 0 (Fin 0))
    (cs :List (Instruction n B)) (hc :cs.length≤S+1) (z v :ℕ→ℝ)
    (he :∀k<arity cs,z k=v k) (i :Fin cs.length) :
    (ofCommands x cs hc).point z i.val=(ofCommands x cs hc).point v i.val:=by
  dsimp only [IntegralMixedFramedRunObservation.Data.point,ofCommands,
    IntegralMixedFramedBankObservation.ofState,IntegralMixedFramedBankObservation.Data.point]
  rw [dite_eq_left i.isLt,dite_eq_left i.isLt]
  rw [he (slotNumber cs i.val) (by
    rw [←IntegralMixedFramedPhysicalIndex.enumerate_scalar cs i]
    exact (IntegralMixedFramedPhysicalIndex.enumerate cs (IntegralMixedFramedPhysicalIndex.scalarSlot cs i)).isLt)]

theorem point_paddedPast {n S B :ℕ} {Q :SpatialSource n} (x :State Q S B 0 (Fin 0))
    (cs :List (Instruction n B)) (fallback :Instruction n B) (hc :cs.length≤S+1)
    (m :ℕ) (hm :m≤cs.length) (z :ℕ→ℝ) (i :Fin m) :
    (ofCommands x (paddedPast fallback cs m) (by rw [paddedPast_length];omega)).point z i.val=
      (ofCommands x cs hc).point z (cs.length-m+i.val):=by
  have HL :(cs.drop (cs.length-m)).length=m:=by rw [List.length_drop];omega
  have HP :paddedPast fallback cs m=cs.drop (cs.length-m):=by
    rw [paddedPast_valid fallback cs m hm]
    simp only [past,List.reverse_take,List.length_reverse,List.reverse_reverse]
  have HJ :i.val<(cs.drop (cs.length-m)).length:=by rw [HL];exact i.isLt
  have HH:=IntegralMixedFramedCriticalReadback.point_append x (cs.take (cs.length-m))
    (cs.drop (cs.length-m)) (by rw [List.take_append_drop];exact hc)
    (by rw [List.length_drop];omega) z ⟨i.val,HJ⟩
  simp only [List.take_append_drop,List.length_take,min_eq_left (Nat.sub_le _ _)] at HH
  simpa only [HP] using HH.symm

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters IntegralMixedAuxiliaryMarkedRecordPlan.plan

/-- A prefix quotient is the literal chronological field of its OWN full word. -/
theorem value (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (IntegralMixedMarkedPrefixFieldReadback.context root) w)
    (j :ℕ) (hj :j≤IntegralMixedCausalRecordPlanBits.count root)
    (i :ℕ) (hi :i<number n root+8+j) :
    (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root j hj).point
      (IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 root w hw) i=
      IntegralMixedPhysicalFieldEquality.pointNewest hn ht ha (radius_binary hR0)
        (IntegralMixedMarkedPrefixFieldReadback.context root) w hw
          (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root-(number n root+8+j)+i):=by
  let z:=IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 root w hw
  have HM :number n root+8+j≤((D).rules root).length:=by
    rw [IntegralMixedMarkedPrefixFieldReadback.rules_length hn ht ha hR0]
    unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
    omega
  have H0:=point_paddedPast (IntegralMixedFramedHistoryFamilyBits.initial P D root) ((D).rules root)
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root)
    (IntegralMixedMarkedPrefixFieldReadback.room hn ht ha hR0 root) (number n root+8+j) HM z ⟨i,hi⟩
  have H1:=IntegralMixedMarkedPrefixFieldReadback.full_value hn ht ha hR0 root w hw
    (((D).rules root).length-(number n root+8+j)+i) (by
      rw [IntegralMixedPhysicalFieldEquality.count_eq]
      simp only [IntegralMixedMarkedPrefixFieldReadback.context,pairFst_pair]
      rw [IntegralMixedMarkedPrefixFieldReadback.rules_length hn ht ha hR0]
      unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
      omega)
  rw [IntegralMixedMarkedPrefixFieldReadback.rules_length hn ht ha hR0] at H0 H1
  exact H0.trans H1

end LeanCanny.Encoding.IntegralMixedMarkedPrefixPoint
