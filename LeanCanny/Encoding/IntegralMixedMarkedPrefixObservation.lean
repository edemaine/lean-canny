/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixRun
public import LeanCanny.Algebra.IntegralMixedFramedRunObservation
/-! # Same raw tuples and quotient values before a reserved probe replacement -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPrefixObservation
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedFramedRunObservation (ofCommands)
open IntegralMixedAuxiliaryMarkedIntegerSource (candidate number)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)

noncomputable def observation (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :=
  ofCommands (initial P D root) (paddedPast (defaultInstruction P D root) ((D).rules root) (number n root+8+j))
    (by rw [paddedPast_length];exact (IntegralMixedMarkedPrefixRun.bound hn ht ha hR0 root j hj).trans (Nat.le_succ _))

private theorem commands_congr {a S B : ℕ} {Q : SpatialSource a} (x : State Q S B 0 (Fin 0))
    (cs ds : List (Instruction a B)) (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :
    ofCommands x cs hc=ofCommands x ds hd :=by cases he;rfl

theorem factor (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :
    observation hn ht ha hR0 root j hj=
      ofCommands (initial P D root)
        (paddedPast (defaultInstruction P D root)
          (IntegralMixedCausalPlanBits.commands (initial P D root) (IntegralMixedMarkedPrefixRecords.records hn ht ha hR0 root)
            (IntegralMixedMarkedPrefixRecords.room hn ht ha hR0 root)) (number n root+8+j))
        (by rw [paddedPast_length];exact (IntegralMixedMarkedPrefixRun.bound hn ht ha hR0 root j hj).trans (Nat.le_succ _)) :=by
  apply commands_congr
  exact congrArg (fun cs=>paddedPast (defaultInstruction P D root) cs (number n root+8+j))
    (IntegralMixedMarkedPrefixRecords.rules hn ht ha hR0 root)

theorem eq (cL cR : List Bool) (hc : candidate cL=candidate cR)
    (hcount : IntegralMixedCausalRecordPlanBits.count cL=IntegralMixedCausalRecordPlanBits.count cR)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count cL)
    (hcode : ∀i,i<j→IntegralMixedCausalRecordPlanBits.code cL i=IntegralMixedCausalRecordPlanBits.code cR i) :
    observation hn ht ha hR0 cL j hj=observation hn ht ha hR0 cR j (hj.trans_eq hcount) :=by
  rw [factor hn ht ha hR0 cL j hj,factor hn ht ha hR0 cR j (hj.trans_eq hcount)]
  apply IntegralMixedFramedRunObservation.prefix_congr
  · rw [IntegralMixedMarkedPrefixRecords.length]
    omega
  · rw [IntegralMixedMarkedPrefixRecords.length]
    omega
  · exact IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 cL cR hc
  · exact congrArg (·+1) (IntegralMixedMarkedPrefixParameters.cap hn ht ha hR0 cL cR hc hcount)
  · exact IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 cL cR hc
  · exact congrArg (fun b=>b+8+j) (IntegralMixedMarkedPreludeCongruence.number_eq cL cR hc)
  · exact IntegralMixedMarkedPrefixRecords.source_heq (n:=n) (t:=t) (R0:=R0) cL cR hc
  · exact IntegralMixedMarkedPrefixRecords.initial_heq hn ht ha hR0 cL cR hc hcount
  · exact IntegralMixedMarkedPrefixRecords.prefix_heq hn ht ha hR0 cL cR hc hcount j hj hcode

theorem roots_iff (cL cR : List Bool) (hc : candidate cL=candidate cR)
    (hcount : IntegralMixedCausalRecordPlanBits.count cL=IntegralMixedCausalRecordPlanBits.count cR)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count cL)
    (hcode : ∀i,i<j→IntegralMixedCausalRecordPlanBits.code cL i=IntegralMixedCausalRecordPlanBits.code cR i)
    (z : ℕ→ℝ) :
    (observation hn ht ha hR0 cL j hj).Roots z↔(observation hn ht ha hR0 cR j (hj.trans_eq hcount)).Roots z :=by
  rw [eq hn ht ha hR0 cL cR hc hcount j hj hcode]

theorem point_eq (cL cR : List Bool) (hc : candidate cL=candidate cR)
    (hcount : IntegralMixedCausalRecordPlanBits.count cL=IntegralMixedCausalRecordPlanBits.count cR)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count cL)
    (hcode : ∀i,i<j→IntegralMixedCausalRecordPlanBits.code cL i=IntegralMixedCausalRecordPlanBits.code cR i)
    (z : ℕ→ℝ) (i : ℕ) :
    (observation hn ht ha hR0 cL j hj).point z i=(observation hn ht ha hR0 cR j (hj.trans_eq hcount)).point z i :=by
  rw [eq hn ht ha hR0 cL cR hc hcount j hj hcode]

theorem reserved_eq (old : List Bool) (codes : List (List Bool)) (p q a b : List Bool) :
    observation hn ht ha hR0 (IntegralMixedMarkedPrefixRun.reservedRoot old codes p a) codes.length
      (by rw [IntegralMixedMarkedPrefixRun.reserved_count];omega)=
    observation hn ht ha hR0 (IntegralMixedMarkedPrefixRun.reservedRoot old codes q b) codes.length
      (by rw [IntegralMixedMarkedPrefixRun.reserved_count];omega) :=by
  apply eq hn ht ha hR0
  · simp only [candidate,IntegralMixedMarkedPrefixRun.reservedRoot,pairFst_pair]
  · rw [IntegralMixedMarkedPrefixRun.reserved_count,IntegralMixedMarkedPrefixRun.reserved_count]
  · exact fun i hi=>IntegralMixedMarkedPrefixRun.reserved_prefix old codes p q a b i hi
end LeanCanny.Encoding.IntegralMixedMarkedPrefixObservation
