/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixRun
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshot
/-! # The actual coefficient algebra before a reserved probe replacement -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedPrefixSnapshot (ofCommands)
open IntegralMixedAuxiliaryMarkedIntegerSource (candidate number)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)

noncomputable def snapshot (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :=
  ofCommands (initial P D root) (paddedPast (defaultInstruction P D root) ((D).rules root) (number n root+8+j))
    (by rw [paddedPast_length];exact (IntegralMixedMarkedPrefixRun.bound hn ht ha hR0 root j hj).trans (Nat.le_succ _))

theorem birth (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :
    (snapshot hn ht ha hR0 root j hj).birth=number n root+8+j:=
 (IntegralMixedPrefixSnapshot.ofCommands_birth (initial P D root)
   (paddedPast (defaultInstruction P D root) ((D).rules root) (number n root+8+j)) _).trans
   (paddedPast_length (defaultInstruction P D root) ((D).rules root) (number n root+8+j))

theorem canonical (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :
    Canonical (snapshot hn ht ha hR0 root j hj).state:=
 IntegralMixedPrefixSnapshot.ofCommands_canonical _ (fun i=>Fin.elim0 i) _ _

theorem realizes_at (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root)
    (values : ℕ→ℝ)
    (hv : IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedFamilyRunView.runAt P D root (number n root+8+j)
        (IntegralMixedMarkedPrefixRun.bound hn ht ha hR0 root j hj)) values) :
    IntegralMixedIntegerRealization.Realizes (snapshot hn ht ha hR0 root j hj).state values:=
 (IntegralMixedPrefixSnapshot.ofCommands_realizes _ _ _ values).mpr hv

private theorem commands_congr {a S B : ℕ} {Q : SpatialSource a} (x : State Q S B 0 (Fin 0))
    (cs ds : List (Instruction a B)) (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :
    ofCommands x cs hc=ofCommands x ds hd :=by cases he;rfl

theorem factor (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :
    snapshot hn ht ha hR0 root j hj=
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
    snapshot hn ht ha hR0 cL j hj=snapshot hn ht ha hR0 cR j (hj.trans_eq hcount) :=by
  rw [factor hn ht ha hR0 cL j hj,factor hn ht ha hR0 cR j (hj.trans_eq hcount)]
  apply IntegralMixedPrefixSnapshot.prefix_congr
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

theorem reserved_eq (old : List Bool) (codes : List (List Bool)) (p q a b : List Bool) :
    snapshot hn ht ha hR0 (IntegralMixedMarkedPrefixRun.reservedRoot old codes p a) codes.length
      (by rw [IntegralMixedMarkedPrefixRun.reserved_count];omega)=
    snapshot hn ht ha hR0 (IntegralMixedMarkedPrefixRun.reservedRoot old codes q b) codes.length
      (by rw [IntegralMixedMarkedPrefixRun.reserved_count];omega) :=by
  apply eq hn ht ha hR0
  · simp only [candidate,IntegralMixedMarkedPrefixRun.reservedRoot,pairFst_pair]
  · rw [IntegralMixedMarkedPrefixRun.reserved_count,IntegralMixedMarkedPrefixRun.reserved_count]
  · exact fun i hi=>IntegralMixedMarkedPrefixRun.reserved_prefix old codes p q a b i hi
end LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshot
