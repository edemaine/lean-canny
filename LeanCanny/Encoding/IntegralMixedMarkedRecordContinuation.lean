/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedStaticRecordContinuation
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixRun
/-! # Actual marked-plan prefixes execute the decoded full local program

The root, horizon and width remain fixed. Only literal original byte slices
are compared. No complete word is transported by this interpreter identity.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedRecordContinuation
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem at_congr (A :Parameters) (E :IntegralMixedFramedHistoryFamilyBits.Plan A)
    (r s :List Bool) (u v :ℕ) (hr :r=s) (hu :u=v) (hc :u≤A.cap r+1) (hd :v≤A.cap s+1)
    {a :ℕ} (Q :SpatialSource a)
    (hQ :PurePowerReductionBounds.dimension (a+1) Q.degree≤2^A.width r)
    (hQ' :PurePowerReductionBounds.dimension (a+1) Q.degree≤2^A.width s) :
    HEq (IntegralMixedFramedFamilyRunView.reframeRunAt A E r u hc Q hQ)
      (IntegralMixedFramedFamilyRunView.reframeRunAt A E s v hd Q hQ'):=by
  cases hr
  cases hu
  rfl

noncomputable def framedState (A :Parameters) (E :IntegralMixedFramedHistoryFamilyBits.Plan A)
    (J :IntegralMixedFramedHistoryFamilyBits.Data A E) (key :List Bool) {a :ℕ} (Q :SpatialSource a)
    (hQ :PurePowerReductionBounds.dimension (a+1) Q.degree≤2^A.width (pairFst key)) :
    State Q (A.cap (pairFst key)+1) (A.width (pairFst key))
      ((IntegralMixedFramedHistoryFamilyBits.family A E J).birth key)
      ((IntegralMixedFramedHistoryFamilyBits.family A E J).physical key):=
  reframe ((IntegralMixedFramedHistoryFamilyBits.family A E J).state key) Q hQ

private theorem family_at (A :Parameters) (E :IntegralMixedFramedHistoryFamilyBits.Plan A)
    (J :IntegralMixedFramedHistoryFamilyBits.Data A E) (root aux :List Bool) (b :ℕ) (hb :b≤A.cap root+1)
    {a :ℕ} (Q :SpatialSource a)
    (hQ :PurePowerReductionBounds.dimension (a+1) Q.degree≤2^A.width root)
    (hQ' :PurePowerReductionBounds.dimension (a+1) Q.degree≤2^A.width
      (pairFst (IntegralMixedFramedHistoryFamilyBits.keyAt root b aux))) :
    HEq (framedState A E J (IntegralMixedFramedHistoryFamilyBits.keyAt root b aux) Q hQ')
      (reframe (IntegralMixedFramedFamilyRunView.runAt A E root b hb) Q hQ):=by
  unfold framedState
  refine (heq_of_eq (IntegralMixedFramedFamilyRunView.family_reframe A E J _ Q hQ')).trans ?_
  exact at_congr A E _ root _ b (IntegralMixedFramedHistoryFamilyBits.keyAt_root root b aux)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix A root b aux hb) (min_le_right _ _) hb Q hQ' hQ

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root
local notation "positive" root=>IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha root
local notation "cap" root=>IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 root
local notation "count" root=>IntegralMixedCausalRecordPlanBits.count root
local notation "poly" root=>IntegralMixedMarkedPrefixRecords.polynomial hn ht ha (R0:=R0) root
local notation "nonzero" root=>IntegralMixedMarkedPrefixRecords.polynomial_nonzero hn ht ha (R0:=R0) root
local notation "degree" root=>IntegralMixedMarkedPrefixRecords.polynomial_degree hn ht ha hR0 root
local notation "code" root=>IntegralMixedCausalRecordPlanBits.code root

noncomputable def records_before (root :List Bool) (j :ℕ):=
  IntegralMixedStaticRecordContinuation.prefixRecords (Q root) (positive root) (cap root)
    (number n root+8) (count root) (poly root) (nonzero root) (degree root) (code root) j

theorem records_before_length (root :List Bool) (j :ℕ) (hj :j≤count root) :
    (records_before hn ht ha hR0 root j).length=number n root+8+j:=
  IntegralMixedStaticRecordContinuation.prefixRecords_length (Q root) (positive root) (cap root)
    (number n root+8) (count root) (poly root) (nonzero root) (degree root) (code root) j hj

theorem room_before (root :List Bool) (j :ℕ) (hj :j≤count root) :
    (records_before hn ht ha hR0 root j).length≤(P).cap root+1+1:=by
  rw [records_before_length hn ht ha hR0 root j hj]
  change number n root+8+j≤number n root+8+(count root)+2+1+1
  omega

noncomputable def oldCommands (root :List Bool) (j :ℕ) (hj :j≤count root):=
  IntegralMixedCausalPlanBits.commands (initial P D root) (records_before hn ht ha hR0 root j)
    (room_before hn ht ha hR0 root j hj)

theorem oldCommands_length (root :List Bool) (j :ℕ) (hj :j≤count root) :
    (oldCommands hn ht ha hR0 root j hj).length=number n root+8+j:=by
  rw [oldCommands,IntegralMixedCausalPlanBits.commands_length,records_before_length hn ht ha hR0 root j hj]

noncomputable def start (root :List Bool) (j :ℕ) (hj :j≤count root):=
  IntegralMixedCausalUnitContinuation.start (initial P D root) (Q root) (cap root)
    (records_before hn ht ha hR0 root j) (room_before hn ht ha hR0 root j hj)

theorem full_bound (root :List Bool) (b :ℕ) (hb :b≤number n root+8+count root) :b≤(P).cap root+1:=by
  change b≤number n root+8+(count root)+2+1
  omega

theorem factor_reframe (root :List Bool) (b :ℕ) (hb :b≤number n root+8+count root) :
    HEq (reframe (IntegralMixedFramedFamilyRunView.runAt P D root b (full_bound hn ht ha hR0 root b hb))
      (Q root) (IntegralMixedStaticRecordPrefix.cap (Q root) (cap root)))
      (reframe (IntegralMixedCausalPrefixCongruence.prefixRun (initial P D root)
        (IntegralMixedMarkedPrefixRecords.records hn ht ha hR0 root)
        (IntegralMixedMarkedPrefixRecords.room hn ht ha hR0 root) (defaultInstruction P D root) b
        (by rw [IntegralMixedMarkedPrefixRecords.length];omega))
        (Q root) (IntegralMixedStaticRecordPrefix.cap (Q root) (cap root))):=by
  unfold IntegralMixedFramedFamilyRunView.runAt IntegralMixedCausalPrefixCongruence.prefixRun
  exact IntegralMixedCausalUnitContinuation.reframe_run_congr (initial P D root) _ _ _ _
    (congrArg (fun cs=>paddedPast (defaultInstruction P D root) cs b)
      (IntegralMixedMarkedPrefixRecords.rules hn ht ha hR0 root)) (Q root) _

theorem start_actual (root :List Bool) (j :ℕ) (hj :j≤count root) :
    HEq (start hn ht ha hR0 root j hj)
      (reframe (IntegralMixedFramedFamilyRunView.runAt P D root (number n root+8+j)
        (full_bound hn ht ha hR0 root _ (by omega))) (Q root)
        (IntegralMixedStaticRecordPrefix.cap (Q root) (cap root))):=by
  have HG:=IntegralMixedStaticRecordContinuation.start_actual (Q root) (positive root) (cap root)
    (number n root+8) (count root) (poly root) (nonzero root) (degree root) (code root)
    (initial P D root) (IntegralMixedMarkedPrefixRecords.room hn ht ha hR0 root)
    (defaultInstruction P D root) j hj
  exact HG.trans (factor_reframe hn ht ha hR0 root _ (by omega)).symm

theorem runAt (root :List Bool) (j :ℕ) (codes :List (List Bool))
    (hj :j+codes.length≤count root)
    (hw :∀i,i<codes.length→(code root) (j+i)=(codes.reverse[i]?).getD [])
    (cs :List (IntegralMixedFullHistoryScript.Command (Q root) ((P).width root)))
    (hc :(oldCommands hn ht ha hR0 root j (by omega)).length+cs.length≤(P).cap root+1+1)
    (HD :LeanCanny.Geometry.IntegralMixedOptionalEndpoints.Decodes
      (start hn ht ha hR0 root j (by omega)) (positive root) (cap root) cs hc codes) :
    HEq (reframe (IntegralMixedFramedFamilyRunView.runAt P D root (number n root+8+j+codes.length)
      (full_bound hn ht ha hR0 root _ (by omega))) (Q root)
      (IntegralMixedStaticRecordPrefix.cap (Q root) (cap root)))
      (IntegralMixedFullHistoryScript.continueRun (start hn ht ha hR0 root j (by omega)) cs hc):=by
  have HG:=IntegralMixedStaticRecordContinuation.prefix_run (Q root) (positive root) (cap root)
    (number n root+8) (count root) (poly root) (nonzero root) (degree root) (code root)
    (initial P D root) (IntegralMixedMarkedPrefixRecords.room hn ht ha hR0 root)
    (defaultInstruction P D root) j codes hj hw cs hc HD
  exact (factor_reframe hn ht ha hR0 root _ (by omega)).trans HG

theorem family_run (root aux :List Bool) (j :ℕ) (codes :List (List Bool))
    (hj :j+codes.length≤count root)
    (hw :∀i,i<codes.length→(code root) (j+i)=(codes.reverse[i]?).getD [])
    (cs :List (IntegralMixedFullHistoryScript.Command (Q root) ((P).width root)))
    (hc :(oldCommands hn ht ha hR0 root j (by omega)).length+cs.length≤(P).cap root+1+1)
    (HD :LeanCanny.Geometry.IntegralMixedOptionalEndpoints.Decodes
      (start hn ht ha hR0 root j (by omega)) (positive root) (cap root) cs hc codes) :
    HEq (framedState P D (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha (radius_binary hR0))
      (IntegralMixedFramedHistoryFamilyBits.keyAt root (number n root+8+j+codes.length) aux) (Q root)
      (by rw [IntegralMixedFramedHistoryFamilyBits.keyAt_root];exact IntegralMixedStaticRecordPrefix.cap (Q root) (cap root)))
      (IntegralMixedFullHistoryScript.continueRun (start hn ht ha hR0 root j (by omega)) cs hc):=
  (family_at P D (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha (radius_binary hR0)) root aux _
    (full_bound hn ht ha hR0 root _ (by omega)) (Q root) (IntegralMixedStaticRecordPrefix.cap (Q root) (cap root))
    (by rw [IntegralMixedFramedHistoryFamilyBits.keyAt_root];exact IntegralMixedStaticRecordPrefix.cap (Q root) (cap root))).trans
    (runAt hn ht ha hR0 root j codes hj hw cs hc HD)

theorem runAt_index (root :List Bool) (j :ℕ) (codes :List (List Bool))
    (hj :j+codes.length≤count root)
    (hw :∀i,i<codes.length→(code root) (j+i)=(codes.reverse[i]?).getD [])
    (cs :List (IntegralMixedFullHistoryScript.Command (Q root) ((P).width root)))
    (hc :(oldCommands hn ht ha hR0 root j (by omega)).length+cs.length≤(P).cap root+1+1)
    (HD :LeanCanny.Geometry.IntegralMixedOptionalEndpoints.Decodes
      (start hn ht ha hR0 root j (by omega)) (positive root) (cap root) cs hc codes) :
    IntegralMixedFramedHistoryScript.Index (Fin 0)
      (paddedPast (defaultInstruction P D root) ((D).rules root) (number n root+8+j+codes.length))=
      IntegralMixedFullHistoryScript.Index
        (IntegralMixedFramedHistoryScript.Index (Fin 0) (oldCommands hn ht ha hR0 root j (by omega))) cs:=by
  have HE:=IntegralMixedStaticRecordContinuation.prefix_commands (Q root) (positive root) (cap root)
    (number n root+8) (count root) (poly root) (nonzero root) (degree root) (code root)
    (initial P D root) (IntegralMixedMarkedPrefixRecords.room hn ht ha hR0 root)
    (defaultInstruction P D root) j codes hj hw cs hc HD
  have HR:=congrArg (fun ds=>paddedPast (defaultInstruction P D root) ds (number n root+8+j+codes.length))
    (IntegralMixedMarkedPrefixRecords.rules hn ht ha hR0 root)
  exact (congrArg (IntegralMixedFramedHistoryScript.Index (Fin 0)) (HR.trans HE)).trans
    (IntegralMixedFramedFixedContinuation.index_append (Q root) (IntegralMixedStaticRecordPrefix.cap (Q root) (cap root)) cs _)

end LeanCanny.Encoding.IntegralMixedMarkedRecordContinuation
