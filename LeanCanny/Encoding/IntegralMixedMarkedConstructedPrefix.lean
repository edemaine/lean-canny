/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedRecordContinuation
public import LeanCanny.Encoding.IntegralFramedPhysicalPrefixObservation
public import LeanCanny.Algebra.IntegralMixedFramedFixedTupleContinuation
/-! # The actual marked prefix has exactly the decoded local command list

The entire physical instruction list is preserved. No whole-history
realization premise, evaluator, or sample-word transport is introduced.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedConstructedPrefix
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

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
local notation "poly" root=>IntegralMixedMarkedPrefixRecords.polynomial hn ht ha (R0:=R0) root
local notation "nonzero" root=>IntegralMixedMarkedPrefixRecords.polynomial_nonzero hn ht ha (R0:=R0) root
local notation "degree" root=>IntegralMixedMarkedPrefixRecords.polynomial_degree hn ht ha hR0 root
attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap

noncomputable def state (root :List Bool) (j :ℕ) (hj :j≤count root) :
    State (Q root) ((P).cap root+1) ((P).width root)
      (IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root j hj).length
      (Index (Fin 0) (IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root j hj)):=
  IntegralMixedMarkedRecordContinuation.start hn ht ha hR0 root j hj


theorem compiled_commands (root :List Bool) (j :ℕ) (jgood :j≤count root) (codes :List (List Bool))
    (hj :j+codes.length≤count root)
    (hw :∀i,i<codes.length→(code root) (j+i)=(codes.reverse[i]?).getD [])
    (cs :List (IntegralMixedFullHistoryScript.Command (Q root) ((P).width root)))
    (hc :(IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root j jgood).length+
      cs.length≤(P).cap root+1+1)
    (HD :IntegralMixedOptionalEndpoints.Decodes
      (state hn ht ha hR0 root j jgood)
      (positive root) (cap root) cs hc codes)
 :
    paddedPast (defaultInstruction P D root) ((D).rules root) (number n root+8+j+codes.length)=
      (cs.map (IntegralMixedFramedFixedContinuation.wrap (Q root) (IntegralMixedStaticRecordPrefix.cap (Q root) (cap root))) :
        List (Instruction ((P).ambient root) ((P).width root)))++
        IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root j jgood:=by
  have HD' :IntegralMixedOptionalEndpoints.Decodes
      (IntegralMixedMarkedRecordContinuation.start hn ht ha hR0 root j jgood)
      (positive root) (cap root) cs hc codes:=by simpa only [state] using HD
  have HE:=IntegralMixedStaticRecordContinuation.prefix_commands (Q root) (positive root) (cap root)
    (number n root+8) (count root) (poly root) (nonzero root) (degree root) (code root)
    (initial P D root) (IntegralMixedMarkedPrefixRecords.room hn ht ha hR0 root)
    (defaultInstruction P D root) j codes hj hw cs hc HD'
  have HR:=congrArg (fun ds=>paddedPast (defaultInstruction P D root) ds (number n root+8+j+codes.length))
    (IntegralMixedMarkedPrefixRecords.rules hn ht ha hR0 root)
  exact HR.trans HE

end LeanCanny.Encoding.IntegralMixedMarkedConstructedPrefix
