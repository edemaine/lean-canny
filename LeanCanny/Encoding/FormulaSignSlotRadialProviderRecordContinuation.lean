/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
public import LeanCanny.Algebra.IntegralMixedStaticRecordContinuation
/-! # Actual provider prefixes execute literal point-companion continuations -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordContinuation
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
local notation "C" => IntegralMixedCausalRecordPlanBits.count
local notation "cap" => FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap
local notation "poly" => FormulaSignSlotRadialProviderRecordReceipt.polynomial
local notation "nonzero" => FormulaSignSlotRadialProviderRecordReceipt.polynomial_nonzero
local notation "degree" => FormulaSignSlotRadialProviderRecordReceipt.polynomial_degree
local notation "positive" => FormulaSignSlotRadialProviderRecordPlan.positive
local notation "code" => IntegralMixedCausalRecordPlanBits.code

theorem record_room (root : List Bool) :
    (IntegralMixedStaticRecordPrefix.records (Q root) (positive root) (cap root)
      (N root) (C root) (poly root) (nonzero root) (degree root) (code root)).length≤(P).cap root+1+1 := by
  have H := FormulaSignSlotRadialProviderRecordReceipt.room root
  change (FormulaSignSlotRadialProviderRecordReceipt.records root).length≤_
  omega

noncomputable def beforeRecords (root : List Bool) (j : ℕ) :=
  IntegralMixedStaticRecordContinuation.prefixRecords (Q root) (positive root) (cap root)
    (N root) (C root) (poly root) (nonzero root) (degree root) (code root) j

theorem beforeRecords_length (root : List Bool) (j : ℕ) (hj : j≤C root) :
    (beforeRecords root j).length=N root+j :=
  IntegralMixedStaticRecordContinuation.prefixRecords_length _ _ _ _ _ _ _ _ _ j hj

theorem before_room (root : List Bool) (j : ℕ) (hj : j≤C root) :
    (beforeRecords root j).length≤(P).cap root+1+1 := by
  rw [beforeRecords_length root j hj]
  exact (FormulaSignSlotRadialProviderRecordPrefix.bound root j hj).trans (Nat.le_succ _)

noncomputable def beforeCommands (root : List Bool) (j : ℕ) (hj : j≤C root) :=
  IntegralMixedCausalPlanBits.commands (initial P D root) (beforeRecords root j) (before_room root j hj)

theorem beforeCommands_length (root : List Bool) (j : ℕ) (hj : j≤C root) :
    (beforeCommands root j hj).length=N root+j := by
  rw [beforeCommands,IntegralMixedCausalPlanBits.commands_length,beforeRecords_length root j hj]

noncomputable def beforeState (root : List Bool) (j : ℕ) (hj : j≤C root) :=
  IntegralMixedStaticRecordContinuation.prefixStart (Q root) (positive root) (cap root)
    (N root) (C root) (poly root) (nonzero root) (degree root) (code root)
    (initial P D root) (record_room root) j hj

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPlan.plan FormulaSignSlotRadialProviderIntegerSource.source

theorem before_commands (root : List Bool) (j : ℕ) (hj : j≤C root) :
    paddedPast (defaultInstruction P D root) ((D).rules root) (N root+j)=beforeCommands root j hj := by
  rw [FormulaSignSlotRadialProviderRecordReceipt.rules root]
  exact IntegralMixedCausalPrefixCongruence.commands_prefix (initial P D root)
    (FormulaSignSlotRadialProviderRecordReceipt.records root) (FormulaSignSlotRadialProviderRecordReceipt.room root)
    (defaultInstruction P D root) (N root+j)
    (by rw [FormulaSignSlotRadialProviderRecordReceipt.records_length];omega)

theorem compiled_commands (root : List Bool) (j : ℕ) (hjgood : j≤C root) (codes : List (List Bool))
    (hj : j+codes.length≤C root)
    (hw : ∀i,i<codes.length→code root (j+i)=(codes.reverse[i]?).getD [])
    (cs : List (IntegralMixedFullHistoryScript.Command (Q root) ((P).width root)))
    (hc : (beforeCommands root j hjgood).length+cs.length≤(P).cap root+1+1)
    (HD : LeanCanny.Geometry.IntegralMixedOptionalEndpoints.Decodes
      (beforeState root j hjgood) (positive root) (cap root) cs hc codes) :
    paddedPast (defaultInstruction P D root) ((D).rules root) (N root+j+codes.length)=
      (cs.map (IntegralMixedFramedFixedContinuation.wrap (Q root) (IntegralMixedStaticRecordPrefix.cap (Q root) (cap root))) :
        List (Instruction ((P).ambient root) ((P).width root)))++
        beforeCommands root j hjgood := by
  have HE := IntegralMixedStaticRecordContinuation.prefix_commands (Q root) (positive root) (cap root)
    (N root) (C root) (poly root) (nonzero root) (degree root) (code root)
    (initial P D root) (record_room root)
    (defaultInstruction P D root) j codes hj hw cs hc HD
  exact (congrArg (fun ds=>paddedPast (defaultInstruction P D root) ds (N root+j+codes.length))
    (FormulaSignSlotRadialProviderRecordReceipt.rules root)).trans HE

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordContinuation
