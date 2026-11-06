/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendConstruct
/-! # Two proper sides retain the same complete pre-child scalar history -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedChronologicalLevelScalarValues
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  canonicalObservation compiledProgram fullObservation
private theorem levelValues_before_child {dim base :ℕ} {frozen :Finset (Fin (dim+1))}
    (pm pl pr :Fin (dim+1)→ℝ) (v :Fin base→ℝ)
    (coord :Fin (dim+1)) (sels :List (IntegralMixedPointCompanion.Free frozen))
    (i :Fin (base+1+sels.length+1+sels.length)) (hi : sels.length + 1 ≤ (i : ℕ)) :
    levelValues pm pl v coord sels i=levelValues pm pr v coord sels i:=by
  let j :Fin (base+1+sels.length):=⟨i.val-sels.length-1,by have :=i.isLt;omega⟩
  have HE :i.val=sels.length+(1+j.val):=by dsimp only [j];omega
  have H (p :Fin (dim+1)→ℝ) :levelValues pm p v coord sels i=
      IntegralMixedPointCompanion.values pm (Fin.cons (pm coord) v) sels j:=by
    unfold levelValues
    have HH:=IntegralMixedPointCompanion.values_old p
      (Fin.cons (p coord) (IntegralMixedPointCompanion.values pm (Fin.cons (pm coord) v) sels))
      sels (⟨1+j.val,by have :=j.isLt;omega⟩ :Fin (base+1+sels.length+1))
    have HI :i=(⟨sels.length+(1+j.val),by have :=j.isLt;omega⟩ :Fin (base+1+sels.length+1+sels.length)):=Fin.ext HE
    rw [HI]
    apply HH.trans
    have HJ :(⟨1+j.val,by have :=j.isLt;omega⟩ :Fin (base+1+sels.length+1))=j.succ:=Fin.ext (by simp only [Fin.val_succ];omega)
    rw [HJ]
    rfl
  exact (H pl).trans (H pr).symm

variable {old : List Bool} {hv : FormulaSignSlotRadialProviderAtomic.Valid old}
  {hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old}
  {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right}
  {pMID pChildL pChildR : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
    (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he
local notation "g" => FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he
local notation "K" => List.length (R.orderedFree hk)
local notation "m" => List.length cs+List.length R.result.commands

theorem SampledLevel.before_child_fields
    (SL : SampledLevel old hv hd left right R false pMID pChildL)
    (SR : SampledLevel old hv hd left right R true pMID pChildR) (b : ℕ) (hb : b<m+1+K) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec false))
      SL.receipt.word SL.receipt.valid b=
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec true))
      SR.receipt.word SR.receipt.valid b := by
  have HL := SL.local_values_count
  have HR := SR.local_values_count
  let idx : Fin (m+1+K+1+K) := ⟨m+1+K+1+K-1-b,by omega⟩
  have HIL := SL.local_value_at idx
  have HIR := SR.local_value_at idx
  have HE : m+1+K+1+K-1-idx.val=b := by dsimp only [idx];omega
  rw [←HL,HE] at HIL
  rw [←HR,HE] at HIR
  exact HIL.trans ((levelValues_before_child pMID pChildL pChildR R.result.nextValues g
    (R.orderedFree hk) idx (by dsimp only [idx];omega)).trans HIR.symm)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
