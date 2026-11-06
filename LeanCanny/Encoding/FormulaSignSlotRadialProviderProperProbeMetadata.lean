/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProbeWords
/-! # Literal source-aware reserved probe metadata -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank creating parent terminal

theorem probe_terminal_count (mean : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) :
    count mean z=creating z+1 :=by
  simpa only [count,IntegralMixedFramedBankSnapshotBits.atKey,terminal,Function.comp_apply] using probe_full_count mean z hv

theorem probe_core (mean : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hg : FormulaSignSlotRadialProviderProperRowWitness.RowGood z) :
    IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P (parent mean) z :=by
  have HC:=row_count_positive z hv
  have HD:=parent_coordinate mean z hg
  have HA : (P).ambient (RankedHistoryTask.root (parent mean z))=dimension z:=by
    rw [parent_root,root_dimension]
  have HL:=probe_completed_length mean z hv hg
  have HM:=(D).room (pairFst (parentKey mean z))
  have HV : birth P (parent mean z)<(P).cap (RankedHistoryTask.root (parent mean z)):=by
    rw [parent_birth mean z HC,parent_root]
    rw [HL] at HM
    rw [parentKey_root] at HM
    omega
  refine ⟨⟨HV,?_⟩,?_⟩
  · change 2≤get P .slot15 (parent mean z) ∧ get P .slot15 (parent mean z)≤4
    rw [parent_context]
    exact ⟨by omega,by omega⟩
  · rw [HD,HA]
    exact (Nat.sub_le _ _).trans (Nat.le_of_lt hg.1.2.2.2.2)

theorem probe_metadata (mean : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hg : FormulaSignSlotRadialProviderProperRowWitness.RowGood z)
    (c s : ℕ) (hc : c<creating z) (hs : s<creating z) :
    IntegralFramedPhysicalNear.Metadata P D H (parent mean) (terminal mean)
      (fun z=>count mean z-1-c) (fun z=>count mean z-1-s) z :=by
  have HT:=probe_terminal_count mean z hv
  refine ⟨probe_core mean z hv hg,?_,?_,?_,?_⟩
  · change (G).birth (parentKey mean z)≤count mean z
    rw [parent_birth_actual mean z hv,HT]
    omega
  · have HE:=FormulaSignSlotRadialProviderFieldEquality.key_root (context mean z)
    have HP : pairFst (terminal mean z)=root mean z:=by
      unfold terminal
      simpa only [Function.comp_apply,context,pairFst_pair] using HE
    have HS : pairFst (IntegralMixedVirtualTaskBits.saved P (parent mean z))=root mean z:=by
      simpa only [parentKey] using parentKey_root mean z
    exact HP.trans HS.symm
  · change count mean z-1-c<count mean z
    omega
  · change count mean z-1-s<count mean z
    omega

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
