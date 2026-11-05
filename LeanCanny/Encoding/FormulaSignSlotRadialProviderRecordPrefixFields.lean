/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixWord
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicPoint
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixPoint
public import LeanCanny.Encoding.IntegralFramedPhysicalBankChronologicalPoint
/-! # Actual provider prefix quotients are its own chronological fields -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedHistoryFamilyBits
open IntegralMixedFramedRunObservation (ofCommands)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem padded_nested {n B : ℕ} (f : Instruction n B) (cs : List (Instruction n B))
    (M m : ℕ) (hm : m≤M) : paddedPast f (paddedPast f cs M) m=paddedPast f cs m := by
  rw [paddedPast_valid _ _ _ (by rw [paddedPast_length];exact hm)]
  simp only [past,List.reverse_take,List.length_reverse,List.reverse_reverse,paddedPast_length]
  exact paddedPast_drop f cs M m hm

private theorem observation_congr {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :
    ofCommands x cs hc=ofCommands x ds hd := by
  cases he
  rfl

private theorem prefix_field (E : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents E.parameters E.plan E.data T)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input E) c w)
    (m : ℕ) (hm : m≤prefixLength E.parameters (E.key c)) (i : ℕ) (hi : i<m) :
    (IntegralFramedPhysicalPrefixObservation.atRoot E.parameters E.plan (pairFst (E.key c)) m
      (hm.trans (min_le_right _ _))).point (bankNatural E c w hw) i=
      IntegralFramedPhysicalBankTerm.env E T hr c w hw (m-1-i) := by
  let cs := commands E.parameters E.plan (E.key c)
  have HCs : cs.length=prefixLength E.parameters (E.key c) := paddedPast_length _ _ _
  have HC : cs.length≤E.parameters.cap (pairFst (E.key c))+1+1 := by
    rw [HCs]
    exact (min_le_right _ _).trans (Nat.le_succ _)
  have H0 := IntegralMixedMarkedPrefixPoint.point_paddedPast
    (initial E.parameters E.plan (pairFst (E.key c))) cs
    (defaultInstruction E.parameters E.plan (pairFst (E.key c))) HC m (hm.trans_eq HCs.symm)
    (bankNatural E c w hw) ⟨i,hi⟩
  have H1 := IntegralFramedPhysicalPrefixPoint.full_point E.parameters E.plan E.data
    E.nodes E.factor E.seed E.bounds E.key E.positive c w hw
    ⟨cs.length-m+i,by change cs.length-m+i<cs.length;omega⟩
  have HN : bankNatural E c w hw=IntegralFramedPhysicalSquare.naturalPoint E.parameters E.plan E.data
      E.nodes E.factor E.seed E.bounds E.key E.positive c w hw := rfl
  rw [HN] at H0
  have HP := padded_nested (defaultInstruction E.parameters E.plan (pairFst (E.key c)))
    (E.plan.rules (pairFst (E.key c))) (prefixLength E.parameters (E.key c)) m hm
  change paddedPast _ cs m=_ at HP
  have HD := observation_congr (initial E.parameters E.plan (pairFst (E.key c)))
    (paddedPast (defaultInstruction E.parameters E.plan (pairFst (E.key c))) cs m)
    (paddedPast (defaultInstruction E.parameters E.plan (pairFst (E.key c)))
      (E.plan.rules (pairFst (E.key c))) m)
    (by rw [paddedPast_length];exact (hm.trans (min_le_right _ _)).trans (Nat.le_succ _))
    (by rw [paddedPast_length];exact (hm.trans (min_le_right _ _)).trans (Nat.le_succ _)) HP
  have H0' := (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.point
    (IntegralFramedPhysicalSquare.naturalPoint E.parameters E.plan E.data E.nodes E.factor E.seed
      E.bounds E.key E.positive c w hw) i) HD).symm.trans H0
  have HE := IntegralFramedPhysicalBankTerm.env_chronological E T hr c w hw (m-1-i) (by
    change m-1-i<(family E.parameters E.plan E.data).birth (E.key c)
    rw [family_birth]
    omega)
  change (ofCommands _ _ _).point _ i=_
  rw [HN]
  refine H0'.trans (H1.trans ?_)
  rw [HE]
  apply congrArg (IntegralFramedPhysicalSquare.point E.parameters E.plan E.data
    E.nodes E.factor E.seed E.bounds E.key E.positive c w hw)
  apply Fin.ext
  change cs.length-m+i=(family E.parameters E.plan E.data).birth (E.key c)-1-(m-1-i)
  rw [family_birth,←HCs]
  omega

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPlan.bank observation

theorem word_value (root w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context root) w)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) (i : ℕ) (hi : i<N root+j) :
    (observation root j hj).point (natural root w hw) i=
      FormulaSignSlotRadialProviderAtomic.bankField (context root) w hw (N root+j-1-i) := by
  have HM : N root+j≤prefixLength (B).parameters ((B).key (context root)) := by
    rw [full_prefix]
    change _≤N root+IntegralMixedCausalRecordPlanBits.count root
    omega
  have H := prefix_field B FormulaSignSlotRadialProviderRecordPlan.tables
    FormulaSignSlotRadialProviderAtomic.bank_represents (context root) w hw (N root+j) HM i hi
  have HE := IntegralFramedPhysicalPrefixObservation.at_congr (B).parameters (B).plan
    (pairFst ((B).key (context root))) root (N root+j) (N root+j)
    (HM.trans (min_le_right _ _)) (bank_bound root j hj) (key_root root) rfl
  have HO := HE.trans (bank_observation root j hj)
  have HV := congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.point (natural root w hw) i) HO
  exact HV.symm.trans H

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
