/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPastValues
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixMetadata
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordCriticalNatural
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedMetadata
/-! # Historical provider critical correlations survive independent resampling -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => IntegralFramedBankQuery.Bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "O" => FormulaSignSlotRadialProviderRecordPrefix.observation
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "Active" => FormulaSignSlotRadialProviderAtomic.Active
local notation "selected" => FormulaSignSlotRadialProviderAtomic.selected
local notation "natural" => FormulaSignSlotRadialProviderRecordPrefix.natural
local notation "header" => FormulaSignSlotRadialProviderRecordPrefix.header
local notation "stage" => IntegralFramedPhysicalCriticalGuardScan.stage
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPrefix.observation
  FormulaSignSlotRadialProviderAtomic.root FormulaSignSlotRadialProviderAtomic.dimension
  preparedRoot start parentCommands IntegralMixedFramedPhysicalIndex.prefixArity

private theorem active_iff_header (r : List Bool) (b : ℕ)
    (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r) :
    Active (C r) b ↔ (header r b).context=1 := by
  simp only [FormulaSignSlotRadialProviderAtomic.Active,IntegralFramedPhysicalCompanionPoint.Active,
    IntegralMixedFramedCriticalGuardBits.Active,IntegralFramedPhysicalCriticalGuardTest.keyDatum,
    IntegralFramedPhysicalCriticalGuardScan.stage,pairFst_pair,pairSnd_pair,List.length_replicate]
  rw [FormulaSignSlotRadialProviderRecordPrefix.full_prefix]
  simp only [hb,true_and]
  rfl

private theorem critical_column_bound (r : List Bool) (b bound : ℕ) (hbound : b<bound)
    (hb : Active (C r) b) :
    IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (C r)) (List.replicate b true))+
      selected (C r) b<
    IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (C r)) (List.replicate bound true)) := by
  have HS := FormulaSignSlotRadialProviderAtomic.selected_lt (C r) b hb
  have HA := (IntegralFramedPhysicalCompanionPoint.active_direct B T (C r) b hb).2
  have HSpan : IntegralMixedFramedPhysicalIndex.span P T
      (pair ((B).key (C r)) (List.replicate b true))=
      IntegralMixedFramedPhysicalIndex.block ((P).ambient (pairFst ((B).key (C r))))+1 := by
    unfold IntegralMixedFramedPhysicalIndex.span
    unfold IntegralMixedFramedCriticalGuardBits.header at HA
    simp only [pairFst_pair,pairSnd_pair,List.length_replicate] at HA ⊢
    rw [ite_eq_left HA]
  have H1 : IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (C r)) (List.replicate b true))+
      selected (C r) b<
      IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (C r)) (List.replicate (b+1) true)) := by
    rw [IntegralMixedFramedPhysicalRowSelector.prefix_succ,HSpan]
    unfold IntegralMixedFramedPhysicalIndex.block
    omega
  exact H1.trans_le ((IntegralMixedFramedPhysicalRowSelector.prefix_strictMono P T ((B).key (C r))).monotone (by omega))

theorem past_critical_raw_stage (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (leftCode rightCode : List Bool) (side : Bool) (hE : EndpointsGood old leftCode rightCode)
    (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (C (preparedRoot old leftCode rightCode side)) w)
    (hr : ∀r<IntegralMixedFramedPhysicalIndex.arity (parentCommands old hv hd leftCode rightCode side hE),
      natural (preparedRoot old leftCode rightCode side) w hw r=FormulaSignSlotRadialProviderRetainedAppend.oldNatural old hv r)
    (j : ℕ) (hj : j<start old)
    (hb : Active (C (preparedRoot old leftCode rightCode side)) (FormulaSignSlotRadialProviderAtomic.initial old+j)) :
    IntegralFramedPhysicalCompanionPoint.scalarValue B T FormulaSignSlotRadialProviderAtomic.bank_represents
      (C (preparedRoot old leftCode rightCode side)) w (FormulaSignSlotRadialProviderAtomic.initial old+j)=InfinitesimalSign.encode 0 := by
  let r := preparedRoot old leftCode rightCode side
  let l := FormulaSignSlotRadialProviderAtomic.root old
  let b := N l+j
  have HN : N r=N l := FormulaSignSlotRadialProviderRecordPrefix.count_eq _ _ (prepared_provider old leftCode rightCode side)
  have HF := start_fit old hv
  have HJL : j<IntegralMixedCausalRecordPlanBits.count l := hj.trans_le HF
  have HJR : j<IntegralMixedCausalRecordPlanBits.count r := HJL.trans_eq (prepared_count old hv hd leftCode rightCode side hE).symm
  have HH := FormulaSignSlotRadialProviderRecordPrefix.header_eq r l (prepared_provider old leftCode rightCode side)
    (prepared_count old hv hd leftCode rightCode side hE) j (Nat.succ_le_of_lt HJR)
    (fun i hi=>prepared_record old hv leftCode rightCode side i (hi.trans_le (Nat.succ_le_of_lt hj)))
  rw [HN] at HH
  have HBLeft : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r := by
    unfold FormulaSignSlotRadialProviderRecordPlan.fullCount
    rw [HN]
    dsimp only [b]
    omega
  have HBRight : b<FormulaSignSlotRadialProviderRecordPlan.fullCount l := by
    unfold FormulaSignSlotRadialProviderRecordPlan.fullCount
    dsimp only [b]
    omega
  have HAnew := (active_iff_header r b HBLeft).mp hb
  have HAold : (header l b).context=1 :=
    (congrArg IntegralMixedCommandHeaderBits.Header.context HH).symm.trans HAnew
  have hbo := (active_iff_header l b HBRight).mpr HAold
  have HS : selected (C r) b=selected (C l) b := by
    exact congrArg (fun h : IntegralMixedCommandHeaderBits.Header=>h.offset+h.coordinate) HH
  have HAr := (FormulaSignSlotRadialProviderRecordPrefix.prefix_arity_observation r j HJR.le).trans
    ((congrArg IntegralMixedFramedRunObservation.Data.arity (prefix_observation old hv hd leftCode rightCode side hE j hj.le)).trans
      (FormulaSignSlotRadialProviderRecordPrefix.prefix_arity_observation l j HJL.le).symm)
  rw [HN] at HAr
  let col := IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (C l)) (List.replicate b true))+selected (C l) b
  have HCol : IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (C r)) (List.replicate b true))+
      selected (C r) b=col := congrArg₂ (·+·) HAr HS
  have HColBound : col<(O l (start old) HF).arity :=
    (critical_column_bound l b (N l+start old) (by dsimp only [b];omega) hbo).trans_eq
      (FormulaSignSlotRadialProviderRecordPrefix.prefix_arity_observation l (start old) HF)
  have HRaw := past_raw_native old hv hd leftCode rightCode side hE _ hr col HColBound
  have HPow : UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) b=
      UniformIntegralPowerSchedule.physical ((P).cap l+1) (2^(P).width l) b := by
    have HC : (P).cap r=(P).cap l := prepared_cap old hv hd leftCode rightCode side hE
    have HW : (P).width r=(P).width l := FormulaSignSlotRadialProviderRecordPrefix.width r l (prepared_provider old leftCode rightCode side)
    rw [HC,HW]
  have HOld := FormulaSignSlotRadialProviderRecordPrefix.scalarValue_of_valid old hv b (by
    change b<IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key (C l))
    rw [FormulaSignSlotRadialProviderRecordPrefix.full_prefix]
    exact HBRight)
  have HOldEq := (FormulaSignSlotRadialProviderRecordPrefix.scalarValue_zero_iff_natural l
    (FormulaSignSlotRadialProviderAtomic.word old) (FormulaSignSlotRadialProviderAtomic.full_valid old hv) b hbo).mp HOld
  apply (FormulaSignSlotRadialProviderRecordPrefix.scalarValue_zero_iff_natural r w hw b hb).mpr
  rw [HCol,HPow]
  exact (past_fields old hv hd leftCode rightCode side hE w hw hr b (by change N l+j<N l+start old;omega)).trans
    (HOldEq.trans (congrArg (fun x : ℝ=>x^UniformIntegralPowerSchedule.physical ((P).cap l+1) (2^(P).width l) b) HRaw).symm)

theorem integer_inactive (r : List Bool) (b : ℕ) (hb : b<N r) : ¬Active (C r) b := by
  intro H
  have HH : (header r b).context=1 := H.2
  rw [FormulaSignSlotRadialProviderRecordPrefix.header_actual] at HH
  have HE := FormulaSignSlotRadialProviderFirstSeed.integer_header r b hb
  change IntegralMixedCommandHeaderBits.command
    (IntegralMixedFramedRootPullback.instructionAt FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
      FormulaSignSlotRadialProviderRecordPlan.certifiedPlan r b).command=IntegralMixedCommandHeaderBits.zero at HE
  rw [HE] at HH
  cases HH

theorem past_critical (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (leftCode rightCode : List Bool) (side : Bool) (hE : EndpointsGood old leftCode rightCode)
    (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (C (preparedRoot old leftCode rightCode side)) w)
    (hr : ∀r<IntegralMixedFramedPhysicalIndex.arity (parentCommands old hv hd leftCode rightCode side hE),
      natural (preparedRoot old leftCode rightCode side) w hw r=FormulaSignSlotRadialProviderRetainedAppend.oldNatural old hv r)
    (b : ℕ) (hb : b<FormulaSignSlotRadialProviderAtomic.initial old+start old)
    (ha : Active (C (preparedRoot old leftCode rightCode side)) b) :
    IntegralFramedPhysicalCompanionPoint.scalarValue B T FormulaSignSlotRadialProviderAtomic.bank_represents
      (C (preparedRoot old leftCode rightCode side)) w b=InfinitesimalSign.encode 0 := by
  have HN : N (preparedRoot old leftCode rightCode side)=FormulaSignSlotRadialProviderAtomic.initial old := prepared_initial old leftCode rightCode side
  by_cases hi : b<FormulaSignSlotRadialProviderAtomic.initial old
  · exact False.elim (integer_inactive (preparedRoot old leftCode rightCode side) b (hi.trans_eq HN.symm) ha)
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
    exact past_critical_raw_stage old hv hd leftCode rightCode side hE w hw hr j (by omega) ha

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
