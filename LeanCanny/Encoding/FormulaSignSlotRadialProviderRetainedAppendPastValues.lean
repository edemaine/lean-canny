/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendParent
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixFields
/-! # Retained natural columns preserve every historical provider field -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedHistoryFamilyBits
open IntegralMixedFramedPhysicalIndex (arity)
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "O" => FormulaSignSlotRadialProviderRecordPrefix.observation
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context

private theorem arity_append {n B : ℕ} (cs ds : List (Instruction n B)) :
    arity (cs++ds)=arity cs+arity ds := by
  induction cs with
  | nil => simp only [List.nil_append,arity,Nat.zero_add]
  | cons c cs ih => simp only [List.cons_append,arity,ih]; omega

private theorem arity_drop_le {n B : ℕ} (cs : List (Instruction n B)) (k : ℕ) :
    arity (cs.drop k)≤arity cs := by
  have H := arity_append (cs.take k) (cs.drop k)
  rw [List.take_append_drop] at H
  omega

private theorem arity_prefix_mono {n B : ℕ} (cs : List (Instruction n B))
    (fallback : Instruction n B) (a b : ℕ) (hab : a≤b) (hb : b≤cs.length) :
    arity (paddedPast fallback cs a)≤arity (paddedPast fallback cs b) := by
  rw [paddedPast_valid fallback cs a (hab.trans hb),paddedPast_valid fallback cs b hb]
  simp only [past,List.reverse_take,List.length_reverse,List.reverse_reverse]
  have HE : cs.drop (cs.length-a)=(cs.drop (cs.length-b)).drop (b-a) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [HE]
  exact arity_drop_le _ _

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPrefix.observation
  FormulaSignSlotRadialProviderAtomic.root
  FormulaSignSlotRadialProviderAtomic.dimension
  preparedRoot start parentCommands

theorem past_prefix_point (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (FormulaSignSlotRadialProviderAtomic.initial old) old)
    (z v : ℕ→ℝ)
    (hz : ∀r<(O (FormulaSignSlotRadialProviderAtomic.root old) (start old) (start_fit old hv)).arity,z r=v r)
    (j : ℕ) (hj : j≤start old) (i : ℕ)
    (hi : i<N (FormulaSignSlotRadialProviderAtomic.root old)+j) :
    (O (preparedRoot old e) j ((hj.trans (start_fit old hv)).trans_eq
      (prepared_count old hv hd e he).symm)).point z i=
    (O (FormulaSignSlotRadialProviderAtomic.root old) j (hj.trans (start_fit old hv))).point v i := by
  have HE := prefix_observation old hv hd e he j hj
  apply (congrArg (fun o : IntegralMixedFramedRunObservation.Data=>o.point z i) HE).trans
  unfold FormulaSignSlotRadialProviderRecordPrefix.observation
  let r := FormulaSignSlotRadialProviderAtomic.root old
  let cs := paddedPast (defaultInstruction P D r) ((D).rules r) (N r+j)
  have HI : i<cs.length := by dsimp only [cs];rw [paddedPast_length];exact hi
  apply IntegralMixedMarkedPrefixPoint.point_congr (initial P D r) cs
    (by dsimp only [cs];rw [paddedPast_length];exact
      (FormulaSignSlotRadialProviderRecordPrefix.bound r j (hj.trans (start_fit old hv))).trans (Nat.le_succ _))
    z v ?_ ⟨i,HI⟩
  intro k hk
  apply hz k
  unfold FormulaSignSlotRadialProviderRecordPrefix.observation
  change k<arity (paddedPast (defaultInstruction P D r) ((D).rules r) (N r+start old))
  apply hk.trans_le (arity_prefix_mono ((D).rules r) (defaultInstruction P D r)
    (N r+j) (N r+start old) (by omega) ?_)
  rw [FormulaSignSlotRadialProviderRecordReceipt.rules,IntegralMixedCausalPlanBits.commands_length,
    FormulaSignSlotRadialProviderRecordReceipt.records_length]
  have HF := start_fit old hv
  change start old≤IntegralMixedCausalRecordPlanBits.count r at HF
  omega

theorem past_raw_native (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (FormulaSignSlotRadialProviderAtomic.initial old) old)
    (z : ℕ→ℝ)
    (hz : ∀r<arity (parentCommands old hv hd e he),z r=oldNatural old hv r) :
    ∀r<(O (FormulaSignSlotRadialProviderAtomic.root old) (start old) (start_fit old hv)).arity,
      z r=oldNatural old hv r := by
  have H0 := prefix_observation old hv hd e he (start old) (Nat.le_refl _)
  have H1 := parent_observation old hv hd e he
  have HA := (congrArg IntegralMixedFramedRunObservation.Data.arity H0).symm.trans
    (congrArg IntegralMixedFramedRunObservation.Data.arity H1)
  intro r hr
  exact hz r (hr.trans_eq HA)

theorem past_fields (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (FormulaSignSlotRadialProviderAtomic.initial old) old)
    (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (C (preparedRoot old e)) w)
    (hr : ∀r<arity (parentCommands old hv hd e he),
      FormulaSignSlotRadialProviderRecordPrefix.natural (preparedRoot old e) w hw r=oldNatural old hv r)
    (b : ℕ) (hb : b<FormulaSignSlotRadialProviderAtomic.initial old+start old) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) w hw b=
      FormulaSignSlotRadialProviderAtomic.field old hv b := by
  let l := FormulaSignSlotRadialProviderAtomic.root old
  let r := preparedRoot old e
  have HN : N l=FormulaSignSlotRadialProviderAtomic.initial old := by
    dsimp only [l,FormulaSignSlotRadialProviderAtomic.initial]
  have HNR : N r=N l := FormulaSignSlotRadialProviderRecordPrefix.count_eq _ _ (prepared_provider old e)
  let i := N l+start old-1-b
  have HI : i<N l+start old := by dsimp only [i];omega
  have HRI : i<N r+start old := by rw [HNR];exact HI
  have HP := past_prefix_point old hv hd e he _ _ (past_raw_native old hv hd e he _ hr)
    (start old) (Nat.le_refl _) i HI
  have HL := FormulaSignSlotRadialProviderRecordPrefix.word_value l (FormulaSignSlotRadialProviderAtomic.word old)
    (FormulaSignSlotRadialProviderAtomic.full_valid old hv) (start old) (start_fit old hv) i HI
  have HR := FormulaSignSlotRadialProviderRecordPrefix.word_value r w hw (start old)
    (prefix_fit old hv hd e he) i HRI
  have HE : N l+start old-1-i=b := by dsimp only [i];omega
  have HER : N r+start old-1-i=b := by rw [HNR];exact HE
  rw [HE] at HL
  rw [HER] at HR
  exact HR.symm.trans (HP.trans HL)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
