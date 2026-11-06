/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendParent
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendParent
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixFields
/-! # Actual general-append natural columns preserve every historical provider field -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
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

private theorem observation_commands {n S B : ℕ} {V : SpatialSource n}
    (x : State V S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :
    IntegralMixedFramedRunObservation.ofCommands x cs hc=IntegralMixedFramedRunObservation.ofCommands x ds hd := by
  cases he
  rfl

theorem parent_observation (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (leftCode rightCode : List Bool) (side : Bool) (hE : EndpointsGood old leftCode rightCode) :
    O (preparedRoot old leftCode rightCode side) (start old) (prefix_fit old hv hd leftCode rightCode side hE)=
      IntegralMixedFramedRunObservation.ofCommands (initial P D (preparedRoot old leftCode rightCode side))
        (parentCommands old hv hd leftCode rightCode side hE) (parent_room old hv hd leftCode rightCode side hE) := by
  unfold FormulaSignSlotRadialProviderRecordPrefix.observation IntegralFramedPhysicalPrefixObservation.atRoot
  apply observation_commands
  unfold parentCommands
  exact FormulaSignSlotRadialProviderRecordContinuation.before_commands _ _ _

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPrefix.observation
  FormulaSignSlotRadialProviderAtomic.root
  FormulaSignSlotRadialProviderAtomic.dimension
  preparedRoot start parentCommands

theorem past_prefix_point (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (leftCode rightCode : List Bool) (side : Bool) (hE : EndpointsGood old leftCode rightCode)
    (z v : ℕ→ℝ)
    (hz : ∀r<(O (FormulaSignSlotRadialProviderAtomic.root old) (start old) (start_fit old hv)).arity,z r=v r)
    (j : ℕ) (hj : j≤start old) (i : ℕ)
    (hi : i<N (FormulaSignSlotRadialProviderAtomic.root old)+j) :
    (O (preparedRoot old leftCode rightCode side) j ((hj.trans (start_fit old hv)).trans_eq
      (prepared_count old hv hd leftCode rightCode side hE).symm)).point z i=
    (O (FormulaSignSlotRadialProviderAtomic.root old) j (hj.trans (start_fit old hv))).point v i := by
  have HE := prefix_observation old hv hd leftCode rightCode side hE j hj
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
    (leftCode rightCode : List Bool) (side : Bool) (hE : EndpointsGood old leftCode rightCode)
    (z : ℕ→ℝ)
    (hz : ∀r<arity (parentCommands old hv hd leftCode rightCode side hE),z r=FormulaSignSlotRadialProviderRetainedAppend.oldNatural old hv r) :
    ∀r<(O (FormulaSignSlotRadialProviderAtomic.root old) (start old) (start_fit old hv)).arity,
      z r=FormulaSignSlotRadialProviderRetainedAppend.oldNatural old hv r := by
  have H0 := prefix_observation old hv hd leftCode rightCode side hE (start old) (Nat.le_refl _)
  have H1 := parent_observation old hv hd leftCode rightCode side hE
  have HA := (congrArg IntegralMixedFramedRunObservation.Data.arity H0).symm.trans
    (congrArg IntegralMixedFramedRunObservation.Data.arity H1)
  intro r hr
  exact hz r (hr.trans_eq HA)

theorem past_fields (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (leftCode rightCode : List Bool) (side : Bool) (hE : EndpointsGood old leftCode rightCode)
    (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (C (preparedRoot old leftCode rightCode side)) w)
    (hr : ∀r<arity (parentCommands old hv hd leftCode rightCode side hE),
      FormulaSignSlotRadialProviderRecordPrefix.natural (preparedRoot old leftCode rightCode side) w hw r=FormulaSignSlotRadialProviderRetainedAppend.oldNatural old hv r)
    (b : ℕ) (hb : b<FormulaSignSlotRadialProviderAtomic.initial old+start old) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old leftCode rightCode side)) w hw b=
      FormulaSignSlotRadialProviderAtomic.field old hv b := by
  let l := FormulaSignSlotRadialProviderAtomic.root old
  let r := preparedRoot old leftCode rightCode side
  have HN : N l=FormulaSignSlotRadialProviderAtomic.initial old := by
    dsimp only [l,FormulaSignSlotRadialProviderAtomic.initial]
  have HNR : N r=N l := FormulaSignSlotRadialProviderRecordPrefix.count_eq _ _ (prepared_provider old leftCode rightCode side)
  let i := N l+start old-1-b
  have HI : i<N l+start old := by dsimp only [i];omega
  have HRI : i<N r+start old := by rw [HNR];exact HI
  have HP := past_prefix_point old hv hd leftCode rightCode side hE _ _ (past_raw_native old hv hd leftCode rightCode side hE _ hr)
    (start old) (Nat.le_refl _) i HI
  have HL := FormulaSignSlotRadialProviderRecordPrefix.word_value l (FormulaSignSlotRadialProviderAtomic.word old)
    (FormulaSignSlotRadialProviderAtomic.full_valid old hv) (start old) (start_fit old hv) i HI
  have HR := FormulaSignSlotRadialProviderRecordPrefix.word_value r w hw (start old)
    (prefix_fit old hv hd leftCode rightCode side hE) i HRI
  have HE : N l+start old-1-i=b := by dsimp only [i];omega
  have HER : N r+start old-1-i=b := by rw [HNR];exact HE
  rw [HE] at HL
  rw [HER] at HR
  exact HR.symm.trans (HP.trans HL)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
