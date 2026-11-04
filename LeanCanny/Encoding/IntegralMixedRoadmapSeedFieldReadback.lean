/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedWord
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedPreludeReadback
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedScan
/-! # The same sampled seed word reads its prescribed chronological fields -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial commands)
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem command_room (A :Parameters) (D :IntegralMixedFramedHistoryFamilyBits.Plan A) (key :List Bool) :
    (commands A D key).length≤A.cap (pairFst key)+1+1:=by
  rw [commands,paddedPast_length]
  exact (min_le_right _ _).trans (Nat.le_succ _)

private def BankJoint (K :IntegralFramedBankQuery.Bank) (c w :List Bool) (u :ℕ→ℝ) :Prop:=
  ∀hv :SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input K) c w,
  ∀i :Fin (IntegralFramedPhysicalSquare.count K.parameters K.plan (K.key c)),
    IntegralFramedPhysicalSquare.joint K.parameters K.plan K.data K.nodes K.factor K.seed K.bounds
      K.key K.positive c w hv i=u i.val

private theorem bank_observation (K :IntegralFramedBankQuery.Bank) (c w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input K) c w)
    (u :ℕ→ℝ) (HJ :BankJoint K c w u)
    (i :Fin ((IntegralMixedFramedHistoryFamilyBits.family K.parameters K.plan K.data).birth (K.key c))) :
    IntegralFramedPhysicalSquare.point K.parameters K.plan K.data K.nodes K.factor K.seed K.bounds
      K.key K.positive c w hw i=
    (IntegralMixedFramedRunObservation.ofCommands (initial K.parameters K.plan (pairFst (K.key c)))
      (commands K.parameters K.plan (K.key c)) (command_room K.parameters K.plan (K.key c))).point u i.val:=
  IntegralFramedPhysicalSquare.point_of_joint_natural K.parameters K.plan K.data K.nodes K.factor K.seed
    K.bounds K.key K.positive c w hw u (HJ hw) i

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "BP"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX" old=>pair (preparedRoot hn ht ha hR0 old) []
local notation "OLD" old=>seedOlder hn ht ha hR0 old
local notation "JS" old=>seedSelections hn ht ha hR0 old
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedFramedHistoryFamilyBits.family preparedRoot seedOlder seedSelections seedTail seedPoint seedObservation
  IntegralFramedPhysicalSquare.point IntegralMixedPhysicalFieldEquality.point

noncomputable def FieldJoint (old w :List Bool) (hw :SquareSampleCompleteVertices.Valid S (CTX old) w)
    (u :ℕ→ℝ) :Prop:=∀i :Fin (IntegralFramedPhysicalSquare.count (BP).parameters (BP).plan ((BP).key (CTX old))),
  IntegralFramedPhysicalSquare.joint (BP).parameters (BP).plan (BP).data (BP).nodes (BP).factor (BP).seed
    (BP).bounds (BP).key (BP).positive (CTX old) w (seed_valid_to_parent hn ht ha hR0 _ _ hw) i=u i.val

private theorem field_joint_native (old w :List Bool) (hw :SquareSampleCompleteVertices.Valid S (CTX old) w)
    (u :ℕ→ℝ) (HJ :FieldJoint hn ht ha hR0 old w hw u) :BankJoint B (CTX old) w u:=by
  have HE :B=BP:=by
    unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
    rfl
  have HP :BankJoint BP (CTX old) w u:=by
    intro hvalid
    exact HJ
  exact (congrArg (fun K=>BankJoint K (CTX old) w u) HE).mpr HP

theorem seed_field_count (old :List Bool) :
    IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (CTX old)=
      (OLD old).length+(JS old).length:=by
  rw [IntegralMixedPhysicalFieldEquality.count_eq]
  simp only [pairFst_pair,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount,
    seed_older_length,seed_length]

private theorem field_seed_observation (old :List Bool) :
    IntegralMixedFramedRunObservation.ofCommands (initial (B).parameters (B).plan (pairFst ((B).key (CTX old))))
      (commands (B).parameters (B).plan ((B).key (CTX old)))
      (command_room (B).parameters (B).plan ((B).key (CTX old)))=
        seedObservation hn ht ha hR0 old:=by
  have HT:=IntegralMixedMarkedPrefixFieldReadback.terminal_bank_data hn ht ha hR0
    (preparedRoot hn ht ha hR0 old)
  have HR :IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0
      (preparedRoot hn ht ha hR0 old)=seedObservation hn ht ha hR0 old:=by
    unfold seedObservation IntegralMixedMarkedPrefixFieldReadback.fullObservation
    rfl
  exact HT.trans HR

theorem seed_field_observation (old w :List Bool) (hw :SquareSampleCompleteVertices.Valid S (CTX old) w)
    (u :ℕ→ℝ) (HJ :FieldJoint hn ht ha hR0 old w hw u) (label :ℕ)
    (hl :label<(OLD old).length+(JS old).length) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX old) w hw label=
      (seedObservation hn ht ha hR0 old).point u ((OLD old).length+(JS old).length-1-label):=by
  have HC:=seed_field_count hn ht ha hR0 old
  have HP :IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters ((B).key (CTX old))=
      (OLD old).length+(JS old).length:=by
    rw [←IntegralMixedFramedHistoryFamilyBits.family_birth (B).parameters (B).plan (B).data]
    exact HC
  have HI : (OLD old).length+(JS old).length-1-label<
      (IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data).birth ((B).key (CTX old)):=by
    change _<IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (CTX old)
    rw [HC]
    omega
  have HX:=bank_observation B (CTX old) w hw u
    (field_joint_native hn ht ha hR0 old w hw u HJ) ⟨_,HI⟩
  have HY:=HX.trans (congrArg (fun O:IntegralMixedFramedRunObservation.Data=>
    O.point u ((OLD old).length+(JS old).length-1-label)) (field_seed_observation hn ht ha hR0 old))
  have HF:=IntegralMixedPhysicalFieldEquality.point_full hn ht ha (radius_binary hR0) (CTX old) w hw label
    (by rw [HP];exact hl)
  simp only [HP] at HF
  exact HF.trans HY


noncomputable def FieldValues (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (p :Fin ((P).ambient (preparedRoot hn ht ha hR0 old)+1)→ℝ) (u :ℕ→ℝ) :Prop:=
  ∀i :Fin ((OLD old).length+(JS old).length),
    (seedObservation hn ht ha hR0 old).point u i.val=
      IntegralMixedPointCompanion.values p (seedPoint hn ht ha hR0 old hv) (JS old) i

theorem seed_field_values (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (p :Fin ((P).ambient (preparedRoot hn ht ha hR0 old)+1)→ℝ) (u :ℕ→ℝ) (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX old) w)
    (HJ :FieldJoint hn ht ha hR0 old w hw u) (HV :FieldValues hn ht ha hR0 old hv p u)
    (label :ℕ) (hl :label<(OLD old).length+(JS old).length) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX old) w hw label=
      IntegralMixedPointCompanion.values p (seedPoint hn ht ha hR0 old hv) (JS old)
        ⟨(OLD old).length+(JS old).length-1-label,by omega⟩:=
  (seed_field_observation hn ht ha hR0 old w hw u HJ label hl).trans (HV ⟨(OLD old).length+(JS old).length-1-label,by omega⟩)

private theorem reverse_selection (d m tail a :ℕ)
    (ha0 :a<(IntegralMixedChronologicalSeedProgram.selections d m tail).length) :
    ((IntegralMixedChronologicalSeedProgram.selections d m tail).get
      ⟨(IntegralMixedChronologicalSeedProgram.selections d m tail).length-1-a,by omega⟩).val.val=
      IntegralMixedRoadmapSeedMetadata.selected d a:=by
  have H:=IntegralMixedChronologicalSeedProgram.selection_coordinate d m tail
    ⟨(IntegralMixedChronologicalSeedProgram.selections d m tail).length-1-a,by omega⟩
  have HL:=IntegralMixedChronologicalSeedProgram.selections_length d m tail
  simp only [List.get_eq_getElem]
  rw [H]
  simp only [HL]
  unfold IntegralMixedRoadmapSeedMetadata.selected
  split_ifs <;> omega

theorem seed_selected_field (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (p :Fin ((P).ambient (preparedRoot hn ht ha hR0 old)+1)→ℝ) (u :ℕ→ℝ) (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX old) w)
    (HJ :FieldJoint hn ht ha hR0 old w hw u) (HV :FieldValues hn ht ha hR0 old hv p u)
    (a :ℕ) (ha0 :a<IntegralMixedCausalRecordPlanBits.count (preparedRoot hn ht ha hR0 old)) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX old) w hw
      (number n (preparedRoot hn ht ha hR0 old)+8+a)=
    p ⟨IntegralMixedRoadmapSeedMetadata.selected ((P).ambient (preparedRoot hn ht ha hR0 old)) a,
      IntegralMixedRoadmapSeedMetadata.selected_lt _ _⟩:=by
  have HA :a<(JS old).length:=by rw [seed_length];exact ha0
  have HH:=seed_field_values hn ht ha hR0 old hv p u w hw HJ HV ((OLD old).length+a) (by omega)
  have HE :(OLD old).length+(JS old).length-1-((OLD old).length+a)=(JS old).length-1-a:=by omega
  simp only [HE] at HH
  rw [←seed_older_length hn ht ha hR0 old]
  let k :Fin (JS old).length:=⟨(JS old).length-1-a,by omega⟩
  have HG:=IntegralMixedPointCompanion.values_get p (seedPoint hn ht ha hR0 old hv) (JS old) k
  refine HH.trans (HG.trans ?_)
  apply congrArg p
  apply Fin.ext
  dsimp only [k]
  unfold seedSelections at HA ⊢
  exact reverse_selection _ _ _ a HA

theorem seed_prelude_field (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (p :Fin ((P).ambient (preparedRoot hn ht ha hR0 old)+1)→ℝ) (u :ℕ→ℝ) (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX old) w)
    (HJ :FieldJoint hn ht ha hR0 old w hw u) (HV :FieldValues hn ht ha hR0 old hv p u)
    (label :ℕ) (hl :label<number n (preparedRoot hn ht ha hR0 old)+8) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX old) w hw label=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapAtomic.context old) (IntegralMixedRoadmapAtomic.word old)
        (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv) label:=by
  have HL :label<(OLD old).length:=by rw [seed_older_length];exact hl
  have HH:=seed_field_values hn ht ha hR0 old hv p u w hw HJ HV label (by omega)
  let i :Fin (OLD old).length:=⟨(OLD old).length-1-label,by omega⟩
  have HE :(OLD old).length+(JS old).length-1-label=(JS old).length+i.val:=by dsimp only [i];omega
  simp only [HE] at HH
  have HG:=IntegralMixedPointCompanion.values_old p (seedPoint hn ht ha hR0 old hv) (JS old) i
  exact HH.trans (HG.trans (seedPoint_old_field hn ht ha hR0 old hv label HL))

end LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
