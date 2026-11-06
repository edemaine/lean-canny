/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendMidpointFields
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendSignatureSyntax
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignatureReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCriticalMetadata
/-! # Independent accepted words satisfy the actual paired midpoint signature -/
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
private theorem point_bankField (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input c w)
    (i : ℕ) (hi : i<FormulaSignSlotRadialProviderFieldEquality.count c) :
    FormulaSignSlotRadialProviderFieldEquality.point c w hw i=
      FormulaSignSlotRadialProviderAtomic.bankField c w hw i :=
  FormulaSignSlotRadialProviderFieldEquality.point_env c w hw i hi

private theorem full_field_count (root : List Bool) :
    FormulaSignSlotRadialProviderFieldEquality.count (C root)=FormulaSignSlotRadialProviderRecordPlan.fullCount root := by
  change (IntegralMixedFramedHistoryFamilyBits.family (FormulaSignSlotRadialProviderRecordPlan.bank).parameters
    (FormulaSignSlotRadialProviderRecordPlan.bank).plan (FormulaSignSlotRadialProviderRecordPlan.bank).data).birth
    ((FormulaSignSlotRadialProviderRecordPlan.bank).key (C root))=_
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth,FormulaSignSlotRadialProviderRecordPrefix.full_prefix]

private theorem signature_depth_eq (q : List Bool) : IntegralMixedRoadmapAtomic.depth q=
    FormulaSignSlotRadialProviderAtomic.depth q := rfl
private theorem signature_payload_eq (q : List Bool) : IntegralMixedRoadmapAtomic.payload q=
    FormulaSignSlotRadialProviderAtomic.payload q := rfl

variable {old : List Bool} {hv : FormulaSignSlotRadialProviderAtomic.Valid old}
  {hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old}
  {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right}
  {pMID pChildL pChildR : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
    (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}
local notation "D" => FormulaSignSlotRadialProviderAtomic.dimension old
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial old
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he
local notation "K" => List.length (R.orderedFree hk)
local notation "m" => List.length cs+List.length R.result.commands
local notation "q" => packet D old R.leftSpec R.rightSpec
attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension
  FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderAtomic.depth

private theorem signature_clock (side : Bool) (w : List Bool) :
    IntegralMixedRoadmapProper.midBirth D N (q side w)=midpointBirth old hv hd left right R := by
  have HC : IntegralMixedRoadmapProper.midBirth D N (q side w)=
      IntegralMixedRoadmapProper.midBirth D N (q side []) := by
    simp only [IntegralMixedRoadmapProper.midBirth,IntegralMixedRoadmapProper.baseBirth,
      IntegralMixedRoadmapProper.levelIndex,signature_depth_eq,signature_payload_eq,depth_packet,payload_packet]
  exact HC.trans (midpoint_birth old hv hd left right R side)

private theorem signature_before_child (side : Bool)
    {pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e)+1)→ℝ}
    (S : SampledLevel old hv hd left right R side pMID pChild) (i : ℕ) (hi : i<D+2) :
    Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderProperMidSignature.ownSignature
      (q side S.receipt.word)) i)<m+1+K := by
  have HDepth : 0<FormulaSignSlotRadialProviderAtomic.depth (q side S.receipt.word) := by rw [depth_packet];omega
  have HG := FormulaSignSlotRadialProviderProperCritical.midpoint_good _ S.atomic_valid HDepth
  have HK : IntegralMixedRoadmapProper.levelIndex (q side S.receipt.word)=FormulaSignSlotRadialProviderAtomic.depth old := by
    simp only [IntegralMixedRoadmapProper.levelIndex,signature_depth_eq,depth_packet,Nat.add_sub_cancel]
  have H := FormulaSignSlotRadialProviderProperMidSignature.signature_bounded_before_clock
    D N (q side S.receipt.word) (by rw [HK];omega)
    (by simpa only [dimension_packet,initial_packet] using HG) i hi
  rw [signature_clock,HK] at H
  have HC := S.free_count
  have HL : List.length cs=beginBirth old := FormulaSignSlotRadialProviderRetainedAppend.parent_length old hv hd e he
  change Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderProperMidSignature.signature
    (FormulaSignSlotRadialProviderAtomic.dimension (q side S.receipt.word))
    (FormulaSignSlotRadialProviderAtomic.initial (q side S.receipt.word)) (q side S.receipt.word)) i)<_
  rw [dimension_packet,initial_packet]
  unfold midpointBirth at H
  omega

private theorem child_lt_full (side : Bool)
    {pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e)+1)→ℝ}
    (S : SampledLevel old hv hd left right R side pMID pChild) :
    m+1+K<FormulaSignSlotRadialProviderFieldEquality.count (C (preparedRoot old R.leftSpec R.rightSpec side)) := by
  rw [full_field_count]
  have H := finish_le_full old hv hd left right R side
  change finishBirth old hv hd left right R side≤FormulaSignSlotRadialProviderRecordPlan.fullCount
    (preparedRoot old R.leftSpec R.rightSpec side) at H
  have HL := S.local_values_count
  omega

theorem SampledLevel.midpoint_signature
    (SL : SampledLevel old hv hd left right R false pMID pChildL)
    (SR : SampledLevel old hv hd left right R true pMID pChildR) :
    pair (q false SL.receipt.word) (q true SR.receipt.word)∈
      FormulaSignSlotRadialProviderProperMidSignature.language := by
  let qL := q false SL.receipt.word
  let qR := q true SR.receipt.word
  have HD : FormulaSignSlotRadialProviderAtomic.dimension qL=FormulaSignSlotRadialProviderAtomic.dimension qR := by
    rw [dimension_packet,dimension_packet]
  have HC : FormulaSignSlotRadialProviderProperMidSignature.Compatible (pair qL qR) := by
    simp only [FormulaSignSlotRadialProviderProperMidSignature.Compatible,
      FormulaSignSlotRadialProviderProperMidSignature.left,FormulaSignSlotRadialProviderProperMidSignature.right,
      pairFst_pair,pairSnd_pair]
    exact ⟨HD,by rw [depth_packet,depth_packet],by rw [depth_packet];omega⟩
  have HB : ∀i<WordListRecords.count (FormulaSignSlotRadialProviderProperMidSignature.table (pair qL qR)),
      FormulaSignSlotRadialProviderFieldEqualityList.label false
        (WordList.get (FormulaSignSlotRadialProviderProperMidSignature.table (pair qL qR)) i)<
          FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context qL) ∧
      FormulaSignSlotRadialProviderFieldEqualityList.label true
        (WordList.get (FormulaSignSlotRadialProviderProperMidSignature.table (pair qL qR)) i)<
          FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context qR) := by
    intro i hi
    have HI : i<FormulaSignSlotRadialProviderAtomic.dimension qL+2 := by
      rwa [FormulaSignSlotRadialProviderProperMidSignature.table_pair_count] at hi
    rw [FormulaSignSlotRadialProviderProperMidSignature.table_pair_lookup qL qR ⟨i,HI⟩]
    simp only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair]
    have HI' : i<D+2 := by simpa only [qL,dimension_packet] using HI
    have HL := (signature_before_child false SL i HI').trans (child_lt_full false SL)
    have HR := (signature_before_child true SR i HI').trans (child_lt_full true SR)
    simpa only [qL,qR,context_packet] using And.intro HL HR
  have HE : FormulaSignSlotRadialProviderProperMidSignature.query (pair qL qR)∈
      FormulaSignSlotRadialProviderFieldEqualityList.language := by
    unfold FormulaSignSlotRadialProviderProperMidSignature.query
    simp only [FormulaSignSlotRadialProviderProperMidSignature.left,FormulaSignSlotRadialProviderProperMidSignature.right,
      pairFst_pair,pairSnd_pair]
    apply (FormulaSignSlotRadialProviderFieldEqualityList.language_packet_iff _ _ _ _ _
      (FormulaSignSlotRadialProviderAtomic.full_valid qL SL.atomic_valid)
      (FormulaSignSlotRadialProviderAtomic.full_valid qR SR.atomic_valid) HB).mpr
    intro i hi
    have HI : i<FormulaSignSlotRadialProviderAtomic.dimension qL+2 := by
      rwa [FormulaSignSlotRadialProviderProperMidSignature.table_pair_count] at hi
    rw [FormulaSignSlotRadialProviderProperMidSignature.table_pair_lookup qL qR ⟨i,HI⟩]
    simp only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair]
    have HS : FormulaSignSlotRadialProviderProperMidSignature.ownSignature qL=
        FormulaSignSlotRadialProviderProperMidSignature.ownSignature qR :=
      midpoint_signature_eq old hv hd left right R SL.receipt.word SR.receipt.word
    rw [←HS]
    let b := Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderProperMidSignature.ownSignature qL) i)
    have HI' : i<D+2 := by simpa only [qL,dimension_packet] using HI
    have BB := signature_before_child false SL i HI'
    have HH := SL.before_child_fields SR b BB
    have HBL := BB.trans (child_lt_full false SL)
    have HBR := BB.trans (child_lt_full true SR)
    have HPL := point_bankField (C (preparedRoot old R.leftSpec R.rightSpec false)) SL.receipt.word SL.receipt.valid b HBL
    have HPR := point_bankField (C (preparedRoot old R.leftSpec R.rightSpec true)) SR.receipt.word SR.receipt.valid b HBR
    simpa only [qL,qR,b,context_packet,word_packet] using HPL.trans (HH.trans HPR.symm)
  exact ⟨HC,HE⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
