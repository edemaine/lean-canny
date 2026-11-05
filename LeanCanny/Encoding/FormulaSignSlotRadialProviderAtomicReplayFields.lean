/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderReplayCoordinates
/-! # Provider replay identifies the actual original prelude fields -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.ReplayFields
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open FormulaSignSlotRadialProviderAtomic
open FormulaSignSlotRadialExternalPrelude (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables

private theorem initial_count (q : List Bool) (hv : Valid q) :
    number (provider q)+8≤(IntegralMixedFramedHistoryFamilyBits.family
      (B).parameters (B).plan (B).data).birth ((B).key (context q)) := by
  have H := (valid_marked q hv).1.2.1
  simpa only [sampleQuery,pairFst_pair,Marked.leafCount,context,FormulaSignSlotRadialProviderRecordPlan.count,
    root_provider,FormulaSignSlotRadialProviderIntegerPlan.count] using H

theorem external_fields (q : List Bool) (hv : Valid q)
    (he : FormulaSignSlotRadialExternalContext.external (provider q)) :
    ∃ ha : FormulaSignSlotRadialExternalReplay.accepted (provider q),
      ∀ i<number (provider q),
        FormulaSignSlotRadialExternalCoordinates.point (provider q)
          (FormulaSignSlotRadialExternalReplay.accepted_valid _ ha) i=field q hv i := by
  have H := (FormulaSignSlotRadialProviderReplay.external_iff B (replayQuery q)
    (by simpa only [replay_provider] using he)).mp (valid_replay q hv)
  have HL := (FormulaSignSlotRadialExternalReplay.languageAt_iff B (replayQuery q)).mp H.2
  simp only [replayQuery,FormulaSignSlotRadialProviderReplay.packet,FormulaSignSlotRadialExternalReplay.packet,
    FormulaSignSlotRadialExternalReplay.context,FormulaSignSlotRadialExternalReplay.target,
    FormulaSignSlotRadialExternalReplay.word,pairFst_pair,pairSnd_pair] at HL
  obtain ⟨_,_,ha,hw,hg⟩ := HL
  refine ⟨ha,fun i hi=>?_⟩
  have HP := hg i hi
  rw [grid_point_env B T bank_represents _ _ hw i (hi.trans_le (by
    have HC := initial_count q hv
    omega))] at HP
  exact HP

theorem external_projection (q : List Bool) (hv : Valid q)
    (he : FormulaSignSlotRadialExternalContext.external (provider q)) :
    ∃ ha : FormulaSignSlotRadialExternalReplay.accepted (provider q),
      ∀ i : Fin (number (provider q)),
        (BoundedRegularSource.markedProjection _ _ _ _ (MarkedPrelude.markedPoint q hv)).val i=
          FormulaSignSlotRadialExternalCoordinates.point (provider q)
            (FormulaSignSlotRadialExternalReplay.accepted_valid _ ha) i.val := by
  obtain ⟨ha,hp⟩ := external_fields q hv he
  refine ⟨ha,fun i=>?_⟩
  rw [MarkedPrelude.projection_coordinate]
  exact (hp i.val i.isLt).symm

private theorem candidate_point_grid {n : List Bool→ℕ} (b : IntegralFramedBankQuery.Bank)
    (ctx c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input b) c w)
    (i : Fin (n (pairFst (pairFst ctx)))) :
    IntegralFramedPhysicalCandidateReplay.point (n:=n) b ctx c w hw i=
      IntegralFramedPhysicalGridReplay.point b c w hw (4*i.val) := by
  unfold IntegralFramedPhysicalCandidateReplay.point IntegralFramedPhysicalGridReplay.point
  congr 1
  apply Fin.ext
  rw [IntegralFramedPhysicalCandidateReplay.coordinate_packet,IntegralFramedPhysicalGridReplay.coordinate_packet]
  change IntegralFramedPhysicalGridReplay.count b c-1-i.val=
    IntegralFramedPhysicalGridReplay.count b c-1-(4*i.val)/4
  omega

theorem candidate_fields {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (b : IntegralFramedBankQuery.Bank) (tab : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents b.parameters b.plan b.data tab)
    (ctx c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input b) c w)
    (hc : n (pairFst (pairFst ctx))≤
      (IntegralMixedFramedHistoryFamilyBits.family b.parameters b.plan b.data).birth (b.key c))
    (h : pair ctx (pair c w)∈IntegralFramedPhysicalCandidateReplayThom.language hn ht ha b) :
    ∃ hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pairFst ctx),
      ∀ i : Fin (n (pairFst (pairFst ctx))),IntegralMixedAuxiliaryCandidate.point hn ht ha (pairFst ctx) hp i=
        IntegralFramedPhysicalBankTerm.env b tab hr c w hw i.val := by
  have HL := (IntegralFramedPhysicalCandidateReplayThom.language_iff hn ht ha b _).mp h
  unfold IntegralFramedPhysicalCandidateReplayThom.dimension
    IntegralFramedPhysicalCandidateReplayThom.oldCandidate at HL
  have HCtx : IntegralFramedPhysicalCandidateReplayThom.context (pair ctx (pair c w))=ctx := pairFst_pair _ _
  have HT : IntegralFramedPhysicalCandidateReplayThom.target (pair ctx (pair c w))=c := by
    simp only [IntegralFramedPhysicalCandidateReplayThom.target,pairSnd_pair,pairFst_pair]
  have HW : IntegralFramedPhysicalCandidateReplayThom.word (pair ctx (pair c w))=w := by
    simp only [IntegralFramedPhysicalCandidateReplayThom.word,pairSnd_pair]
  rw [HCtx,HT,HW] at HL
  obtain ⟨hp,hv,hg⟩ := HL
  refine ⟨hp,fun i=>?_⟩
  have H := hg i
  rw [candidate_point_grid,grid_point_env b tab hr c w hv i.val (i.isLt.trans_le hc)] at H
  exact H

attribute [local irreducible] IntegralMixedAuxiliaryCandidate.point IntegralMixedAuxiliaryCandidate.Valid

theorem old_fields (q : List Bool) (hv : Valid q)
    (he : ¬FormulaSignSlotRadialExternalContext.external (provider q)) :
    ∃ hp : IntegralMixedAuxiliaryCandidate.Valid
        CanonicalAuxiliaryCandidateCover.dimension_unary CanonicalAuxiliaryCandidateCover.equation_FP
        CanonicalAuxiliaryCandidateCover.equation_scope (pairFst (provider q)),
      ∀ i : Fin (number (provider q)),
        IntegralMixedAuxiliaryCandidate.point
          CanonicalAuxiliaryCandidateCover.dimension_unary CanonicalAuxiliaryCandidateCover.equation_FP
          CanonicalAuxiliaryCandidateCover.equation_scope (pairFst (provider q)) hp i=field q hv i.val := by
  have H := (FormulaSignSlotRadialProviderReplay.old_iff B (replayQuery q)
    (by simpa only [replay_provider] using he)).mp (valid_replay q hv)
  exact candidate_fields CanonicalAuxiliaryCandidateCover.dimension_unary
    CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope
    B T bank_represents (provider q) (context q) (word q) (full_valid q hv)
    (by have HC := initial_count q hv;exact (Nat.le_add_right _ 8).trans HC) H

theorem old_projection (q : List Bool) (hv : Valid q)
    (he : ¬FormulaSignSlotRadialExternalContext.external (provider q)) :
    ∃ hp : IntegralMixedAuxiliaryCandidate.Valid
        CanonicalAuxiliaryCandidateCover.dimension_unary CanonicalAuxiliaryCandidateCover.equation_FP
        CanonicalAuxiliaryCandidateCover.equation_scope (pairFst (provider q)),
      ∀ i : Fin (number (provider q)),
        (BoundedRegularSource.markedProjection _ _ _ _ (MarkedPrelude.markedPoint q hv)).val i=
          IntegralMixedAuxiliaryCandidate.point
            CanonicalAuxiliaryCandidateCover.dimension_unary CanonicalAuxiliaryCandidateCover.equation_FP
            CanonicalAuxiliaryCandidateCover.equation_scope (pairFst (provider q)) hp i := by
  obtain ⟨hp,hp_eq⟩ := old_fields q hv he
  refine ⟨hp,fun i=>?_⟩
  rw [MarkedPrelude.projection_coordinate]
  exact (hp_eq i).symm

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.ReplayFields
