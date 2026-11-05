/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderReplay
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderReplayCoordinates
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixWord
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicPoint
/-! # Provider replay survives fresh own words with the same initial fields -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderReplay
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity
open IntegralFramedBankQuery (Bank)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "hn" => CanonicalAuxiliaryCandidateCover.dimension_unary
local notation "ht" => CanonicalAuxiliaryCandidateCover.equation_FP
local notation "ha" => CanonicalAuxiliaryCandidateCover.equation_scope
local notation "number" => FormulaSignSlotRadialExternalContext.number
attribute [local irreducible] CanonicalAuxiliaryCandidateCover.dimension
  IntegralFramedPhysicalCandidateReplay.point IntegralFramedPhysicalGridReplay.point

private theorem old_context_iff (B : Bank) (q ctx c w : List Bool)
    (hc : IntegralFramedPhysicalCandidateReplayThom.context q=ctx)
    (htarget : IntegralFramedPhysicalCandidateReplayThom.target q=c)
    (hword : IntegralFramedPhysicalCandidateReplayThom.word q=w) :
    q∈IntegralFramedPhysicalCandidateReplayThom.language hn ht ha B ↔
      ∃hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pairFst ctx),
        ∃hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B) c w,
          ∀i : Fin (number ctx),IntegralMixedAuxiliaryCandidate.point hn ht ha (pairFst ctx) hp i=
            IntegralFramedPhysicalCandidateReplay.point (n:=CanonicalAuxiliaryCandidateCover.dimension) B ctx c w hw i := by
  subst ctx
  subst c
  subst w
  exact IntegralFramedPhysicalCandidateReplayThom.language_iff hn ht ha B q

private theorem old_packet_iff (B : Bank) (ctx c w : List Bool) :
    packet ctx c w∈IntegralFramedPhysicalCandidateReplayThom.language hn ht ha B ↔
      ∃hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pairFst ctx),
        ∃hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B) c w,
          ∀i : Fin (number ctx),IntegralMixedAuxiliaryCandidate.point hn ht ha (pairFst ctx) hp i=
            IntegralFramedPhysicalCandidateReplay.point (n:=CanonicalAuxiliaryCandidateCover.dimension) B ctx c w hw i := by
  exact old_context_iff B (packet ctx c w) ctx c w
    (by simp only [IntegralFramedPhysicalCandidateReplayThom.context,packet,
      FormulaSignSlotRadialExternalReplay.packet,pairFst_pair])
    (by simp only [IntegralFramedPhysicalCandidateReplayThom.target,packet,
      FormulaSignSlotRadialExternalReplay.packet,pairFst_pair,pairSnd_pair])
    (by simp only [IntegralFramedPhysicalCandidateReplayThom.word,packet,
      FormulaSignSlotRadialExternalReplay.packet,pairSnd_pair])

theorem of_grid_points (B : Bank) (ctx cL wL cR wR : List Bool)
    (hL : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B) cL wL)
    (hR : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B) cR wR)
    (heq : ∀i<number ctx,IntegralFramedPhysicalGridReplay.point B cL wL hL (4*i)=
      IntegralFramedPhysicalGridReplay.point B cR wR hR (4*i))
    (H : packet ctx cL wL∈languageAt B) : packet ctx cR wR∈languageAt B := by
  by_cases he : FormulaSignSlotRadialExternalContext.external ctx
  · have HE : FormulaSignSlotRadialExternalContext.external (context (packet ctx cL wL)) := by
      simpa only [context,packet,FormulaSignSlotRadialExternalReplay.packet,
        FormulaSignSlotRadialExternalReplay.context,pairFst_pair] using he
    have HL := (external_iff B _ HE).mp H
    have HR := (FormulaSignSlotRadialExternalReplay.languageAt_iff B _).mp HL.2
    simp only [packet,FormulaSignSlotRadialExternalReplay.packet,FormulaSignSlotRadialExternalReplay.context,
      FormulaSignSlotRadialExternalReplay.target,FormulaSignSlotRadialExternalReplay.word,pairFst_pair,pairSnd_pair] at HR
    obtain ⟨_,hf,hA,hW,hpoints⟩ := HR
    apply (external_iff B _ (by simpa only [context,packet,FormulaSignSlotRadialExternalReplay.packet,
      FormulaSignSlotRadialExternalReplay.context,pairFst_pair] using he)).mpr
    refine ⟨?_,(FormulaSignSlotRadialExternalReplay.languageAt_iff B _).mpr ?_⟩
    · simpa only [context,packet,FormulaSignSlotRadialExternalReplay.packet,
        FormulaSignSlotRadialExternalReplay.context,pairFst_pair] using HL.1
    · simp only [packet,FormulaSignSlotRadialExternalReplay.packet,FormulaSignSlotRadialExternalReplay.context,
        FormulaSignSlotRadialExternalReplay.target,FormulaSignSlotRadialExternalReplay.word,pairFst_pair,pairSnd_pair]
      exact ⟨he,hf,hA,hR,fun i hi=>(hpoints i hi).trans (heq i hi)⟩
  · have HE : ¬FormulaSignSlotRadialExternalContext.external (context (packet ctx cL wL)) := by
      simpa only [context,packet,FormulaSignSlotRadialExternalReplay.packet,
        FormulaSignSlotRadialExternalReplay.context,pairFst_pair] using he
    have HL := (old_packet_iff B ctx cL wL).mp ((old_iff B _ HE).mp H)
    obtain ⟨hp,hW,hpoints⟩ := HL
    apply (old_iff B _ (by simpa only [context,packet,FormulaSignSlotRadialExternalReplay.packet,
      FormulaSignSlotRadialExternalReplay.context,pairFst_pair] using he)).mpr
    apply (old_packet_iff B ctx cR wR).mpr
    refine ⟨hp,hR,fun i=>?_⟩
    have H0 := old_point_eq B ctx cL wL hL i
    have H1 := old_point_eq B ctx cR wR hR i
    exact (hpoints i).trans (H0.trans ((heq i.val i.isLt).trans H1.symm))

end LeanCanny.Encoding.FormulaSignSlotRadialProviderReplay

namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "number" => FormulaSignSlotRadialExternalContext.number

theorem prelude_birth (q : List Bool) : number (provider q)+8≤
    (IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data).birth ((B).key (context q)) := by
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
  have HC := FormulaSignSlotRadialProviderRecordPrefix.full_prefix (root q)
  change IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters ((B).key (context q))=
    FormulaSignSlotRadialProviderRecordPlan.fullCount (root q) at HC
  rw [HC]
  unfold FormulaSignSlotRadialProviderRecordPlan.fullCount FormulaSignSlotRadialProviderRecordPlan.count
  rw [root_provider]
  change number (provider q)+8≤number (provider q)+8+_
  omega

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPlan.bank

theorem replay_of_initial_fields (old : List Bool) (hv : Valid old) (q : List Bool) (hw : FullValid q)
    (hp : provider q=provider old)
    (hfields : ∀i<number (provider old),field old hv i=bankField (context q) (word q) hw i) : Replay q := by
  have HO := valid_replay old hv
  change FormulaSignSlotRadialProviderReplay.packet (provider old) (context old) (word old)∈
    FormulaSignSlotRadialProviderReplay.languageAt B at HO
  have HOld := prelude_birth old
  have HNew : number (provider old)+8≤
      (IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data).birth ((B).key (context q)) := by
    simpa only [hp] using prelude_birth q
  have HG (i : ℕ) (hi : i<number (provider old)) :
      IntegralFramedPhysicalGridReplay.point B (context old) (word old) (full_valid old hv) (4*i)=
        IntegralFramedPhysicalGridReplay.point B (context q) (word q) hw (4*i) := by
    rw [ReplayFields.grid_point_env B T bank_represents _ _ (full_valid old hv) i (by omega),
      ReplayFields.grid_point_env B T bank_represents _ _ hw i (by omega)]
    exact hfields i hi
  have HR := FormulaSignSlotRadialProviderReplay.of_grid_points B (provider old)
    (context old) (word old) (context q) (word q) (full_valid old hv) hw HG HO
  simpa only [Replay,replayQuery,hp] using HR

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
