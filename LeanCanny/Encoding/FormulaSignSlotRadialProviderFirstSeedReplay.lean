/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedFields
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderReplayCoordinates
public import LeanCanny.Encoding.FormulaSignSlotRadialOldProviderRealization
/-! # The fresh seed word replays its own source-associated endpoint -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.Connectivity IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem external_packet_iff (BB : IntegralFramedBankQuery.Bank) (ctx t w : List Bool) :
    FormulaSignSlotRadialExternalReplay.packet ctx t w∈FormulaSignSlotRadialExternalReplay.languageAt BB ↔
    FormulaSignSlotRadialExternalContext.external ctx ∧ FormulaSignSlotRadialExternalReplay.fits ctx ∧
      ∃ ha : FormulaSignSlotRadialExternalReplay.accepted ctx,
        ∃ hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input BB) t w,
          ∀i<FormulaSignSlotRadialExternalContext.number ctx,
            FormulaSignSlotRadialExternalCoordinates.point ctx (FormulaSignSlotRadialExternalReplay.accepted_valid ctx ha) i=
              IntegralFramedPhysicalGridReplay.point BB t w hw (4*i) := by
  simpa only [FormulaSignSlotRadialExternalReplay.packet,FormulaSignSlotRadialExternalReplay.context,
    FormulaSignSlotRadialExternalReplay.target,FormulaSignSlotRadialExternalReplay.word,pairFst_pair,pairSnd_pair] using
      FormulaSignSlotRadialExternalReplay.languageAt_iff BB (FormulaSignSlotRadialExternalReplay.packet ctx t w)

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderIntegerSource.source IntegralMixedFramedHistoryFamilyBits.family

private theorem replay_query_packet (c w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.replayQuery (packet c w)=
      FormulaSignSlotRadialProviderReplay.packet c (seedContext c) w := by
  rw [FormulaSignSlotRadialProviderAtomic.replayQuery,provider_packet,context_packet,word_packet]
  rfl

theorem WordReceipt.grid_field {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p) (i : ℕ) (hi : i<FormulaSignSlotRadialProviderRecordPlan.count (root c)) :
    IntegralFramedPhysicalGridReplay.point B (seedContext c) W.word W.valid (4*i)=v i := by
  have HB : i<(family (B).parameters (B).plan (B).data).birth ((B).key (seedContext c)) := by
    rw [full_birth,older_length]
    omega
  exact (FormulaSignSlotRadialProviderAtomic.ReplayFields.grid_point_env B T
    FormulaSignSlotRadialProviderAtomic.bank_represents (seedContext c) W.word W.valid i HB).trans (W.prelude_field i hi)

theorem external_fits (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool) :
    FormulaSignSlotRadialExternalReplay.fits (FormulaSignSlotRadialExternalContext.packet H K Gamma label s w) := by
  unfold FormulaSignSlotRadialExternalReplay.fits
  rw [FormulaSignSlotRadialExternalContext.number_packet,FormulaSignSlotRadialExternalContext.sideNat_packet,
    FormulaSignSlotRadialExternalContext.gridContext_packet]
  have HC := FormulaSignSlotRadialExternalCoordinates.count_packet H K Gamma
  change ImplicitSourceGramGrid.count FormulaSignSlotRadialJointStratum.source
    (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma)=_ at HC
  rw [HC]
  by_cases hn : FormulaSignSlotRadialJointLayout.circleCount s H=0
  · exact Or.inl hn
  · right
    exact FormulaSignSlotRadialExternalContext.slot_lt H s
      ⟨FormulaSignSlotRadialJointLayout.circleCount s H-1,by omega⟩

private theorem provider_external_packet (BB : IntegralFramedBankQuery.Bank) (ctx t w : List Bool)
    (he : FormulaSignSlotRadialExternalContext.external ctx)
    (ha : FormulaSignSlotRadialProviderReplay.associated ctx)
    (hh : FormulaSignSlotRadialExternalReplay.packet ctx t w∈FormulaSignSlotRadialExternalReplay.languageAt BB) :
    FormulaSignSlotRadialProviderReplay.packet ctx t w∈FormulaSignSlotRadialProviderReplay.languageAt BB := by
  apply (FormulaSignSlotRadialProviderReplay.external_iff BB (FormulaSignSlotRadialProviderReplay.packet ctx t w)
    (by simpa only [FormulaSignSlotRadialProviderReplay.packet,FormulaSignSlotRadialExternalReplay.packet,
      FormulaSignSlotRadialProviderReplay.context,FormulaSignSlotRadialExternalReplay.context,pairFst_pair] using he)).mpr
  refine ⟨?_,hh⟩
  simpa only [FormulaSignSlotRadialProviderReplay.packet,FormulaSignSlotRadialExternalReplay.packet,
    FormulaSignSlotRadialProviderReplay.context,FormulaSignSlotRadialExternalReplay.context,pairFst_pair] using ha

section External
variable (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (oldWord : List Bool)
local notation "ctx" => FormulaSignSlotRadialExternalContext.packet H K Gamma label s oldWord

theorem WordReceipt.replay_external {v : ℕ→ℝ} {p : Fin ((P).ambient (root ctx)+1)→ℝ}
    (W : WordReceipt ctx v p) (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid ctx)
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma) oldWord∈
      FormulaSignSlotRadialJointStratumSampler.language)
    (hV : ∀i<FormulaSignSlotRadialExternalContext.number ctx,
      v i=FormulaSignSlotRadialExternalCoordinates.point ctx hw i) :
    FormulaSignSlotRadialProviderAtomic.Replay (packet ctx W.word) := by
  unfold FormulaSignSlotRadialProviderAtomic.Replay
  rw [replay_query_packet]
  apply provider_external_packet B ctx (seedContext ctx) W.word
    (FormulaSignSlotRadialExternalContext.external_packet H K Gamma label s oldWord)
    (FormulaSignSlotRadialProviderReplay.associated_packet H K Gamma label s oldWord)
  apply (external_packet_iff B ctx (seedContext ctx) W.word).mpr
  have HA : FormulaSignSlotRadialExternalReplay.accepted ctx := by
    simpa only [FormulaSignSlotRadialExternalReplay.accepted,
      FormulaSignSlotRadialExternalContext.gridContext_packet,FormulaSignSlotRadialExternalContext.ownWord_packet] using hq
  refine ⟨FormulaSignSlotRadialExternalContext.external_packet H K Gamma label s oldWord,
    external_fits H K Gamma label s oldWord,HA,W.valid,?_⟩
  intro i hi
  exact (hV i hi).symm.trans (W.grid_field i (by
    rw [count_root]
    change i<FormulaSignSlotRadialExternalContext.number ctx+8
    omega)).symm

end External

local notation "hn" => CanonicalAuxiliaryCandidateCover.dimension_unary
local notation "ht" => CanonicalAuxiliaryCandidateCover.equation_FP
local notation "ha" => CanonicalAuxiliaryCandidateCover.equation_scope

private theorem old_packet_iff {nn : List Bool→ℕ} {tt : List Bool→LeanCanny.ETR.Term}
    (hN : UnaryFn nn) (hT : (fun q=>(tt q).toData.toBits)∈FP) (hA : ∀q,(tt q).arity≤nn q)
    (BB : IntegralFramedBankQuery.Bank) (ctx t w : List Bool) :
    FormulaSignSlotRadialProviderReplay.packet ctx t w∈IntegralFramedPhysicalCandidateReplayThom.language hN hT hA BB ↔
      ∃ hp : IntegralMixedAuxiliaryCandidate.Valid hN hT hA (pairFst ctx),
        ∃ hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input BB) t w,
          ∀i : Fin (nn (pairFst (pairFst ctx))),
            IntegralMixedAuxiliaryCandidate.point hN hT hA (pairFst ctx) hp i=
              IntegralFramedPhysicalCandidateReplay.point (n:=nn) BB ctx t w hw i := by
  have HH := IntegralFramedPhysicalCandidateReplayThom.language_iff hN hT hA BB
    (FormulaSignSlotRadialProviderReplay.packet ctx t w)
  unfold IntegralFramedPhysicalCandidateReplayThom.dimension IntegralFramedPhysicalCandidateReplayThom.oldCandidate at HH
  have HCtx : IntegralFramedPhysicalCandidateReplayThom.context
      (FormulaSignSlotRadialProviderReplay.packet ctx t w)=ctx := pairFst_pair _ _
  have HT : IntegralFramedPhysicalCandidateReplayThom.target
      (FormulaSignSlotRadialProviderReplay.packet ctx t w)=t := by
    simp only [IntegralFramedPhysicalCandidateReplayThom.target,FormulaSignSlotRadialProviderReplay.packet,
      FormulaSignSlotRadialExternalReplay.packet,pairSnd_pair,pairFst_pair]
  have HW : IntegralFramedPhysicalCandidateReplayThom.word
      (FormulaSignSlotRadialProviderReplay.packet ctx t w)=w := by
    simp only [IntegralFramedPhysicalCandidateReplayThom.word,FormulaSignSlotRadialProviderReplay.packet,
      FormulaSignSlotRadialExternalReplay.packet,pairSnd_pair]
  rw [HCtx,HT,HW] at HH
  exact HH

theorem WordReceipt.replay_old {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p) (he : ¬FormulaSignSlotRadialExternalContext.external c)
    (hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pairFst c))
    (hV : ∀i : Fin (FormulaSignSlotRadialExternalContext.number c),
      IntegralMixedAuxiliaryCandidate.point hn ht ha (pairFst c) hp i=v i.val) :
    FormulaSignSlotRadialProviderAtomic.Replay (packet c W.word) := by
  unfold FormulaSignSlotRadialProviderAtomic.Replay
  rw [replay_query_packet]
  apply (FormulaSignSlotRadialProviderReplay.old_iff B
    (FormulaSignSlotRadialProviderReplay.packet c (seedContext c) W.word)
      (by simpa only [FormulaSignSlotRadialProviderReplay.packet,FormulaSignSlotRadialExternalReplay.packet,
        FormulaSignSlotRadialProviderReplay.context,FormulaSignSlotRadialExternalReplay.context,pairFst_pair] using he)).mpr
  apply (old_packet_iff hn ht ha B c (seedContext c) W.word).mpr
  refine ⟨hp,W.valid,?_⟩
  intro i
  have HI : i.val<FormulaSignSlotRadialExternalContext.number c := i.isLt
  rw [FormulaSignSlotRadialProviderReplay.old_point_eq]
  exact (hV i).trans (W.grid_field i.val (by
    rw [count_root]
    change i.val<FormulaSignSlotRadialExternalContext.number c+8
    omega)).symm

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
