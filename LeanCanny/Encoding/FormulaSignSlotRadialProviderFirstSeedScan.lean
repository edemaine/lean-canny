/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedPhysical
/-! # Native critical and companion guards of the constructed own seed word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem inactive_scalar (BB : IntegralFramedBankQuery.Bank) (TT : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents BB.parameters BB.plan BB.data TT)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input BB) c w)
    (b : ℕ) (hb : ¬IntegralFramedPhysicalCompanionPoint.Active BB TT c b) :
    IntegralFramedPhysicalCompanionPoint.scalarValue BB TT hr c w b=InfinitesimalSign.encode 0 := by
  have HP := IntegralFramedPhysicalCriticalGuardTest.packet (IntegralFramedPhysicalBankTerm.input BB)
    BB.parameters BB.plan BB.data TT BB.nodes BB.factor BB.seed BB.bounds BB.key
    IntegralFramedPhysicalCriticalGuardScan.stage (IntegralFramedPhysicalCompanionPoint.count_eq BB TT hr)
    c w (List.replicate b true) hw
  change IntegralFramedPhysicalCompanionPoint.scalarValue BB TT hr c w b=InfinitesimalSign.encode (SignType.sign
    ((IntegralMixedFramedCriticalGuardBits.polynomial BB.parameters BB.plan BB.data TT
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum BB.key) IntegralFramedPhysicalCriticalGuardScan.stage
      (pair c (List.replicate b true))).eval₂ (Int.castRingHom ℝ)
        (IntegralFramedPhysicalCompanionPoint.fullTuple BB TT hr c w hw b))) at HP
  have HN : ¬IntegralMixedFramedCriticalGuardBits.Active BB.parameters TT
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum BB.key) IntegralFramedPhysicalCriticalGuardScan.stage
        (pair c (List.replicate b true)) := hb
  rw [IntegralMixedFramedCriticalGuardBits.polynomial,ite_eq_right HN,MvPolynomial.eval₂_zero,sign_zero] at HP
  exact HP

private theorem critical_holds (BB : IntegralFramedBankQuery.Bank) (TT : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents BB.parameters BB.plan BB.data TT)
    (hc : ∀c d,IntegralMixedFramedCriticalGuardBits.count BB.parameters TT
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum BB.key) (pair c d)=(IntegralFramedPhysicalBankTerm.input BB).count c)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input BB) c w)
    (h : ∀b,b<prefixLength BB.parameters (BB.key c)→IntegralFramedPhysicalCompanionPoint.Active BB TT c b→
      IntegralFramedPhysicalCompanionPoint.scalarValue BB TT hr c w b=InfinitesimalSign.encode 0) :
    IntegralFramedPhysicalCriticalGuardScan.holds (IntegralFramedPhysicalBankTerm.input BB) BB.parameters BB.plan
      BB.data TT BB.nodes BB.factor BB.seed BB.bounds BB.key hc (pair c w) := by
  simp only [IntegralFramedPhysicalCriticalGuardScan.holds,pairFst_pair]
  change ∀b,b<prefixLength BB.parameters (BB.key c)→
    IntegralFramedPhysicalCompanionPoint.scalarValue BB TT hr c w b=InfinitesimalSign.encode 0
  intro b hb
  by_cases ha : IntegralFramedPhysicalCompanionPoint.Active BB TT c b
  · exact h b hb ha
  · exact inactive_scalar BB TT hr c w hw b ha

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderIntegerSource.source IntegralMixedFramedHistoryFamilyBits.family

theorem sample_query_packet (c w : List Bool) : FormulaSignSlotRadialProviderAtomic.sampleQuery (packet c w)=
    pair (seedContext c) w := by
  rw [FormulaSignSlotRadialProviderAtomic.sampleQuery,context_packet,word_packet]
  rfl

theorem WordReceipt.correlation {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p) (a : ℕ) (ha : a<IntegralMixedCausalRecordPlanBits.count (root c)) :
    FormulaSignSlotRadialProviderAtomic.bankField (seedContext c) W.word W.valid
      (FormulaSignSlotRadialProviderRecordPlan.count (root c)+a)=
      nativePoint c p ⟨FormulaSignSlotRadialProviderAtomic.selected (seedContext c)
        (FormulaSignSlotRadialProviderRecordPlan.count (root c)+a),
          FormulaSignSlotRadialProviderAtomic.selected_lt _ _ (critical_active c a ha)⟩ := by
  refine (W.critical_field a ha).trans ?_
  apply congrArg p
  apply Fin.ext
  have HS := critical_selected c a ha
  have HD := congrArg (fun d=>IntegralMixedRoadmapSeedMetadata.selected d a) (ambient_root c)
  exact HD.trans HS.symm

private theorem critical_packet (cc w : List Bool) : pair cc w∈FormulaSignSlotRadialProviderAtomic.criticalLanguage ↔
    SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input cc w ∧
      IntegralFramedPhysicalCriticalGuardScan.holds FormulaSignSlotRadialProviderAtomic.input
        (B).parameters (B).plan (B).data T (B).nodes (B).factor (B).seed (B).bounds (B).key
        FormulaSignSlotRadialProviderAtomic.critical_count (pair cc w) := by
  simp only [FormulaSignSlotRadialProviderAtomic.criticalLanguage,IntegralFramedPhysicalCriticalGuardScan.language,
    Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair]

theorem WordReceipt.all_critical {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p) : FormulaSignSlotRadialProviderAtomic.CriticalScan (packet c W.word) := by
  change FormulaSignSlotRadialProviderAtomic.sampleQuery (packet c W.word)∈FormulaSignSlotRadialProviderAtomic.criticalLanguage
  rw [sample_query_packet,critical_packet]
  refine ⟨W.valid,?_⟩
  apply critical_holds B T FormulaSignSlotRadialProviderAtomic.bank_represents
    FormulaSignSlotRadialProviderAtomic.critical_count (seedContext c) W.word W.valid
  intro b hb hactive
  have HN : FormulaSignSlotRadialProviderRecordPlan.count (root c)≤b := by
    by_contra H
    exact integer_inactive c b (by omega) hactive
  obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le HN
  have HBound : prefixLength (B).parameters ((B).key (seedContext c))=
      FormulaSignSlotRadialProviderRecordPlan.count (root c)+IntegralMixedCausalRecordPlanBits.count (root c) := native_prefix c
  rw [HBound] at hb
  have HA : a<IntegralMixedCausalRecordPlanBits.count (root c) := by omega
  apply (FormulaSignSlotRadialProviderAtomic.scalarValue_zero_iff_field (seedContext c) W.word W.valid _ hactive).mpr
  rw [W.geometric_point a HA]
  exact W.correlation a HA

theorem seed_count_lower (c : List Bool) : dim c+2≤IntegralMixedCausalRecordPlanBits.count (root c) := by
  have H := IntegralMixedChronologicalSeedProgram.selections_length ((P).ambient (root c)) (older c).length (tail c)
  change (selections c).length=tail c+(P).ambient (root c)+2 at H
  rw [selections_count,ambient_root] at H
  omega

theorem companion_query_packet (c w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.companionQuery
      (FormulaSignSlotRadialProviderAtomic.dimension (packet c w))
      (FormulaSignSlotRadialProviderAtomic.initial (packet c w)) (packet c w)=
      pair (pair (seedContext c) w) (IntegralMixedPhysicalPointCompanionScan.descriptor
        (FormulaSignSlotRadialProviderRecordPlan.count (root c))
        (FormulaSignSlotRadialProviderRecordPlan.count (root c)+1) (dim c+1)) := by
  have HZ : IntegralMixedRoadmapAtomic.depth (packet c w)=0 := depth_packet c w
  have HA := IntegralMixedRoadmapAtomic.seed_anchor (dim c)
    (FormulaSignSlotRadialProviderRecordPlan.count (root c)) (packet c w) HZ
  rw [FormulaSignSlotRadialProviderAtomic.companionQuery,dimension_packet,initial_packet,←count_root]
  simp only [IntegralMixedRoadmapAtomic.first,HA,IntegralMixedRoadmapAtomic.free,HZ,Nat.sub_zero]
  rw [sample_query_packet]

theorem WordReceipt.companions {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p) :
    FormulaSignSlotRadialProviderAtomic.companionQuery
      (FormulaSignSlotRadialProviderAtomic.dimension (packet c W.word))
      (FormulaSignSlotRadialProviderAtomic.initial (packet c W.word)) (packet c W.word)∈
        FormulaSignSlotRadialProviderAtomic.Companions.language := by
  rw [companion_query_packet]
  have HK := seed_count_lower c
  have HA := critical_active c 0 (by omega)
  simp only [Nat.add_zero] at HA
  apply (FormulaSignSlotRadialProviderAtomic.companion_language_packet_iff (seedContext c) W.word W.valid
    (FormulaSignSlotRadialProviderRecordPlan.count (root c))
    (FormulaSignSlotRadialProviderRecordPlan.count (root c)+1) (dim c+1) HA (by
      have H := native_prefix c
      change prefixLength (B).parameters ((B).key (seedContext c))=_ at H
      rw [H]
      omega)).mpr
  intro j hj
  have HJ : 1+j<IntegralMixedCausalRecordPlanBits.count (root c) := by omega
  have HB : FormulaSignSlotRadialProviderAtomic.Active (seedContext c)
      (FormulaSignSlotRadialProviderRecordPlan.count (root c)+(1+j)) := critical_active c (1+j) HJ
  have HZero : FormulaSignSlotRadialProviderAtomic.geometricPoint (seedContext c) W.word W.valid
      (FormulaSignSlotRadialProviderRecordPlan.count (root c))=nativePoint c p := by
    simpa only [Nat.add_zero] using W.geometric_point 0 (by omega)
  have HE : FormulaSignSlotRadialProviderRecordPlan.count (root c)+1+j=
      FormulaSignSlotRadialProviderRecordPlan.count (root c)+(1+j) := by omega
  rw [HE]
  refine ⟨HB,?_,?_⟩
  · rw [W.geometric_point (1+j) HJ]
    exact HZero.symm
  · rw [HZero]
    exact W.correlation (1+j) HJ

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
