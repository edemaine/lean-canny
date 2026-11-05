/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedProgram
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicPointLanguage
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordReceipt
public import LeanCanny.Algebra.IntegralMixedStaticRecordHeaderReceipt
/-! # Exact creating metadata for the source-aware seed program -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderIntegerSource.source
local notation "N" c => FormulaSignSlotRadialProviderRecordPlan.count (root c)
local notation "C" c => IntegralMixedCausalRecordPlanBits.count (root c)

theorem native_ambient_root (c : List Bool) : (P).ambient (root c)=dim c := ambient_root c

noncomputable def stageHeader (r : List Bool) (b : ℕ) := IntegralMixedCommandHeaderBits.command
  (IntegralMixedFramedRootPullback.instructionAt P D r b).command

theorem stageHeader_records (r : List Bool) (b : ℕ) : stageHeader r b=
    (((FormulaSignSlotRadialProviderRecordReceipt.records r).reverse[b]?).map (fun s=>s.template.header)).getD IntegralMixedCommandHeaderBits.zero := by
  unfold stageHeader IntegralMixedFramedRootPullback.instructionAt
  rw [FormulaSignSlotRadialProviderRecordReceipt.rules r]
  exact IntegralMixedStaticRecordHeaderReceipt.commands_header _ _ _ _ _

theorem integer_header (r : List Bool) (b : ℕ) (hb : b<FormulaSignSlotRadialProviderRecordPlan.count r) :
    stageHeader r b=IntegralMixedCommandHeaderBits.zero := by
  rw [stageHeader_records]
  exact IntegralMixedStaticRecordHeaderReceipt.integer_header
    (FormulaSignSlotRadialProviderRecordPlan.spatial r) (FormulaSignSlotRadialProviderRecordPlan.positive r)
    (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap r) _ _ (FormulaSignSlotRadialProviderRecordReceipt.polynomial r) (FormulaSignSlotRadialProviderRecordReceipt.polynomial_nonzero r) (FormulaSignSlotRadialProviderRecordReceipt.polynomial_degree r)
    (IntegralMixedCausalRecordPlanBits.code r) b hb

theorem later_header (r : List Bool) (a : ℕ) (ha : a<IntegralMixedCausalRecordPlanBits.count r) :
    stageHeader r (FormulaSignSlotRadialProviderRecordPlan.count r+a)=
      (IntegralMixedCausalUnitRecordBits.record (FormulaSignSlotRadialProviderRecordPlan.spatial r)
        (FormulaSignSlotRadialProviderRecordPlan.positive r) (FormulaSignSlotRadialProviderRecordPlan.count r+a)
        (IntegralMixedCausalRecordPlanBits.code r a) (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap r)).template.header := by
  rw [stageHeader_records]
  exact IntegralMixedStaticRecordHeaderReceipt.later_header
    (FormulaSignSlotRadialProviderRecordPlan.spatial r) (FormulaSignSlotRadialProviderRecordPlan.positive r)
    (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap r) _ _ (FormulaSignSlotRadialProviderRecordReceipt.polynomial r) (FormulaSignSlotRadialProviderRecordReceipt.polynomial_nonzero r) (FormulaSignSlotRadialProviderRecordReceipt.polynomial_degree r)
    (IntegralMixedCausalRecordPlanBits.code r) a ha

private theorem empty_rule_header {n birth bwidth : ℕ} (S : SpatialSource n) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^bwidth)
    (j : ℕ) (hj : j<n+1) :
    (IntegralMixedCausalUnitRecordBits.record S hn birth
      (IntegralMixedChronologicalFrameCode.code n [] 0 j) hcap).template.header=
      (⟨1,j,0,0,0,0,1⟩ : IntegralMixedCommandHeaderBits.Header) :=by
  have HG:=IntegralMixedRoadmapChain.seed_point_good n birth j hj
  have HC:=IntegralMixedChronologicalFrameCode.raw_command S hn [] 0 j HG hcap 1 one_ne_zero
  have HE:=congrArg IntegralMixedCommandHeaderBits.command HC
  change (IntegralMixedCausalUnitRecordBits.record S hn birth
    (IntegralMixedChronologicalFrameCode.code n [] 0 j) hcap).template.header=_ at HE
  rw [HE]
  let dd:=IntegralMixedChronologicalFrameCode.descriptor n birth [] HG.1
  have HF : dd.frame.frozen.card=0:=by
    rw [dd.frozen_card,IntegralMixedChronologicalFrameCode.descriptor_length]
    exact WordListRecords.count_encode []
  have HP : FrozenCoordinateOrdering.permutation dd.frame.frozen=Equiv.refl (Fin (n+1)):=dd.prefix_frozen.permutation
  have HZ : ∀i : Fin (n+1),i∉dd.frame.frozen:=by
    intro i
    rw [dd.frozen_mem,IntegralMixedChronologicalFrameCode.descriptor_length]
    rw [show WordListRecords.count ([] : List Bool)=0 from WordListRecords.count_encode []]
    omega
  change (⟨1,(IntegralMixedFrozenFrame.freeCoordinate dd.frame ⟨j,hj⟩ (HZ _)).val%(n-dd.frame.frozen.card+1),
    dd.frame.frozen.card,(IntegralMixedFrozenFrame.freeCoordinate dd.frame ⟨0,by omega⟩ (HZ _)).val,0,0,1⟩ :
      IntegralMixedCommandHeaderBits.Header)=⟨1,j,0,0,0,0,1⟩
  simp only [IntegralMixedFrozenFrame.freeCoordinate,HF,HP,Equiv.refl_symm,Equiv.refl_apply,
    Nat.sub_zero,Nat.mod_eq_of_lt hj]

theorem critical_header (c : List Bool) (a : ℕ) (ha : a<C c) :
    stageHeader (root c) ((N c)+a)=
      (⟨1,IntegralMixedRoadmapSeedMetadata.selected (dim c) a,0,0,0,0,1⟩ : IntegralMixedCommandHeaderBits.Header) := by
  rw [later_header _ _ ha,raw_code c a ha]
  have HC : IntegralMixedChronologicalFrameCode.code (dim c) [] 0
      (IntegralMixedRoadmapSeedMetadata.selected (dim c) a)=
      IntegralMixedChronologicalFrameCode.code ((P).ambient (root c)) [] 0
        (IntegralMixedRoadmapSeedMetadata.selected (dim c) a) := by rw [native_ambient_root]
  rw [HC]
  exact empty_rule_header _ _ _ _ (by rw [ambient_root];exact IntegralMixedRoadmapSeedMetadata.selected_lt _ _)

private theorem stage_packet (c : List Bool) (b : ℕ) :
    IntegralFramedPhysicalCriticalGuardScan.stage (pair c (List.replicate b true))=b := by
  rw [IntegralFramedPhysicalCriticalGuardScan.stage,pairSnd_pair,List.length_replicate]
private theorem datum_packet (f : List Bool→List Bool) (c : List Bool) (b : ℕ) :
    IntegralFramedPhysicalCriticalGuardTest.keyDatum f (pair c (List.replicate b true))=f c :=
  congrArg f (pairFst_pair _ _)

theorem native_header (c : List Bool) (b : ℕ) :
    IntegralMixedFramedCriticalGuardBits.header T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) IntegralFramedPhysicalCriticalGuardScan.stage
      (pair (pair (root c) []) (List.replicate b true))=stageHeader (root c) b := by
  rw [IntegralMixedFramedCriticalGuardBits.header_actual P D (B).data T
    FormulaSignSlotRadialProviderAtomic.bank_represents,datum_packet,stage_packet]
  have HK : pairFst ((B).key (pair (root c) []))=root c := by
    simp only [FormulaSignSlotRadialProviderRecordPlan.bank,FormulaSignSlotRadialProviderRecordPlan.bankKey,
      keyAt,pairFst_pair]
  rw [HK]
  rfl

private theorem prefix_count (BB : IntegralFramedBankQuery.Bank) (cc : List Bool) :
    prefixLength BB.parameters (BB.key cc)=
      (IntegralMixedFramedBankSnapshotBits.atKey BB.parameters BB.plan BB.data (BB.key cc)).count :=
  (family_birth BB.parameters BB.plan BB.data (BB.key cc)).symm

theorem native_prefix (c : List Bool) : prefixLength P ((B).key (pair (root c) []))=(N c)+(C c) := by
  have H := FormulaSignSlotRadialProviderRecordPlan.bank_count (pair (root c) [])
  rw [pairFst_pair] at H
  exact (prefix_count B (pair (root c) [])).trans H

theorem integer_inactive (c : List Bool) (b : ℕ) (hb : b<N c) :
    ¬FormulaSignSlotRadialProviderAtomic.Active (pair (root c) []) b := by
  intro H
  have HH := H.2
  rw [native_header,integer_header _ _ hb] at HH
  cases HH

theorem critical_active (c : List Bool) (a : ℕ) (ha : a<C c) :
    FormulaSignSlotRadialProviderAtomic.Active (pair (root c) []) ((N c)+a) := by
  constructor
  · rw [datum_packet,stage_packet]
    change (N c)+a<prefixLength P ((B).key (pair (root c) []))
    rw [native_prefix]
    omega
  · rw [native_header,critical_header c a ha]

theorem critical_selected (c : List Bool) (a : ℕ) (ha : a<C c) :
    FormulaSignSlotRadialProviderAtomic.selected (pair (root c) []) ((N c)+a)=
      IntegralMixedRoadmapSeedMetadata.selected (dim c) a := by
  unfold FormulaSignSlotRadialProviderAtomic.selected IntegralFramedPhysicalCompanionPoint.selected
  rw [native_header,critical_header c a ha]
  exact Nat.zero_add _

private theorem header_packet (TT : IntegralMixedHeaderTablesBits.Tables) (f : List Bool→List Bool)
    (c : List Bool) (b : ℕ) : IntegralMixedFramedCriticalGuardBits.header TT
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum f) IntegralFramedPhysicalCriticalGuardScan.stage
        (pair c (List.replicate b true))=IntegralMixedCommandHeaderBits.lookup (TT.commands (pairFst (f c))) b := by
  rw [IntegralMixedFramedCriticalGuardBits.header,datum_packet,stage_packet]

theorem seed_key_root (c : List Bool) : pairFst ((B).key (pair (root c) []))=root c := by
  simp only [FormulaSignSlotRadialProviderRecordPlan.bank,FormulaSignSlotRadialProviderRecordPlan.bankKey,
    keyAt,pairFst_pair]

theorem native_span (c : List Bool) (b : ℕ) :
    IntegralMixedFramedPhysicalIndex.span P T (pair ((B).key (pair (root c) [])) (List.replicate b true))=
      if (stageHeader (root c) b).context=1 then IntegralMixedFramedPhysicalIndex.block (dim c)+1 else 1 := by
  have HH := native_header c b
  rw [header_packet] at HH
  unfold IntegralMixedFramedPhysicalIndex.span
  simp only [pairFst_pair,pairSnd_pair,List.length_replicate]
  rw [HH,seed_key_root,native_ambient_root]

private theorem prefix_succ (PP : Parameters) (TT : IntegralMixedHeaderTablesBits.Tables) (key : List Bool) (b : ℕ) :
    IntegralMixedFramedPhysicalIndex.prefixArity PP TT (pair key (List.replicate (b+1) true))=
      IntegralMixedFramedPhysicalIndex.prefixArity PP TT (pair key (List.replicate b true))+
        IntegralMixedFramedPhysicalIndex.span PP TT (pair key (List.replicate b true)) := by
  simp only [IntegralMixedFramedPhysicalIndex.prefixArity,pairFst_pair,pairSnd_pair,
    List.length_replicate,Finset.sum_range_succ]

theorem prefix_arity (c : List Bool) (a : ℕ) (ha : a≤C c) :
    IntegralMixedFramedPhysicalIndex.prefixArity P T
      (pair ((B).key (pair (root c) [])) (List.replicate ((N c)+a) true))=(N c)+(2*dim c+4)*a := by
  induction a with
  | zero =>
    simp only [Nat.add_zero,Nat.mul_zero]
    unfold IntegralMixedFramedPhysicalIndex.prefixArity
    simp only [pairFst_pair,pairSnd_pair,List.length_replicate]
    have HE : ∀j∈Finset.range (N c),IntegralMixedFramedPhysicalIndex.span P T
        (pair ((B).key (pair (root c) [])) (List.replicate j true))=1 := by
      intro j hj
      rw [native_span,integer_header _ _ (Finset.mem_range.mp hj)]
      rfl
    rw [Finset.sum_congr rfl HE]
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,Nat.mul_one]
  | succ a ih =>
    have HL : a<C c := by omega
    rw [show (N c)+(a+1)=((N c)+a)+1 by omega,prefix_succ,ih (by omega),native_span,critical_header c a HL]
    simp only [IntegralMixedFramedPhysicalIndex.block,ite_true]
    ring

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
