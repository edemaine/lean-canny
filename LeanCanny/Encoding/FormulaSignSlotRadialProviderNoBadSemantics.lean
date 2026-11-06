/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeBounds
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutIntervalMeaning
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderBankContext
public import LeanCanny.Encoding.IntegralFramedTraceCutObservation
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshotRawBad
/-! # Native provider bad probes refer to their original quotient-determined parent -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderNoBadSemantics
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedRoadmapBadProbePacket (root count labels word producer creating)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => IntegralFramedBankQuery.Bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank
local notation "D" => IntegralFramedBankQuery.Bank.plan FormulaSignSlotRadialProviderRecordPlan.bank
local notation "H" => IntegralFramedBankQuery.Bank.data FormulaSignSlotRadialProviderRecordPlan.bank
local notation "G" => family P D H
local notation "S" => FormulaSignSlotRadialProviderAtomic.input
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
local notation "C" => IntegralMixedCausalRecordPlanBits.count
local notation "ctx" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "IC" => FormulaSignSlotRadialProviderBadProbeTest.intervalContext
local notation "dim" => FormulaSignSlotRadialProviderBadProbeTest.dimension
local notation "ini" => FormulaSignSlotRadialProviderBadProbeTest.initial
local notation "wid" => FormulaSignSlotRadialProviderBadProbeTest.width
local notation "new" => FormulaSignSlotRadialProviderBadProbeProvenance.prepared
local notation "birth" => FormulaSignSlotRadialProviderBadProbeProvenance.birth
local notation "saved" => FormulaSignSlotRadialProviderBadProbeProvenance.saved
local notation "parent" => FormulaSignSlotRadialProviderCutInterval.parent

private theorem family_cap (p : Parameters) (d : Plan p)
    (h : IntegralMixedFramedHistoryFamilyBits.Data p d) (k : List Bool) :
    (family p d h).cap k=p.cap (pairFst k)+1 := rfl

private theorem bank_natural (E : IntegralFramedBankQuery.Bank) (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input E) c w) :
    FormulaSignSlotRadialProviderRecordPrefix.bankNatural E c w hv=
      IntegralFramedPhysicalSquare.naturalPoint E.parameters E.plan E.data E.nodes E.factor E.seed E.bounds
        E.key E.positive c w hv := rfl

private theorem raw_rule_family (p : Parameters) (d : Plan p)
    (h : IntegralMixedFramedHistoryFamilyBits.Data p d) (k labels : List Bool) (j b : ℕ)
    (hg : IntegralMixedChronologicalCutCode.Good (p.ambient (pairFst k)) b labels
      (WordListRecords.count labels+1) j)
    (hb : b=(family p d h).birth k)
    (hr : (family p d h).rule k=(IntegralMixedChronologicalCutCode.rawData
      (p.ambient (pairFst k)) b labels (WordListRecords.count labels+1) j hg).rule
        (commonDenominator ((family p d h).state k)) (commonDenominator_ne_zero ((family p d h).state k))) :
    ∃HG : IntegralMixedChronologicalCutCode.Good ((family p d h).ambient k) ((family p d h).birth k)
      labels (WordListRecords.count labels+1) j,
      (family p d h).rule k=(IntegralMixedChronologicalCutCode.rawData
        ((family p d h).ambient k) ((family p d h).birth k) labels (WordListRecords.count labels+1) j HG).rule
        (commonDenominator ((family p d h).state k)) (commonDenominator_ne_zero ((family p d h).state k)) := by
  cases hb
  exact ⟨hg,hr⟩

private theorem selected_eval (p : Parameters) (d : Plan p)
    (h : IntegralMixedFramedHistoryFamilyBits.Data p d) (par : List Bool→List Bool) (q : List Bool)
    (φ : ((family p d h).state (IntegralMixedVirtualTaskBits.saved p (par q))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (t : ℝ) : (IntegralMixedFramedFullCutIntervalSelected.factor p d h par q φ).eval t=
      (IntegralMixedRelativeCuts.factor ((family p d h).state (IntegralMixedVirtualTaskBits.saved p (par q)))
        ((family p d h).birth_bound _) ((family p d h).rule _) ((family p d h).kind _)).eval₂ φ.toRingHom t := by
  simp only [IntegralMixedFramedFullCutIntervalSelected.factor,Polynomial.eval_map]
  rfl

private theorem root_of_failure {p : Polynomial ℝ} {a b : ℝ} {L : Prop}
    (he : L↔a<b∧∀t,p.eval t=0→t∉Set.Ioo a b) (hab : a<b) (hn : ¬L) :
    ∃t∈Set.Ioo a b,p.eval t=0 := by
  by_contra! HN
  exact hn (he.mpr ⟨hab,fun t ht hi=>HN t hi ht⟩)

private theorem ordinary_mem_bad (F : IntegralMixedCutSource.Family) (key labels : List Bool) (j : ℕ)
    (hg : IntegralMixedChronologicalCutCode.Good (F.ambient key) (F.birth key) labels
      (WordListRecords.count labels+1) j)
    (hr : F.rule key=(IntegralMixedChronologicalCutCode.rawData (F.ambient key) (F.birth key) labels
      (WordListRecords.count labels+1) j hg).rule (commonDenominator (F.state key))
        (commonDenominator_ne_zero (F.state key)))
    (φ : (F.state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : ℕ→ℝ)
    (hφ : ∀i,φ ((F.state key).bank.numerator i)/((F.state key).bank.denominator i:ℝ)=values i.val)
    (hv : IntegralMixedRelativeCuts.Valid (F.state key) (F.birth_bound key) (F.rule key) φ (F.kind key))
    (ho : IntegralMixedSelectedBadMembership.Ordinary (F.rule key) (F.kind key)) (t : ℝ)
    (ht : (IntegralMixedRelativeCuts.factor (F.state key) (F.birth_bound key) (F.rule key) (F.kind key)).eval₂ φ.toRingHom t=0)
    (hx : Canonical (F.state key)) :
    t∈(IntegralMixedPrefixSnapshot.ofState (F.state key)).bad labels values := by
  have HF := IntegralMixedPrefixSnapshot.ofState_mem_bad_iff (F.state key) (F.birth_bound key) hx
    labels j hg φ values hφ t
  rw [←hr] at HF
  exact HF.mpr ⟨F.kind key,hv,ho,ht⟩

private theorem present_from_interpretation (F : IntegralMixedCutSource.Family) (key labels : List Bool) (j : ℕ)
    (hg : IntegralMixedChronologicalCutCode.Good (F.ambient key) (F.birth key) labels
      (WordListRecords.count labels+1) j)
    (hr : F.rule key=(IntegralMixedChronologicalCutCode.rawData (F.ambient key) (F.birth key) labels
      (WordListRecords.count labels+1) j hg).rule (commonDenominator (F.state key))
        (commonDenominator_ne_zero (F.state key)))
    (hx : Canonical (F.state key))
    (ho : IntegralMixedSelectedBadMembership.Ordinary (F.rule key) (F.kind key))
    (GP : ((F.state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)→Prop)
    (poly : ((F.state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)→Polynomial ℝ)
    (values : ℕ→ℝ) (a b : ℝ) (d : ℕ) (L : Prop)
    (hvalues : ∀φ,GP φ→∀i,φ ((F.state key).bank.numerator i)/
      ((F.state key).bank.denominator i:ℝ)=values i.val)
    (hpoly : ∀φ t,(poly φ).eval t=(IntegralMixedRelativeCuts.factor (F.state key)
      (F.birth_bound key) (F.rule key) (F.kind key)).eval₂ φ.toRingHom t)
    (HP : ∃φ,GP φ∧IntegralMixedRelativeCuts.Valid (F.state key) (F.birth_bound key) (F.rule key) φ
      (F.kind key)∧poly φ≠0∧(poly φ).natDegree=d∧(L↔a<b∧∀t,(poly φ).eval t=0→t∉Set.Ioo a b))
    (hab : a<b) (hn : ¬L) :
    ∃t∈Set.Ioo a b,t∈(IntegralMixedPrefixSnapshot.ofState (F.state key)).bad labels values := by
  obtain ⟨φ,hφ,hv,_,_,he⟩ := HP
  obtain ⟨t,ht,hr0⟩ := root_of_failure he hab hn
  exact ⟨t,ht,ordinary_mem_bad F key labels j hg hr φ values (hvalues φ hφ) hv ho t
    ((hpoly φ t).symm.trans hr0) hx⟩

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderRecordPrefix.bankNatural IntegralFramedPhysicalSquare.naturalPoint
  IntegralFramedPhysicalSquare.input

section
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank IntegralMixedFramedHistoryFamilyBits.family
private theorem record_natural (r w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid S (ctx r) w) :
    FormulaSignSlotRadialProviderRecordPrefix.natural r w hv=
      IntegralFramedPhysicalSquare.naturalPoint (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (B).key (B).positive (ctx r) w hv := by
  unfold FormulaSignSlotRadialProviderRecordPrefix.natural
  exact bank_natural B (ctx r) w hv
end

noncomputable def endpoint (base : List Bool)
    (hv : SquareSampleCompleteVertices.Valid S (ctx (root base)) (word base)) (side : Bool) : ℝ :=
  FormulaSignSlotRadialProviderAtomic.bankField (ctx (root base)) (word base) hv (producer side base)

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  FormulaSignSlotRadialProviderCutInterval.parent FormulaSignSlotRadialProviderCutInterval.endpoint
  FormulaSignSlotRadialProviderBadProbeParent.snapshot FormulaSignSlotRadialProviderBadProbeParent.values

private theorem context_saved (z : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (parent (IC z))=saved z :=
  FormulaSignSlotRadialProviderBadProbeProvenance.context_saved z

variable (z w : List Bool)
  (hh : IntegralMixedRoadmapBadProbePacket.HintGood (dim z) (ini z) (wid z) z)
  (hw : SquareSampleCompleteVertices.Valid S (IC z) w)
include hw in
theorem prepared_valid : SquareSampleCompleteVertices.Valid S (ctx (new z)) w :=
  (FormulaSignSlotRadialProviderBankContext.valid_iff (IC z) (ctx (new z)) w
    ((FormulaSignSlotRadialProviderBadProbeProvenance.context_root z).trans (pairFst_pair _ _).symm)).mp hw
local notation "emptyValid" => prepared_valid z w hw
local notation "old" => IntegralMixedVirtualTaskBits.saved P (parent (IC z))

include hh in
theorem interval_quotients
    (φ : ((G).state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : FormulaSignSlotRadialProviderCutInterval.IntervalGenerators (IC z) w hw φ) :
    ∀i,φ (((G).state old).bank.numerator i)/(((G).state old).bank.denominator i:ℝ)=
      FormulaSignSlotRadialProviderBadProbeParent.values (new z) w emptyValid i.val := by
  have HB := FormulaSignSlotRadialProviderBadProbeBounds.bounds z hh w
  have HCtx := context_saved z
  have HK := HCtx.trans (FormulaSignSlotRadialProviderBadProbeProvenance.saved_key z hh)
  have HBirth : birth z=N (new z)+(C (new z)-1) := by
    rw [FormulaSignSlotRadialProviderBadProbeProvenance.birth_eq z hh,
      FormulaSignSlotRadialProviderBadProbeProvenance.prepared_count z hh]
  have HM : birth z≤prefixLength P ((B).key (IC z)) := by
    have HC := FormulaSignSlotRadialProviderCutInterval.bank_birth (IC z)
    rw [family_birth] at HC
    have HP : prefixLength P ((B).key (IC z))=FormulaSignSlotRadialProviderRecordPlan.fullCount (new z) :=
      HC.trans ((FormulaSignSlotRadialProviderCutInterval.count_eq (IC z)).trans
        (congrArg FormulaSignSlotRadialProviderRecordPlan.fullCount
          (FormulaSignSlotRadialProviderBadProbeProvenance.context_root z)))
    exact (FormulaSignSlotRadialProviderBadProbeProvenance.birth_fit z hh).le.trans_eq HP.symm
  have HE : old=keyAt (pairFst ((B).key (IC z))) (birth z) (BinaryNatCode.encode 2) :=
    HK.trans (congrArg (fun r=>keyAt r (birth z) (BinaryNatCode.encode 2))
      ((FormulaSignSlotRadialProviderCutInterval.key_root (IC z)).trans
        (FormulaSignSlotRadialProviderBadProbeProvenance.context_root z)).symm)
  have HParent : old=IntegralMixedVirtualTaskBits.saved P
      (IntegralFramedPhysicalTraceCutSource.parent B (IC z)
        (FormulaSignSlotRadialProviderCutInterval.birthWord (IC z))) :=
    congrArg (IntegralMixedVirtualTaskBits.saved P) (FormulaSignSlotRadialProviderCutInterval.parent_eq (IC z))
  have HGen : ∀i,φ (((G).state old).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSuffixTest.rawTuple B (IC z) w hw
        (i.val+(IntegralFramedTerminalCutTest.count P D H (IntegralFramedPhysicalTraceCutSource.taskKey B)
          (IntegralFramedPhysicalTraceCutSource.parent B (IC z)
            (FormulaSignSlotRadialProviderCutInterval.birthWord (IC z)))-(G).birth old))^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P
        (IntegralFramedPhysicalTraceCutSource.parent B (IC z)
          (FormulaSignSlotRadialProviderCutInterval.birthWord (IC z))))
        (2^(G).width old) ((G).birth old) i := by
    intro i
    have Hi := hφ i
    refine Hi.trans ?_
    exact congrArg₂ (fun (v : ℝ) (e : ℕ)=>v^e)
      (congrArg (fun p=>IntegralFramedPhysicalSuffixTest.rawTuple B (IC z) w hw
        (i.val+(IntegralFramedTerminalCutTest.count P D H (IntegralFramedPhysicalTraceCutSource.taskKey B) p-(G).birth old)))
        (FormulaSignSlotRadialProviderCutInterval.parent_eq (IC z)))
      (congrArg (fun p=>UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P p)
        (2^(G).width old) ((G).birth old) i) (FormulaSignSlotRadialProviderCutInterval.parent_eq (IC z)))
  have HQ := IntegralFramedPhysicalTraceCutSource.quotient_observation B
    FormulaSignSlotRadialProviderAtomic.Cuts.key_context (IC z) w hw
    (FormulaSignSlotRadialProviderCutInterval.birthWord (IC z)) old HParent (birth z) HM
    (BinaryNatCode.encode 2) HE (FormulaSignSlotRadialProviderCutInterval.terminal_fits (IC z) w HB) φ HGen
  have HO0 := congrArg (IntegralFramedPhysicalScalarObservation.atKeyObservation P D) HK
  have HBnd := HBirth.trans_le (FormulaSignSlotRadialProviderRecordPrefix.bank_bound
    (new z) (C (new z)-1) (Nat.sub_le _ _))
  have HO1 := IntegralFramedPhysicalScalarObservation.observation_keyAt P D (new z) (birth z)
    (BinaryNatCode.encode 2) HBnd
  have HO2 := IntegralFramedPhysicalPrefixObservation.at_congr P D (new z) (new z) (birth z)
    (N (new z)+(C (new z)-1)) HBnd
    (FormulaSignSlotRadialProviderRecordPrefix.bank_bound (new z) (C (new z)-1) (Nat.sub_le _ _)) rfl HBirth
  have HO := HO0.trans (HO1.trans (HO2.trans
    (FormulaSignSlotRadialProviderRecordPrefix.bank_observation (new z) (C (new z)-1) (Nat.sub_le _ _))))
  have HN := FormulaSignSlotRadialProviderBankContext.natural_eq (IC z) (ctx (new z)) w
    ((FormulaSignSlotRadialProviderBadProbeProvenance.context_root z).trans (pairFst_pair _ _).symm) hw emptyValid
  have HZ := HN.trans (record_natural (new z) w emptyValid).symm
  intro i
  unfold FormulaSignSlotRadialProviderBadProbeParent.values
  exact (HQ i).trans ((congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.point
    (IntegralFramedPhysicalSquare.naturalPoint P D H (B).nodes (B).factor (B).seed (B).bounds
      (B).key (B).positive (IC z) w hw) i.val) HO).trans
      (congrArg (fun v : ℕ→ℝ=>(FormulaSignSlotRadialProviderRecordPrefix.observation (new z)
        (C (new z)-1) (Nat.sub_le _ _)).point v i.val) HZ))

include hh in
theorem ordinary_rule :
    ∃hg : IntegralMixedChronologicalCutCode.Good ((G).ambient old) ((G).birth old) (labels (pairFst z))
      (WordListRecords.count (labels (pairFst z))+1) (Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field 1 z)),
      (G).rule old=(IntegralMixedChronologicalCutCode.rawData ((G).ambient old) ((G).birth old)
        (labels (pairFst z)) (WordListRecords.count (labels (pairFst z))+1)
        (Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field 1 z)) hg).rule
          (commonDenominator ((G).state old)) (commonDenominator_ne_zero ((G).state old)) := by
  rw [context_saved z]
  exact raw_rule_family P D H (saved z) (labels (pairFst z))
    (Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field 1 z)) _
    (FormulaSignSlotRadialProviderBadProbeProvenance.good_saved z hh)
    ((FormulaSignSlotRadialProviderBadProbeProvenance.creating_saved z hh).symm.trans
      (FormulaSignSlotRadialProviderBadProbeProvenance.saved_birth z hh).symm)
    (FormulaSignSlotRadialProviderBadProbeCommand.rule_eq z hh)

include hh in
private theorem ordinary_kind : IntegralMixedSelectedBadMembership.Ordinary ((G).rule old) ((G).kind old) := by
  rw [context_saved z]
  exact FormulaSignSlotRadialProviderBadProbeCommand.ordinary z hh

include hh in
private theorem saved_snapshot : IntegralMixedPrefixSnapshot.ofState ((G).state old)=
    FormulaSignSlotRadialProviderBadProbeParent.snapshot (new z) :=
  (congrArg (fun k=>IntegralMixedPrefixSnapshot.ofState ((G).state k))
    (context_saved z)).trans
    (FormulaSignSlotRadialProviderBadProbeProvenance.snapshot_saved z hh)

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank

attribute [local irreducible] FormulaSignSlotRadialProviderCutInterval.language
  FormulaSignSlotRadialProviderCutInterval.comparison FormulaSignSlotRadialProviderCutInterval.sign
  FormulaSignSlotRadialProviderCutInterval.head FormulaSignSlotRadialProviderCutInterval.choice
  FormulaSignSlotRadialProviderCutInterval.cap FormulaSignSlotRadialProviderCutInterval.degree
  FormulaSignSlotRadialProviderCutInterval.Bounds FormulaSignSlotRadialProviderCutInterval.IntervalGenerators
  IntegralMixedRelativeCuts.Valid IntegralMixedRelativeCuts.CoefficientGuards
  IntegralMixedFramedFullCutIntervalSelected.factor FormulaSignSlotRadialProviderBadProbeParent.bad

include hh in
theorem present_prepared
    (hg : FormulaSignSlotRadialProviderCutInterval.Guards (pair (IC z) w))
    (hab : FormulaSignSlotRadialProviderCutInterval.endpoint false (IC z) w hw
        (FormulaSignSlotRadialProviderCutInterval.left_bound (IC z) w
          (FormulaSignSlotRadialProviderBadProbeBounds.bounds z hh w))<
      FormulaSignSlotRadialProviderCutInterval.endpoint true (IC z) w hw
        (FormulaSignSlotRadialProviderCutInterval.right_bound (IC z) w
          (FormulaSignSlotRadialProviderBadProbeBounds.bounds z hh w)))
    (hn : pair (IC z) w∉FormulaSignSlotRadialProviderCutInterval.language) :
    ∃t∈Set.Ioo
        (FormulaSignSlotRadialProviderCutInterval.endpoint false (IC z) w hw
          (FormulaSignSlotRadialProviderCutInterval.left_bound (IC z) w
            (FormulaSignSlotRadialProviderBadProbeBounds.bounds z hh w)))
        (FormulaSignSlotRadialProviderCutInterval.endpoint true (IC z) w hw
          (FormulaSignSlotRadialProviderCutInterval.right_bound (IC z) w
            (FormulaSignSlotRadialProviderBadProbeBounds.bounds z hh w))),
      t∈FormulaSignSlotRadialProviderBadProbeParent.bad (new z) w (labels (pairFst z)) emptyValid := by
  have HB := FormulaSignSlotRadialProviderBadProbeBounds.bounds z hh w
  have HRaw := ordinary_rule z hh
  let hraw := Classical.choose HRaw
  have HR := Classical.choose_spec HRaw
  have HP := present_from_interpretation G old (labels (pairFst z))
    (Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field 1 z)) hraw HR
    (family_canonical P D H old) (ordinary_kind z hh)
    (FormulaSignSlotRadialProviderCutInterval.IntervalGenerators (IC z) w hw)
    (IntegralMixedFramedFullCutIntervalSelected.factor P D H parent (IC z))
    (FormulaSignSlotRadialProviderBadProbeParent.values (new z) w emptyValid) _ _
    (FormulaSignSlotRadialProviderCutInterval.degree (IC z))
    (pair (IC z) w∈FormulaSignSlotRadialProviderCutInterval.language)
    (fun φ hφ=>interval_quotients z w hh hw φ hφ)
    (fun φ t=>selected_eval P D H parent (IC z) φ t)
    (FormulaSignSlotRadialProviderCutInterval.interpreted_empty_iff (IC z) w hw HB hg) hab hn
  obtain ⟨t,ht,HX⟩ := HP
  have HS := saved_snapshot z hh
  unfold FormulaSignSlotRadialProviderBadProbeParent.bad
  exact ⟨t,ht,(congrArg (fun d : IntegralMixedPrefixSnapshot.Data=>
    t∈d.bad (labels (pairFst z)) (FormulaSignSlotRadialProviderBadProbeParent.values (new z) w emptyValid)) HS).mp HX⟩

private theorem bank_field_context (c d w : List Bool) (hr : pairFst c=pairFst d)
    (hc : SquareSampleCompleteVertices.Valid S c w) (hd : SquareSampleCompleteVertices.Valid S d w)
    (i : ℕ) (hi : i<FormulaSignSlotRadialProviderFieldEquality.count c) :
    FormulaSignSlotRadialProviderAtomic.bankField c w hc i=
      FormulaSignSlotRadialProviderAtomic.bankField d w hd i := by
  have HE : FormulaSignSlotRadialProviderFieldEquality.count c=FormulaSignSlotRadialProviderFieldEquality.count d :=
    (FormulaSignSlotRadialProviderFieldEquality.count_eq c).trans
      ((congrArg FormulaSignSlotRadialProviderRecordPlan.fullCount hr).trans
        (FormulaSignSlotRadialProviderFieldEquality.count_eq d).symm)
  exact (FormulaSignSlotRadialProviderFieldEquality.point_env c w hc i hi).symm.trans
    ((FormulaSignSlotRadialProviderBankContext.point_eq c d w hr hc hd i).trans
      (FormulaSignSlotRadialProviderFieldEquality.point_env d w hd i (hi.trans_eq HE)))

include hh in
theorem producer_fit (side : Bool) : producer side (pairFst z)<birth z := by
  cases side
  · exact hh.2.2.2.2.2.2.2.1
  · exact hh.2.2.2.2.2.2.2.2

include hh in
theorem endpoint_eq
    (hl : SquareSampleCompleteVertices.Valid S (ctx (root (pairFst z))) (word (pairFst z)))
    (hf : FormulaSignSlotRadialProviderBadProbeFields.packet (dim z) (ini z) z w∈
      FormulaSignSlotRadialProviderFieldEqualityList.language) (side : Bool) :
    FormulaSignSlotRadialProviderCutInterval.endpoint side (IC z) w hw
      (by cases side
          · exact FormulaSignSlotRadialProviderCutInterval.left_bound (IC z) w
              (FormulaSignSlotRadialProviderBadProbeBounds.bounds z hh w)
          · exact FormulaSignSlotRadialProviderCutInterval.right_bound (IC z) w
              (FormulaSignSlotRadialProviderBadProbeBounds.bounds z hh w))=
      endpoint (pairFst z) hl side := by
  have HP := producer_fit z hh side
  have HF := (FormulaSignSlotRadialProviderBadProbeFields.packet_iff (dim z) (ini z) z w hh.1
    (FormulaSignSlotRadialProviderBadProbeProvenance.initial_eq z) hl emptyValid).mp hf
  have HI : producer side (pairFst z)<FormulaSignSlotRadialProviderFieldEquality.count (IC z) := by
    rw [FormulaSignSlotRadialProviderFieldEquality.count_eq,
      FormulaSignSlotRadialProviderBadProbeProvenance.context_root,
      ←FormulaSignSlotRadialProviderBadProbeProvenance.last_birth z hh]
    omega
  have HE := FormulaSignSlotRadialProviderCutInterval.endpoint_env side (IC z) w hw
    (by cases side
        · exact FormulaSignSlotRadialProviderCutInterval.left_bound (IC z) w
            (FormulaSignSlotRadialProviderBadProbeBounds.bounds z hh w)
        · exact FormulaSignSlotRadialProviderCutInterval.right_bound (IC z) w
            (FormulaSignSlotRadialProviderBadProbeBounds.bounds z hh w))
  have HIndex : FormulaSignSlotRadialProviderCutInterval.count (IC z)-1-
      FormulaSignSlotRadialProviderCutInterval.selected side (IC z)=producer side (pairFst z) := by
    rw [FormulaSignSlotRadialProviderBadProbeBounds.count z hh,FormulaSignSlotRadialProviderBadProbeBounds.selected]
    omega
  rw [HIndex] at HE
  exact HE.trans ((bank_field_context (IC z) (ctx (new z)) w
    ((FormulaSignSlotRadialProviderBadProbeProvenance.context_root z).trans (pairFst_pair _ _).symm)
    hw emptyValid _ HI).trans (HF _ HP).symm)

theorem ordinary_bad
    (hl : SquareSampleCompleteVertices.Valid S (ctx (root (pairFst z))) (word (pairFst z)))
    (hW : FormulaSignSlotRadialProviderBadProbeTest.Witness (pair z w))
    (hab : endpoint (pairFst z) hl false<endpoint (pairFst z) hl true) :
    ∃t∈Set.Ioo (endpoint (pairFst z) hl false) (endpoint (pairFst z) hl true),
      t∈FormulaSignSlotRadialProviderBadProbeParent.bad (root (pairFst z)) (word (pairFst z))
        (labels (pairFst z)) hl := by
  have HH : IntegralMixedRoadmapBadProbePacket.HintGood (dim z) (ini z) (wid z) z := by
    simpa only [pairFst_pair] using hW.1
  have HV : SquareSampleCompleteVertices.Valid S (IC z) w := by
    simpa only [pairFst_pair,pairSnd_pair] using hW.2.2.1
  have HF : FormulaSignSlotRadialProviderBadProbeFields.packet (dim z) (ini z) z w∈
      FormulaSignSlotRadialProviderFieldEqualityList.language := by
    simpa only [FormulaSignSlotRadialProviderBadProbeTest.fieldPacket,
      FormulaSignSlotRadialProviderBadProbeFields.packet,FormulaSignSlotRadialProviderRecordPrefix.context,
      pairFst_pair,pairSnd_pair] using hW.2.1
  have HG : FormulaSignSlotRadialProviderCutInterval.Guards (pair (IC z) w) := by
    simpa only [FormulaSignSlotRadialProviderBadProbeTest.intervalPacket,pairFst_pair,pairSnd_pair] using hW.2.2.2.2.1
  have HN : pair (IC z) w∉FormulaSignSlotRadialProviderCutInterval.language := by
    simpa only [FormulaSignSlotRadialProviderBadProbeTest.intervalPacket,pairFst_pair,pairSnd_pair] using hW.2.2.2.2.2
  have HE := endpoint_eq z w HH HV hl HF
  have HO : FormulaSignSlotRadialProviderCutInterval.endpoint false (IC z) w HV
      (FormulaSignSlotRadialProviderCutInterval.left_bound (IC z) w
        (FormulaSignSlotRadialProviderBadProbeBounds.bounds z HH w))<
      FormulaSignSlotRadialProviderCutInterval.endpoint true (IC z) w HV
        (FormulaSignSlotRadialProviderCutInterval.right_bound (IC z) w
          (FormulaSignSlotRadialProviderBadProbeBounds.bounds z HH w)) := by
    rw [HE false,HE true]
    exact hab
  obtain ⟨t,ht,hbad⟩ := present_prepared z w HH HV HG HO HN
  have HF0 : FormulaSignSlotRadialProviderBadProbeFields.packet (dim z) (N (root (pairFst z))) z w∈
      FormulaSignSlotRadialProviderFieldEqualityList.language := by
    rw [←FormulaSignSlotRadialProviderBadProbeProvenance.initial_eq z]
    exact HF
  have HB := FormulaSignSlotRadialProviderBadProbeParent.bad_eq_of_fields (dim z) z w HH.1 hl
    (prepared_valid z w HV) HF0
  refine ⟨t,?_,(congrArg (fun A : Set ℝ=>t∈A) HB.symm).mp hbad⟩
  simpa only [HE false,HE true] using ht

end LeanCanny.Encoding.FormulaSignSlotRadialProviderNoBadSemantics
