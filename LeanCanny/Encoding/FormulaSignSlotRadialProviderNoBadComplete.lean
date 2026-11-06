/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderNoBadSemantics
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCriticalMetadata
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperBase
public import LeanCanny.Encoding.IntegralMixedReservedCutActualVertex
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderReservedCutRealization
public import LeanCanny.Encoding.IntegralMixedSourceIntegerCutReceipt
public import LeanCanny.Encoding.IntegralMixedPrefixSnapshotCodedHint
public import LeanCanny.Algebra.IntegralMixedRelativeCutCoefficientIff
/-! # Original provider bad heights yield actual bounded native probe witnesses

Canonicalizing the four numbers preserves the literal prepared root and
interval query. Only words at that SAME root are retained in this argument.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeSearch
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem dimension_hint (base hint : List Bool) :
    FormulaSignSlotRadialProviderBadProbeTest.dimension (pair base hint)=
      FormulaSignSlotRadialProviderBadProbeTest.dimension (pair base []) :=by
  simp only [FormulaSignSlotRadialProviderBadProbeTest.dimension,pairFst_pair]
private theorem initial_hint (base hint : List Bool) :
    FormulaSignSlotRadialProviderBadProbeTest.initial (pair base hint)=
      FormulaSignSlotRadialProviderBadProbeTest.initial (pair base []) :=by
  simp only [FormulaSignSlotRadialProviderBadProbeTest.initial,dimension_hint]
private theorem width_hint (base hint : List Bool) :
    FormulaSignSlotRadialProviderBadProbeTest.width (pair base hint)=
      FormulaSignSlotRadialProviderBadProbeTest.width (pair base []) :=by
  simp only [FormulaSignSlotRadialProviderBadProbeTest.width,pairFst_pair]
attribute [local irreducible] FormulaSignSlotRadialProviderBadProbeTest.dimension
  FormulaSignSlotRadialProviderBadProbeTest.initial FormulaSignSlotRadialProviderBadProbeTest.width

private theorem probe_hint_eq (d : ℕ) (base hL hR : List Bool)
    (he : ∀i<4,Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i (pair base hL))=
      Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i (pair base hR))) :
    IntegralMixedRoadmapBadProbePacket.probe d (pair base hL)=
      IntegralMixedRoadmapBadProbePacket.probe d (pair base hR) :=by
  unfold IntegralMixedRoadmapBadProbePacket.probe
  simp only [pairFst_pair]
  rw [he 0 (by decide),he 1 (by decide),he 2 (by decide),he 3 (by decide)]

private theorem prepared_hint_eq (d : ℕ) (base hL hR : List Bool)
    (he : ∀i<4,Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i (pair base hL))=
      Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i (pair base hR))) :
    IntegralMixedRoadmapBadProbePacket.preparedRoot d (pair base hL)=
      IntegralMixedRoadmapBadProbePacket.preparedRoot d (pair base hR) :=by
  unfold IntegralMixedRoadmapBadProbePacket.preparedRoot IntegralMixedRoadmapBadProbePacket.preparedRaw
  simp only [pairFst_pair]
  rw [probe_hint_eq d base hL hR he]

theorem witness_hint_iff (base hL hR' w : List Bool)
    (he : ∀i<4,Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i (pair base hL))=
      Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i (pair base hR'))) :
    FormulaSignSlotRadialProviderBadProbeTest.Witness (pair (pair base hL) w) ↔
      FormulaSignSlotRadialProviderBadProbeTest.Witness (pair (pair base hR') w) :=by
  have HQ:=prepared_hint_eq (FormulaSignSlotRadialProviderBadProbeTest.dimension (pair base hL)) base hL hR' he
  simp only [dimension_hint] at HQ
  have HG : IntegralMixedRoadmapBadProbePacket.HintGood
      (FormulaSignSlotRadialProviderBadProbeTest.dimension (pair base hL))
      (FormulaSignSlotRadialProviderBadProbeTest.initial (pair base hL))
      (FormulaSignSlotRadialProviderBadProbeTest.width (pair base hL)) (pair base hL) ↔
    IntegralMixedRoadmapBadProbePacket.HintGood
      (FormulaSignSlotRadialProviderBadProbeTest.dimension (pair base hR'))
      (FormulaSignSlotRadialProviderBadProbeTest.initial (pair base hR'))
      (FormulaSignSlotRadialProviderBadProbeTest.width (pair base hR')) (pair base hR') :=by
    unfold IntegralMixedRoadmapBadProbePacket.HintGood
    simp only [pairFst_pair,dimension_hint,initial_hint,width_hint]
    rw [he 0 (by decide),he 1 (by decide),he 2 (by decide),he 3 (by decide)]
  have HI : FormulaSignSlotRadialProviderBadProbeTest.intervalContext (pair base hL)=
      FormulaSignSlotRadialProviderBadProbeTest.intervalContext (pair base hR') :=by
    unfold FormulaSignSlotRadialProviderBadProbeTest.intervalContext IntegralMixedRoadmapBadProbePacket.intervalContext
    simp only [pairFst_pair,dimension_hint,initial_hint]
    rw [HQ]
  have HF : FormulaSignSlotRadialProviderBadProbeTest.fieldPacket (pair (pair base hL) w)=
      FormulaSignSlotRadialProviderBadProbeTest.fieldPacket (pair (pair base hR') w) :=by
    unfold FormulaSignSlotRadialProviderBadProbeTest.fieldPacket
    simp only [pairFst_pair,pairSnd_pair,dimension_hint,initial_hint]
    rw [HQ]
  simp only [FormulaSignSlotRadialProviderBadProbeTest.Witness,pairFst_pair,pairSnd_pair,
    FormulaSignSlotRadialProviderBadProbeTest.intervalPacket,HG,HI,HF]

theorem hasBadProbe_iff (base : List Bool) : HasBadProbe base ↔
    ∃hint : List Bool,FormulaSignSlotRadialProviderBadProbeTest.HasWitness (pair base hint) :=by
  constructor
  · rintro ⟨bits,_,h⟩
    refine ⟨pairSnd (hintPacket (pair base bits)),?_⟩
    simpa only [hintPacket,pairFst_pair,pairSnd_pair] using h
  · rintro ⟨hint,h⟩
    obtain ⟨w,HW⟩:=(FormulaSignSlotRadialProviderBadProbeTest.hasWitness_iff _).mp h
    let e : ℕ→ℕ:=fun i=>Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i (pair base hint))
    have HG:=HW.1
    simp only [pairFst_pair,dimension_hint,initial_hint,width_hint] at HG
    have Hfit:=ordinary_fields_fit base (e 0) (e 1) (e 2) (e 3)
      HG.2.2.1 HG.2.2.2.2.1 HG.2.2.2.2.2.1 HG.2.2.2.2.2.2.1
    have HE : ∀i<4,e i<2^blockWidth base:=by
      intro i hi
      interval_cases i
      · exact Hfit.1
      · exact Hfit.2.1
      · exact Hfit.2.2.1
      · exact Hfit.2.2.2
    let bits:=FixedWidthNatVector.encode 4 (blockWidth base) e
    have HEq : ∀i<4,Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i
        (hintPacket (pair base bits)))=e i:=encode_fields base e HE
    refine ⟨bits,FixedWidthNatVector.length_encode _ _ _,?_⟩
    apply (FormulaSignSlotRadialProviderBadProbeTest.hasWitness_iff _).mpr
    refine ⟨w,?_⟩
    have HI:=witness_hint_iff base
      (pairSnd (hintPacket (pair base bits))) hint w (by
        intro i hi
        simpa only [hintPacket,pairFst_pair,pairSnd_pair] using HEq i hi)
    have Hnew:=HI.mpr HW
    simpa only [hintPacket,pairFst_pair,pairSnd_pair] using Hnew

theorem noBadProbe_iff (base : List Bool) : NoBadProbe base ↔
    ∀hint w : List Bool,¬FormulaSignSlotRadialProviderBadProbeTest.Witness (pair (pair base hint) w) :=by
  rw [NoBadProbe,hasBadProbe_iff]
  simp only [FormulaSignSlotRadialProviderBadProbeTest.hasWitness_iff,not_exists]

end LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeSearch

namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderNoBadComplete
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedRoadmapBadProbePacket (root count labels word field probe prefixCodes)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem realizes_from_snapshot {n S B m : ℕ} {Q : SpatialSource n} {ι : Type}
    (x : State Q S B m ι) (d : IntegralMixedPrefixSnapshot.Data)
    (he : IntegralMixedPrefixSnapshot.ofState x=d) (v : ℕ→ℝ) (hv : d.Realizes v) :
    IntegralMixedIntegerRealization.Realizes x v :=
  (congrArg (fun a : IntegralMixedPrefixSnapshot.Data=>a.Realizes v) he).mpr hv

private theorem align_interpretation {n S B m : ℕ} {Q : SpatialSource n} {ι : Type}
    (x : State Q S B m ι) (hm : m≤S) (r : IntegralMixedCriticalSweep.Rule n)
    (k : IntegralMixedRelativeCuts.Kind Q r) (d : ℕ) (values : ℕ→ℝ) (a : ℝ) (hx : Canonical x)
    (hroot : ∃φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i.val)∧
      IntegralMixedRelativeCuts.Valid x hm r φ k∧
      ((IntegralMixedRelativeCuts.factor x hm r k).map φ.toRingHom).natDegree=d∧
      (IntegralMixedRelativeCuts.factor x hm r k).eval₂ φ.toRingHom a=0)
    (ψ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hψ : ∀i,ψ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i.val) :
    IntegralMixedRelativeCuts.Valid x hm r ψ k∧
      ((IntegralMixedRelativeCuts.factor x hm r k).map ψ.toRingHom).natDegree=d∧
      (IntegralMixedRelativeCuts.factor x hm r k).eval₂ ψ.toRingHom a=0 := by
  obtain ⟨φ,hφ,hv,hd,hr⟩ := hroot
  have HE : φ=ψ := IntegralMixedBankValueInterpretation.hom_ext x hx φ ψ
    (fun i=>(hφ i).trans (hψ i).symm)
  subst φ
  exact ⟨hv,hd,hr⟩

private theorem selected_eval (p : Parameters) (d : Plan p)
    (h : IntegralMixedFramedHistoryFamilyBits.Data p d) (par : List Bool→List Bool) (q : List Bool)
    (φ : ((family p d h).state (IntegralMixedVirtualTaskBits.saved p (par q))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (t : ℝ) : (IntegralMixedFramedFullCutIntervalSelected.factor p d h par q φ).eval t=
      (IntegralMixedRelativeCuts.factor ((family p d h).state (IntegralMixedVirtualTaskBits.saved p (par q)))
        ((family p d h).birth_bound _) ((family p d h).rule _) ((family p d h).kind _)).eval₂ φ.toRingHom t := by
  simp only [IntegralMixedFramedFullCutIntervalSelected.factor,Polynomial.eval_map]
  rfl

private theorem commands_shape (p : Parameters) (d : Plan p) (r : List Bool)
    (cs : List (IntegralMixedFramedHistoryScript.Instruction (p.ambient r) (p.width r)))
    (hc : cs.length≤p.cap r+1+1) :
    let a:=IntegralMixedPrefixSnapshot.ofCommands (initial p d r) cs hc
    a.ambient=p.ambient r∧a.width=p.width r∧a.source.degree=p.degree r :=
  ⟨rfl,rfl,d.initial_degree r⟩

private theorem field_from_points (E : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents E.parameters E.plan E.data T)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input E) c w)
    (v : ℕ→ℝ)
    (hp : ∀i : Fin ((family E.parameters E.plan E.data).birth (E.key c)),
      IntegralFramedPhysicalSquare.point E.parameters E.plan E.data E.nodes E.factor E.seed E.bounds
        E.key E.positive c w hw i=v i.val)
    (i : ℕ) (hi : i<(family E.parameters E.plan E.data).birth (E.key c)) :
    IntegralFramedPhysicalBankTerm.env E T hr c w hw i=
      v ((family E.parameters E.plan E.data).birth (E.key c)-1-i) :=
  (IntegralFramedPhysicalBankTerm.env_chronological E T hr c w hw i hi).trans (hp _)

private theorem padded_old (v : ℕ→ℝ) (m i : ℕ) (hi : i<m) :
    IntegralFramedPaddedCutVertex.values v (m-i)=v (m-1-i) := by
  have H0 : m-i≠0 := by omega
  have HE : m-i-1=m-1-i := by omega
  simp only [IntegralFramedPaddedCutVertex.values,H0,ite_false,HE]

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => IntegralFramedBankQuery.Bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank
local notation "D" => IntegralFramedBankQuery.Bank.plan FormulaSignSlotRadialProviderRecordPlan.bank
local notation "H" => IntegralFramedBankQuery.Bank.data FormulaSignSlotRadialProviderRecordPlan.bank
local notation "G" => family P D H
local notation "S" => FormulaSignSlotRadialProviderAtomic.input
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
local notation "ctx" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "IC" => FormulaSignSlotRadialProviderBadProbeTest.intervalContext
local notation "dim" => FormulaSignSlotRadialProviderBadProbeTest.dimension
local notation "ini" => FormulaSignSlotRadialProviderBadProbeTest.initial
local notation "wid" => FormulaSignSlotRadialProviderBadProbeTest.width
local notation "new" => FormulaSignSlotRadialProviderBadProbeProvenance.prepared
local notation "birth" => FormulaSignSlotRadialProviderBadProbeProvenance.birth
local notation "saved" => FormulaSignSlotRadialProviderBadProbeProvenance.saved
local notation "parent" => FormulaSignSlotRadialProviderCutInterval.parent
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedIntegerRealization.Realizes
  IntegralMixedPrefixSnapshot.Data.Realizes

variable (z : List Bool)
  (hh : IntegralMixedRoadmapBadProbePacket.HintGood (dim z) (ini z) (wid z) z)
  (hl : SquareSampleCompleteVertices.Valid S (ctx (root (pairFst z))) (word (pairFst z)))
local notation "VL" => FormulaSignSlotRadialProviderBadProbeParent.values (root (pairFst z)) (word (pairFst z)) hl

include hh in
theorem parent_realizes : IntegralMixedIntegerRealization.Realizes ((G).state (saved z)) VL := by
  have HS : IntegralMixedPrefixSnapshot.ofState ((G).state (saved z))=
      FormulaSignSlotRadialProviderBadProbeParent.snapshot (root (pairFst z)) :=
    (FormulaSignSlotRadialProviderBadProbeProvenance.snapshot_saved z hh).trans
      (FormulaSignSlotRadialProviderBadProbeParent.snapshot_prepared (dim z) z hh.1).symm
  exact realizes_from_snapshot _ _ HS VL
    (FormulaSignSlotRadialProviderBadProbeParent.realizes (root (pairFst z)) (word (pairFst z)) hl)

section
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  FormulaSignSlotRadialProviderCutInterval.parent FormulaSignSlotRadialProviderCutInterval.endpoint
  FormulaSignSlotRadialProviderCutInterval.Bounds FormulaSignSlotRadialProviderCutInterval.IntervalGenerators
  FormulaSignSlotRadialProviderCutInterval.sign FormulaSignSlotRadialProviderCutInterval.head
  FormulaSignSlotRadialProviderCutInterval.choice FormulaSignSlotRadialProviderCutInterval.degree
  FormulaSignSlotRadialProviderCutInterval.cap FormulaSignSlotRadialProviderCutInterval.language
  FormulaSignSlotRadialProviderCutInterval.comparison IntegralMixedRelativeCuts.Valid
  IntegralMixedRelativeCuts.CoefficientGuards IntegralMixedFramedFullCutIntervalSelected.factor

variable (w : List Bool) (hw : SquareSampleCompleteVertices.Valid S (IC z) w)
local notation "old" => IntegralMixedVirtualTaskBits.saved P (parent (IC z))
local notation "values" => FormulaSignSlotRadialProviderBadProbeParent.values (new z) w
  (FormulaSignSlotRadialProviderNoBadSemantics.prepared_valid z w hw)
local notation "HB" => FormulaSignSlotRadialProviderBadProbeBounds.bounds z hh w
local notation "EP" => (fun side=>FormulaSignSlotRadialProviderCutInterval.endpoint side (IC z) w hw)

include hh in
theorem root_acceptance (a : ℝ)
    (ha : a∈Set.Ioo (EP false (FormulaSignSlotRadialProviderCutInterval.left_bound (IC z) w HB))
      (EP true (FormulaSignSlotRadialProviderCutInterval.right_bound (IC z) w HB)))
    (hroot : (IntegralMixedCutCreationReceipt.native P D H old).HasRoot values a) :
    FormulaSignSlotRadialProviderCutInterval.Guards (pair (IC z) w)∧
      pair (IC z) w∉FormulaSignSlotRadialProviderCutInterval.language := by
  have HP := FormulaSignSlotRadialProviderCutInterval.interval_coefficient_evaluation (IC z) w hw HB
  let ψ := Classical.choose HP
  have hψ := (Classical.choose_spec HP).1
  have HQ := FormulaSignSlotRadialProviderNoBadSemantics.interval_quotients z w hh hw ψ hψ
  have HR := (IntegralMixedCutCreationReceipt.native_root_iff P D H old values a).mp hroot
  have HV := align_interpretation ((G).state old) ((G).birth_bound old) ((G).rule old) ((G).kind old)
    ((G).degree old) values a (family_canonical P D H old) HR ψ HQ
  have HC := (IntegralMixedRelativeCuts.coefficientGuards_iff_valid_degree ((G).state old)
    ((G).birth_bound old) ((G).rule old) ψ ((G).kind old) ((G).degree old)).mpr ⟨HV.1,HV.2.1⟩
  have HG := (FormulaSignSlotRadialProviderCutInterval.interval_guards_iff_coefficients (IC z) w hw HB ψ hψ).mpr HC
  refine ⟨HG,?_⟩
  intro HEmpty
  have HM := (FormulaSignSlotRadialProviderCutInterval.language_iff_comparison (IC z) w hw HB HG).mp HEmpty
  have HI := FormulaSignSlotRadialProviderCutInterval.comparison_iff_no_root (IC z) w hw HB ψ hψ HC (ha.1.trans ha.2)
  exact (HI.mp HM.1 a ((selected_eval P D H parent (IC z) ψ a).trans HV.2.2)) ha
end

private theorem snapshot_shape (r : List Bool) :
    (FormulaSignSlotRadialProviderBadProbeParent.snapshot r).ambient=(P).ambient r∧
    (FormulaSignSlotRadialProviderBadProbeParent.snapshot r).width=(P).width r∧
    (FormulaSignSlotRadialProviderBadProbeParent.snapshot r).source.degree=(P).degree r := by
  unfold FormulaSignSlotRadialProviderBadProbeParent.snapshot FormulaSignSlotRadialProviderRecordPrefix.snapshot
  exact commands_shape P D r _ _

private theorem snapshot_cap (r : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap
      ((FormulaSignSlotRadialProviderBadProbeParent.snapshot r).ambient+1)
      (FormulaSignSlotRadialProviderBadProbeParent.snapshot r).source.degree≤
      2^(FormulaSignSlotRadialProviderBadProbeParent.snapshot r).width := by
  have HS := snapshot_shape r
  rw [HS.2.2,HS.1,HS.2.1]
  exact (D).scalar_cap r

include hh in
private theorem decoded_degree_cap
    (hd : Nat.fromBitsLE (field 3 z)≤IntegralMixedExceptionalBounds.auxiliaryCap
      ((FormulaSignSlotRadialProviderBadProbeParent.snapshot (root (pairFst z))).ambient+1)
      (FormulaSignSlotRadialProviderBadProbeParent.snapshot (root (pairFst z))).source.degree) :
    Nat.fromBitsLE (field 3 z)≤IntegralMixedExceptionalBounds.auxiliaryCap
      ((P).ambient (pairFst (saved z))+1) ((P).degree (pairFst (saved z))) := by
  have HE := congrArg (fun a : IntegralMixedPrefixSnapshot.Data=>
    IntegralMixedExceptionalBounds.auxiliaryCap (a.ambient+1) a.source.degree)
    (FormulaSignSlotRadialProviderBadProbeParent.snapshot_prepared (dim z) z hh.1)
  have HN : Nat.fromBitsLE (field 3 z)≤IntegralMixedExceptionalBounds.auxiliaryCap
      ((FormulaSignSlotRadialProviderBadProbeParent.snapshot (new z)).ambient+1)
      (FormulaSignSlotRadialProviderBadProbeParent.snapshot (new z)).source.degree := hd.trans_eq HE
  have HS := snapshot_shape (new z)
  rw [HS.2.2,HS.1] at HN
  rw [FormulaSignSlotRadialProviderBadProbeProvenance.saved_root z hh]
  exact HN

attribute [local irreducible] IntegralFramedPhysicalSquare.input IntegralFramedPhysicalSquare.point

include hh hl in
theorem exists_vertex
    (hd : Nat.fromBitsLE (field 3 z)≤IntegralMixedExceptionalBounds.auxiliaryCap
      ((FormulaSignSlotRadialProviderBadProbeParent.snapshot (root (pairFst z))).ambient+1)
      (FormulaSignSlotRadialProviderBadProbeParent.snapshot (root (pairFst z))).source.degree) :
    ∃w,∃hw : SquareSampleCompleteVertices.Valid S (ctx (new z)) w,
      w.length=SquareSampleCompleteVertices.width S (ctx (new z))∧
      ∀i : Fin ((G).birth ((B).key (ctx (new z)))),
        IntegralFramedPhysicalSquare.point P D H (B).nodes (B).factor (B).seed (B).bounds
          (B).key (B).positive (ctx (new z)) w hw i=IntegralFramedPaddedCutVertex.values VL i.val := by
  let d : IntegralMixedCutRecordConstructor.Data ((P).ambient (pairFst (saved z)))
      (N (pairFst (saved z))+(prefixCodes (pairFst z)).length) :=
    FormulaSignSlotRadialProviderBadProbeProvenance.data z hh
  let tag := IntegralMixedChronologicalCutCode.ordinaryTag (Nat.fromBitsLE (field 0 z))
  have HT : IntegralMixedCausalRecordPlanBits.records (pairFst (saved z))=WordList.encode
      (prefixCodes (pairFst z)++[d.code tag (Nat.fromBitsLE (field 2 z)) (Nat.fromBitsLE (field 3 z))]) :=
    FormulaSignSlotRadialProviderBadProbeProvenance.records_saved z hh
  have HP : prefixLength P (saved z)=N (pairFst (saved z))+(prefixCodes (pairFst z)).length :=
    FormulaSignSlotRadialProviderBadProbeProvenance.saved_prefix z hh
  have HR := FormulaSignSlotRadialProviderReservedCutRealization.run_realizes (saved z) (prefixCodes (pairFst z))
    d tag (Nat.fromBitsLE (field 2 z)) (Nat.fromBitsLE (field 3 z)) (decoded_degree_cap z hh hd) HT HP VL
    (parent_realizes z hh hl)
  have HL := FormulaSignSlotRadialProviderReservedCutRealization.rules_length (saved z) (prefixCodes (pairFst z))
    (d.code tag (Nat.fromBitsLE (field 2 z)) (Nat.fromBitsLE (field 3 z))) HT
  have HLen : ((D).rules (pairFst (saved z))).length=FormulaSignSlotRadialProviderRecordPlan.fullCount (new z) :=
    HL.trans ((congrArg (fun m=>m+1) (FormulaSignSlotRadialProviderBadProbeProvenance.creating_saved z hh)).symm.trans
      (FormulaSignSlotRadialProviderBadProbeProvenance.last_birth z hh))
  have HK : pairFst ((B).key (ctx (new z)))=pairFst (saved z) :=
    (FormulaSignSlotRadialProviderRecordPrefix.key_root (new z)).trans
      (FormulaSignSlotRadialProviderBadProbeProvenance.saved_root z hh).symm
  have HF : prefixLength P ((B).key (ctx (new z)))=((D).rules (pairFst (saved z))).length :=
    (FormulaSignSlotRadialProviderRecordPrefix.full_prefix (new z)).trans HLen.symm
  exact IntegralMixedReservedCutActualVertex.vertex_from_full_run P D H (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive (ctx (new z)) (pairFst (saved z)) HK HF _ HR

attribute [local irreducible] IntegralFramedPhysicalBankTerm.env

include hh in
private theorem original_birth :
    (FormulaSignSlotRadialProviderBadProbeParent.snapshot (root (pairFst z))).birth=birth z := by
  rw [FormulaSignSlotRadialProviderBadProbeParent.birth,FormulaSignSlotRadialProviderBadProbePrefix.root_count]
  change N (root (pairFst z))+(count (pairFst z)-1)=IntegralMixedRoadmapBadProbePacket.creating (ini z) (pairFst z)
  rw [FormulaSignSlotRadialProviderBadProbeProvenance.initial_eq z]
  unfold IntegralMixedRoadmapBadProbePacket.creating
  have HC := hh.1
  omega

private theorem parent_field (r w : List Bool) (hw : SquareSampleCompleteVertices.Valid S (ctx r) w)
    (i : ℕ) (hi : i<(FormulaSignSlotRadialProviderBadProbeParent.snapshot r).birth) :
    FormulaSignSlotRadialProviderBadProbeParent.values r w hw i=
      FormulaSignSlotRadialProviderAtomic.bankField (ctx r) w hw
        ((FormulaSignSlotRadialProviderBadProbeParent.snapshot r).birth-1-i) :=
  (FormulaSignSlotRadialProviderBadProbeParent.value_field r w hw i hi).trans
    (congrArg (FormulaSignSlotRadialProviderAtomic.bankField (ctx r) w hw)
      (congrArg (fun m=>m-1-i) (FormulaSignSlotRadialProviderBadProbeParent.birth r)).symm)

include hh in
private theorem original_field (i : ℕ) (hi : i<birth z) :
    VL (birth z-1-i)=FormulaSignSlotRadialProviderAtomic.bankField (ctx (root (pairFst z)))
      (word (pairFst z)) hl i := by
  have HI : birth z-1-i<birth z := by omega
  have HField := parent_field (root (pairFst z)) (word (pairFst z)) hl (birth z-1-i)
    (HI.trans_eq (original_birth z hh).symm)
  rw [original_birth z hh] at HField
  exact HField.trans (congrArg (FormulaSignSlotRadialProviderAtomic.bankField (ctx (root (pairFst z)))
    (word (pairFst z)) hl) (by omega))

include hh hl in
theorem exists_fields
    (hd : Nat.fromBitsLE (field 3 z)≤IntegralMixedExceptionalBounds.auxiliaryCap
      ((FormulaSignSlotRadialProviderBadProbeParent.snapshot (root (pairFst z))).ambient+1)
      (FormulaSignSlotRadialProviderBadProbeParent.snapshot (root (pairFst z))).source.degree) :
    ∃w,∃hw : SquareSampleCompleteVertices.Valid S (ctx (new z)) w,
      w.length=SquareSampleCompleteVertices.width S (ctx (new z))∧
      ∀i<birth z,FormulaSignSlotRadialProviderAtomic.bankField (ctx (root (pairFst z)))
        (word (pairFst z)) hl i=FormulaSignSlotRadialProviderAtomic.bankField (ctx (new z)) w hw i := by
  have HV := exists_vertex z hh hl hd
  obtain ⟨w,hw,hlen,hpoints⟩ := HV
  have HBirth : (G).birth ((B).key (ctx (new z)))=birth z+1 :=
    (family_birth P D H _).trans ((FormulaSignSlotRadialProviderRecordPrefix.full_prefix (new z)).trans
      (FormulaSignSlotRadialProviderBadProbeProvenance.last_birth z hh).symm)
  refine ⟨w,hw,hlen,fun i hi=>?_⟩
  have HE := field_from_points B FormulaSignSlotRadialProviderRecordPlan.tables
    FormulaSignSlotRadialProviderAtomic.bank_represents (ctx (new z)) w hw
    (IntegralFramedPaddedCutVertex.values VL) hpoints i (by rw [HBirth];omega)
  have HSlot : (G).birth ((B).key (ctx (new z)))-1-i=birth z-i := by omega
  rw [HSlot,padded_old VL (birth z) i hi] at HE
  exact (original_field z hh hl i hi).symm.trans HE.symm

private theorem append_package :
    (⟨FormulaSignSlotRadialProviderBadProbeCommand.appendPlan,
      FormulaSignSlotRadialProviderBadProbeCommand.appendData⟩ :
      (d : Plan P)×IntegralMixedFramedHistoryFamilyBits.Data P d)=⟨D,H⟩ := rfl

include hh in
private theorem native_root_saved (values : ℕ→ℝ) (a : ℝ)
    (hcoded : (IntegralMixedPrefixSnapshot.ofState ((G).state (saved z))).CodedFactor
      (labels (pairFst z)) values a (probe (dim z) z)) :
    (IntegralMixedCutCreationReceipt.native P D H (saved z)).HasRoot values a := by
  have HT : IntegralMixedCausalRecordPlanBits.records (pairFst (saved z))=
      WordList.encode (prefixCodes (pairFst z)++[probe (dim z) z]) :=
    (congrArg IntegralMixedCausalRecordPlanBits.records
      (FormulaSignSlotRadialProviderBadProbeProvenance.saved_root z hh)).trans
      (FormulaSignSlotRadialProviderBadProbeProvenance.records z)
  have HP := IntegralMixedSourceIntegerCutReceipt.native_root P
    (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial r)
    FormulaSignSlotRadialProviderRecordPlan.positive
    (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial_degree r)
    FormulaSignSlotRadialProviderRecordPlan.spatial_cap N
    FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.source_nonzero
    FormulaSignSlotRadialProviderRecordPlan.source_degree_cap FormulaSignSlotRadialProviderRecordPlan.room
    FormulaSignSlotRadialProviderBadProbeCommand.appendData (saved z) (prefixCodes (pairFst z))
    (probe (dim z) z) (labels (pairFst z)) values a HT
    (FormulaSignSlotRadialProviderBadProbeProvenance.saved_prefix z hh)
  have HE := congrArg (fun dh : (d : Plan P)×IntegralMixedFramedHistoryFamilyBits.Data P d=>
    (IntegralMixedPrefixSnapshot.ofState ((family P dh.1 dh.2).state (saved z))).CodedFactor
      (labels (pairFst z)) values a (probe (dim z) z)→
    (IntegralMixedCutCreationReceipt.native P dh.1 dh.2 (saved z)).HasRoot values a) append_package
  exact (HE.mp HP) hcoded

include hh in
private theorem values_eq_of_fields (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid S (ctx (new z)) w)
    (hf : ∀i<birth z,FormulaSignSlotRadialProviderAtomic.bankField (ctx (root (pairFst z)))
      (word (pairFst z)) hl i=FormulaSignSlotRadialProviderAtomic.bankField (ctx (new z)) w hw i) :
    ∀i<(FormulaSignSlotRadialProviderBadProbeParent.snapshot (root (pairFst z))).birth,
      VL i=FormulaSignSlotRadialProviderBadProbeParent.values (new z) w hw i := by
  have HO := original_birth z hh
  have HE := FormulaSignSlotRadialProviderBadProbeParent.snapshot_prepared (dim z) z hh.1
  have HN : (FormulaSignSlotRadialProviderBadProbeParent.snapshot (new z)).birth=birth z :=
    (congrArg IntegralMixedPrefixSnapshot.Data.birth HE).symm.trans HO
  intro i hi
  have HR : i<(FormulaSignSlotRadialProviderBadProbeParent.snapshot (new z)).birth :=
    hi.trans_eq (congrArg IntegralMixedPrefixSnapshot.Data.birth HE)
  have HLeft := parent_field (root (pairFst z)) (word (pairFst z)) hl i hi
  have HRight := parent_field (new z) w hw i HR
  rw [HO] at HLeft
  rw [HN] at HRight
  exact HLeft.trans ((hf _ (by have HI:=hi.trans_eq HO;omega)).trans HRight.symm)

include hh hl in
theorem at_hint (a : ℝ)
    (hcoded : (FormulaSignSlotRadialProviderBadProbeParent.snapshot (root (pairFst z))).CodedFactor
      (labels (pairFst z)) VL a (probe (dim z) z))
    (hd : Nat.fromBitsLE (field 3 z)≤IntegralMixedExceptionalBounds.auxiliaryCap
      ((FormulaSignSlotRadialProviderBadProbeParent.snapshot (root (pairFst z))).ambient+1)
      (FormulaSignSlotRadialProviderBadProbeParent.snapshot (root (pairFst z))).source.degree)
    (ha : a∈Set.Ioo (FormulaSignSlotRadialProviderNoBadSemantics.endpoint (pairFst z) hl false)
      (FormulaSignSlotRadialProviderNoBadSemantics.endpoint (pairFst z) hl true)) :
    ∃w,FormulaSignSlotRadialProviderBadProbeTest.Witness (pair z w) := by
  obtain ⟨w,hw,_,HF⟩ := exists_fields z hh hl hd
  let v := FormulaSignSlotRadialProviderBadProbeParent.values (new z) w hw
  have HS : FormulaSignSlotRadialProviderBadProbeParent.snapshot (root (pairFst z))=
      IntegralMixedPrefixSnapshot.ofState ((G).state (saved z)) :=
    (FormulaSignSlotRadialProviderBadProbeParent.snapshot_prepared (dim z) z hh.1).trans
      (FormulaSignSlotRadialProviderBadProbeProvenance.snapshot_saved z hh).symm
  have HC := (IntegralMixedPrefixSnapshot.Data.coded_transport _ _ HS (labels (pairFst z)) VL v a
    (probe (dim z) z) (values_eq_of_fields z hh hl w hw HF)).mp hcoded
  have HR := native_root_saved z hh v a HC
  have HV : SquareSampleCompleteVertices.Valid S (IC z) w :=
    (FormulaSignSlotRadialProviderBankContext.valid_iff (ctx (new z)) (IC z) w
      ((pairFst_pair _ _).trans (FormulaSignSlotRadialProviderBadProbeProvenance.context_root z).symm)).mp hw
  have HFields := (FormulaSignSlotRadialProviderBadProbeFields.packet_iff (dim z) (ini z) z w hh.1
    (FormulaSignSlotRadialProviderBadProbeProvenance.initial_eq z) hl hw).mpr HF
  have HE := FormulaSignSlotRadialProviderNoBadSemantics.endpoint_eq z w hh HV hl HFields
  have HB := FormulaSignSlotRadialProviderBadProbeBounds.bounds z hh w
  have HA : a∈Set.Ioo
      (FormulaSignSlotRadialProviderCutInterval.endpoint false (IC z) w HV
        (FormulaSignSlotRadialProviderCutInterval.left_bound (IC z) w HB))
      (FormulaSignSlotRadialProviderCutInterval.endpoint true (IC z) w HV
        (FormulaSignSlotRadialProviderCutInterval.right_bound (IC z) w HB)) := by
    rw [HE false,HE true]
    exact ha
  have HK : IntegralMixedVirtualTaskBits.saved P (parent (IC z))=saved z :=
    FormulaSignSlotRadialProviderBadProbeProvenance.context_saved z
  have HRoot : (IntegralMixedCutCreationReceipt.native P D H
      (IntegralMixedVirtualTaskBits.saved P (parent (IC z)))).HasRoot v a :=
    (congrArg (fun d : IntegralMixedCutCreationReceipt.Data=>d.HasRoot v a)
      (congrArg (IntegralMixedCutCreationReceipt.native P D H) HK)).mpr HR
  obtain ⟨HG,HN⟩ := root_acceptance z hh w HV a HA HRoot
  refine ⟨w,(FormulaSignSlotRadialProviderBadProbeBounds.witness_iff z w).mpr ⟨hh,?_,HV,?_,?_⟩⟩
  · simpa only [FormulaSignSlotRadialProviderBadProbeTest.fieldPacket,
      FormulaSignSlotRadialProviderBadProbeFields.packet,FormulaSignSlotRadialProviderRecordPrefix.context,
      pairFst_pair,pairSnd_pair] using HFields
  · simpa only [FormulaSignSlotRadialProviderBadProbeTest.intervalPacket,pairFst_pair,pairSnd_pair] using HG
  · simpa only [FormulaSignSlotRadialProviderBadProbeTest.intervalPacket,pairFst_pair,pairSnd_pair] using HN

include hh in
theorem at_hint_base (base : List Bool) (hb : pairFst z=base)
    (hbase : SquareSampleCompleteVertices.Valid S (ctx (root base)) (word base)) (a : ℝ)
    (hcoded : (FormulaSignSlotRadialProviderBadProbeParent.snapshot (root base)).CodedFactor
      (labels base) (FormulaSignSlotRadialProviderBadProbeParent.values (root base) (word base) hbase)
      a (probe (dim z) z))
    (hd : Nat.fromBitsLE (field 3 z)≤IntegralMixedExceptionalBounds.auxiliaryCap
      ((FormulaSignSlotRadialProviderBadProbeParent.snapshot (root base)).ambient+1)
      (FormulaSignSlotRadialProviderBadProbeParent.snapshot (root base)).source.degree)
    (ha : a∈Set.Ioo (FormulaSignSlotRadialProviderNoBadSemantics.endpoint base hbase false)
      (FormulaSignSlotRadialProviderNoBadSemantics.endpoint base hbase true)) :
    ∃w,FormulaSignSlotRadialProviderBadProbeTest.Witness (pair z w) := by
  subst base
  exact at_hint z hh hbase a hcoded hd ha

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedPrefixSnapshot.Data.CodedFactor FormulaSignSlotRadialProviderBadProbeParent.snapshot
  FormulaSignSlotRadialProviderBadProbeParent.values FormulaSignSlotRadialProviderBadProbeParent.bad
  FormulaSignSlotRadialProviderBadProbeTest.Witness

theorem complete (base : List Bool)
    (hbase : SquareSampleCompleteVertices.Valid S (ctx (root base)) (word base))
    (hc : 0<count base)
    (hp : ∀side,IntegralMixedRoadmapBadProbePacket.producer side base<
      (FormulaSignSlotRadialProviderBadProbeParent.snapshot (root base)).birth)
    (hbad : ∃a∈Set.Ioo (FormulaSignSlotRadialProviderNoBadSemantics.endpoint base hbase false)
        (FormulaSignSlotRadialProviderNoBadSemantics.endpoint base hbase true),
      a∈FormulaSignSlotRadialProviderBadProbeParent.bad (root base) (word base) (labels base) hbase) :
    ∃hint w,FormulaSignSlotRadialProviderBadProbeTest.Witness (pair (pair base hint) w) := by
  obtain ⟨a,ha,hbad0⟩ := hbad
  let d := FormulaSignSlotRadialProviderBadProbeParent.snapshot (root base)
  let v := FormulaSignSlotRadialProviderBadProbeParent.values (root base) (word base) hbase
  unfold FormulaSignSlotRadialProviderBadProbeParent.bad at hbad0
  change a∈d.bad (labels base) v at hbad0
  obtain ⟨code,HC⟩ := (IntegralMixedPrefixSnapshot.Data.mem_bad_iff_coded d (labels base) v
    (FormulaSignSlotRadialProviderBadProbeParent.canonical (root base)) a).mp hbad0
  have HB : d.birth=IntegralMixedRoadmapBadProbePacket.creating (N (root base)) base := by
    dsimp only [d]
    rw [FormulaSignSlotRadialProviderBadProbeParent.birth,FormulaSignSlotRadialProviderBadProbePrefix.root_count]
    unfold IntegralMixedRoadmapBadProbePacket.creating
    omega
  obtain ⟨hint,HGood,HCode,HDegree⟩ := IntegralMixedPrefixSnapshot.Data.coded_hint d base v a code
    (N (root base)) hc HB (hp false) (hp true) (snapshot_cap (root base)) HC
  let z0 := pair base hint
  have HN : dim z0=d.ambient := by
    simpa only [FormulaSignSlotRadialProviderBadProbeTest.dimension,z0,pairFst_pair]
      using (snapshot_shape (root base)).1.symm
  have HW : wid z0=d.width := by
    simpa only [FormulaSignSlotRadialProviderBadProbeTest.width,z0,pairFst_pair]
      using (snapshot_shape (root base)).2.1.symm
  have HI : ini z0=N (root base) := by
    simpa only [z0,pairFst_pair] using FormulaSignSlotRadialProviderBadProbeProvenance.initial_eq z0
  have HH : IntegralMixedRoadmapBadProbePacket.HintGood (dim z0) (ini z0) (wid z0) z0 := by
    rw [HN,HI,HW]
    exact HGood
  have HE : probe (dim z0) z0=code := (congrArg (fun n=>probe n z0) HN).trans HCode
  have HC0 : d.CodedFactor (labels base) v a (probe (dim z0) z0) :=
    (congrArg (fun bits=>d.CodedFactor (labels base) v a bits) HE).mpr HC
  obtain ⟨w,HW0⟩ := at_hint_base z0 HH base (pairFst_pair _ _) hbase a HC0 HDegree ha
  exact ⟨hint,w,HW0⟩

theorem hasBadProbe_iff (base : List Bool)
    (hbase : SquareSampleCompleteVertices.Valid S (ctx (root base)) (word base))
    (hc : 0<count base)
    (hp : ∀side,IntegralMixedRoadmapBadProbePacket.producer side base<
      (FormulaSignSlotRadialProviderBadProbeParent.snapshot (root base)).birth)
    (hab : FormulaSignSlotRadialProviderNoBadSemantics.endpoint base hbase false<
      FormulaSignSlotRadialProviderNoBadSemantics.endpoint base hbase true) :
    FormulaSignSlotRadialProviderBadProbeSearch.HasBadProbe base↔
      ∃a∈Set.Ioo (FormulaSignSlotRadialProviderNoBadSemantics.endpoint base hbase false)
        (FormulaSignSlotRadialProviderNoBadSemantics.endpoint base hbase true),
        a∈FormulaSignSlotRadialProviderBadProbeParent.bad (root base) (word base) (labels base) hbase := by
  rw [FormulaSignSlotRadialProviderBadProbeSearch.hasBadProbe_iff base]
  constructor
  · rintro ⟨hint,hhint⟩
    obtain ⟨w,hW⟩ := (FormulaSignSlotRadialProviderBadProbeTest.hasWitness_iff (pair base hint)).mp hhint
    have HL0 : SquareSampleCompleteVertices.Valid S (ctx (root (pairFst (pair base hint))))
        (word (pairFst (pair base hint))) := by simpa only [pairFst_pair] using hbase
    have HO : FormulaSignSlotRadialProviderNoBadSemantics.endpoint (pairFst (pair base hint)) HL0 false<
        FormulaSignSlotRadialProviderNoBadSemantics.endpoint (pairFst (pair base hint)) HL0 true := by
      simpa only [pairFst_pair] using hab
    simpa only [pairFst_pair] using FormulaSignSlotRadialProviderNoBadSemantics.ordinary_bad
      (pair base hint) w HL0 hW HO
  · intro hbad
    obtain ⟨hint,w,hW⟩ := complete base hbase hc hp hbad
    exact ⟨hint,(FormulaSignSlotRadialProviderBadProbeTest.hasWitness_iff (pair base hint)).mpr ⟨w,hW⟩⟩

theorem noBadProbe_iff (base : List Bool)
    (hbase : SquareSampleCompleteVertices.Valid S (ctx (root base)) (word base))
    (hc : 0<count base)
    (hp : ∀side,IntegralMixedRoadmapBadProbePacket.producer side base<
      (FormulaSignSlotRadialProviderBadProbeParent.snapshot (root base)).birth)
    (hab : FormulaSignSlotRadialProviderNoBadSemantics.endpoint base hbase false<
      FormulaSignSlotRadialProviderNoBadSemantics.endpoint base hbase true) :
    FormulaSignSlotRadialProviderBadProbeSearch.NoBadProbe base↔
      ∀a,a∈Set.Ioo (FormulaSignSlotRadialProviderNoBadSemantics.endpoint base hbase false)
        (FormulaSignSlotRadialProviderNoBadSemantics.endpoint base hbase true)→
        a∉FormulaSignSlotRadialProviderBadProbeParent.bad (root base) (word base) (labels base) hbase := by
  rw [FormulaSignSlotRadialProviderBadProbeSearch.NoBadProbe,hasBadProbe_iff base hbase hc hp hab]
  simp only [not_exists,not_and]

end LeanCanny.Encoding.FormulaSignSlotRadialProviderNoBadComplete

namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProper
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedRoadmapProper (badPacket producer labels)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S" => FormulaSignSlotRadialProviderAtomic.input
local notation "ctx" => FormulaSignSlotRadialProviderRecordPrefix.context

private theorem bad_root (q : List Bool) : IntegralMixedRoadmapBadProbePacket.root (badPacket q)=FormulaSignSlotRadialProviderAtomic.root q := by
  simp only [IntegralMixedRoadmapBadProbePacket.root,IntegralMixedRoadmapBadProbePacket.candidate,IntegralMixedRoadmapBadProbePacket.raw,badPacket,IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair,pairSnd_pair,
    FormulaSignSlotRadialProviderAtomic.root,FormulaSignSlotRadialProviderAtomic.provider,FormulaSignSlotRadialProviderAtomic.payload,FormulaSignSlotRadialProviderRecordPlan.root,
    IntegralMixedRoadmapAtomic.candidate,IntegralMixedRoadmapAtomic.payload]
private theorem bad_word (q : List Bool) : IntegralMixedRoadmapBadProbePacket.word (badPacket q)=FormulaSignSlotRadialProviderAtomic.word q := by
  simp only [IntegralMixedRoadmapBadProbePacket.word,badPacket,IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair,pairSnd_pair,FormulaSignSlotRadialProviderAtomic.word,IntegralMixedRoadmapAtomic.word]
private theorem bad_labels (q : List Bool) : IntegralMixedRoadmapBadProbePacket.labels (badPacket q)=labels q := by
  simp only [IntegralMixedRoadmapBadProbePacket.labels,badPacket,IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair,pairSnd_pair]
private theorem bad_producer (q : List Bool) (side : Bool) : IntegralMixedRoadmapBadProbePacket.producer side (badPacket q)=producer side q := by
  cases side <;> simp only [IntegralMixedRoadmapBadProbePacket.producer,IntegralMixedRoadmapBadProbePacket.endpoints,badPacket,IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair,pairSnd_pair,
    Bool.false_eq_true,ite_false,ite_true,BinaryNatCode.encode,Nat.fromBitsLE_bits]
private theorem bad_context (q : List Bool) : ctx (IntegralMixedRoadmapBadProbePacket.root (badPacket q))=FormulaSignSlotRadialProviderAtomic.context q :=
  congrArg (fun r=>pair r []) (bad_root q)

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralFramedPhysicalSquare.input IntegralFramedPhysicalBankTerm.env
  FormulaSignSlotRadialProviderAtomic.Valid FormulaSignSlotRadialProviderAtomic.field
  FormulaSignSlotRadialProviderBadProbeParent.snapshot FormulaSignSlotRadialProviderBadProbeParent.bad

private theorem bank_field_congr (c d w v : List Bool) (hc : c=d) (hw : w=v)
    (hL : SquareSampleCompleteVertices.Valid S c w) (hR : SquareSampleCompleteVertices.Valid S d v) (i : ℕ) :
    FormulaSignSlotRadialProviderAtomic.bankField c w hL i=FormulaSignSlotRadialProviderAtomic.bankField d v hR i := by
  subst d
  subst v
  rfl
private theorem bad_congr (r s w v l k : List Bool) (hr : r=s) (hw : w=v) (hl : l=k)
    (hL : SquareSampleCompleteVertices.Valid S (ctx r) w)
    (hR : SquareSampleCompleteVertices.Valid S (ctx s) v) :
    FormulaSignSlotRadialProviderBadProbeParent.bad r w l hL=
      FormulaSignSlotRadialProviderBadProbeParent.bad s v k hR := by
  subst s
  subst v
  subst k
  rfl

private theorem bad_valid (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    SquareSampleCompleteVertices.Valid S (ctx (IntegralMixedRoadmapBadProbePacket.root (badPacket q))) (IntegralMixedRoadmapBadProbePacket.word (badPacket q)) := by
  rw [bad_context,bad_word]
  exact FormulaSignSlotRadialProviderAtomic.full_valid q hv

private theorem bad_endpoint (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (side : Bool) :
    FormulaSignSlotRadialProviderNoBadSemantics.endpoint (badPacket q) (bad_valid q hv) side=
      FormulaSignSlotRadialProviderAtomic.field q hv (producer side q) := by
  unfold FormulaSignSlotRadialProviderNoBadSemantics.endpoint FormulaSignSlotRadialProviderAtomic.field
  exact (bank_field_congr _ _ _ _ (bad_context q) (bad_word q) (bad_valid q hv) (FormulaSignSlotRadialProviderAtomic.full_valid q hv) _).trans
    (congrArg (FormulaSignSlotRadialProviderAtomic.bankField (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv)) (bad_producer q side))

private theorem bad_producer_fit (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) (side : Bool) :
    IntegralMixedRoadmapBadProbePacket.producer side (badPacket q)<(FormulaSignSlotRadialProviderBadProbeParent.snapshot (IntegralMixedRoadmapBadProbePacket.root (badPacket q))).birth := by
  have HG := FormulaSignSlotRadialProviderProperCritical.midpoint_good q hv hd
  have HM := FormulaSignSlotRadialProviderProperCritical.midpoint_fit q hv hd
  rw [FormulaSignSlotRadialProviderAtomic.raw_count q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv)] at HM
  have HClock : IntegralMixedRoadmapProper.midBirth (FormulaSignSlotRadialProviderAtomic.dimension q) (FormulaSignSlotRadialProviderAtomic.initial q) q=
      FormulaSignSlotRadialProviderAtomic.initial q+IntegralMixedRoadmapProper.midRawIndex (FormulaSignSlotRadialProviderAtomic.dimension q) q := by
    simp only [IntegralMixedRoadmapProper.midBirth,IntegralMixedRoadmapProper.baseBirth,
      IntegralMixedRoadmapChain.birth,IntegralMixedRoadmapProper.midRawIndex,Nat.add_assoc]
  have HP : producer side q<IntegralMixedRoadmapProper.midBirth (FormulaSignSlotRadialProviderAtomic.dimension q) (FormulaSignSlotRadialProviderAtomic.initial q) q := by
    cases side
    · exact HG.2.1
    · exact HG.2.2.1
  rw [HClock] at HP
  have HC : IntegralMixedCausalRecordPlanBits.count (FormulaSignSlotRadialProviderAtomic.root q)=
      IntegralMixedRoadmapRecordChain.probedRecordBound (FormulaSignSlotRadialProviderAtomic.dimension q) := by
    unfold IntegralMixedCausalRecordPlanBits.count
    rw [FormulaSignSlotRadialProviderAtomic.root_records,FormulaSignSlotRadialProviderAtomic.raw_count q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv)]
  have HB : (FormulaSignSlotRadialProviderBadProbeParent.snapshot (IntegralMixedRoadmapBadProbePacket.root (badPacket q))).birth=
      FormulaSignSlotRadialProviderAtomic.initial q+(IntegralMixedRoadmapRecordChain.probedRecordBound (FormulaSignSlotRadialProviderAtomic.dimension q)-1) := by
    rw [bad_root,FormulaSignSlotRadialProviderBadProbeParent.birth,HC]
    rfl
  rw [bad_producer,HB]
  exact HP.trans_le (Nat.add_le_add_left (by omega) _)
noncomputable def OriginalBadFree (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) : Prop :=
  ∀a,a∈Set.Ioo (FormulaSignSlotRadialProviderAtomic.field q hv (producer false q)) (FormulaSignSlotRadialProviderAtomic.field q hv (producer true q))→
    a∉FormulaSignSlotRadialProviderBadProbeParent.bad (FormulaSignSlotRadialProviderAtomic.root q) (FormulaSignSlotRadialProviderAtomic.word q) (labels q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv)

theorem noBad_iff_original_bad_free (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q)
    (hab : FormulaSignSlotRadialProviderAtomic.field q hv (producer false q)<FormulaSignSlotRadialProviderAtomic.field q hv (producer true q)) :
    NoBad q↔OriginalBadFree q hv := by
  have HV := bad_valid q hv
  have HO : FormulaSignSlotRadialProviderNoBadSemantics.endpoint (badPacket q) HV false<
      FormulaSignSlotRadialProviderNoBadSemantics.endpoint (badPacket q) HV true := by
    rw [bad_endpoint q hv false,bad_endpoint q hv true]
    exact hab
  have HE := FormulaSignSlotRadialProviderNoBadComplete.noBadProbe_iff (badPacket q) HV
    (FormulaSignSlotRadialProviderProperCritical.count_positive q hv) (bad_producer_fit q hv hd) HO
  have HF := bad_congr _ _ _ _ _ _ (bad_root q) (bad_word q) (bad_labels q) HV (FormulaSignSlotRadialProviderAtomic.full_valid q hv)
  unfold NoBad OriginalBadFree
  simpa only [bad_endpoint q hv false,bad_endpoint q hv true,HF] using HE

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProper
