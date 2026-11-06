/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderLabelClosedGeometry
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderFirstSeedConstruct
public import LeanCanny.Connectivity.FormulaSignSlotCircularPoint
/-! # The native OLD-label comparison is exactly projected sample equality -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotProjectedSampleEquality
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open FormulaSignSlotRadialProviderLabelClosedGeometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "N" => CanonicalAuxiliaryCandidateCover.dimension
local notation "T" => CanonicalAuxiliaryCandidateCover.equation
local notation "hn" => CanonicalAuxiliaryCandidateCover.dimension_unary
local notation "ht" => CanonicalAuxiliaryCandidateCover.equation_FP
local notation "ha" => CanonicalAuxiliaryCandidateCover.equation_scope

noncomputable def Good (side : Bool) (H : List Bool) : Prop :=
  AuxiliaryCandidateComponentCover.Good hn ht ha (FormulaSignSlotRadialJointLayout.source side H)
    (LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.candidate side H)
theorem dimension_eq (side : Bool) (H : List Bool) :
    FormulaSignSlotSource.dimension (FormulaSignSlotRadialJointLayout.source side H) = LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.dimension H := by
  cases side
  · exact FormulaSignSlotRadialJointLayout.original_dimension_eq H
  · rfl
noncomputable def projectedSample (side : Bool) (H : List Bool) (hg : Good side H) :
    Fin (LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.dimension H) → ℝ :=
  fun i => (FormulaSignSlotCircularBoundedCover.projectedPoint (FormulaSignSlotRadialJointLayout.source side H)
    (sourceSample (FormulaSignSlotRadialJointLayout.source side H) (LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.candidate side H) hg)).val
      (Fin.cast (dimension_eq side H).symm i)

attribute [local irreducible] FormulaSignSlotCircularBoundedCover.root
  FormulaSignSlotCircularInterior.description FormulaSignSlotSource.dimension
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.kind
  Input.field FormulaView.normalize

private theorem circle_dimension (c : List Bool) : N c =
    BoundedMonotoneGateSource.total ClosedFormulaGateTruth.F (FormulaSignSlotCircularBoundedCover.root c) := rfl
private theorem homeomorph_coordinate (c : List Bool) (z : FormulaSignSlotCircularBoundedCover.Source c)
    (i : Fin (N c)) : ((CanonicalAuxiliaryCandidateCover.sourceHomeomorph c) z).val i =
      z.val (Fin.cast (circle_dimension c) i) := rfl
private theorem projected_index_val (c : List Bool) (i : Fin (FormulaSignSlotSource.dimension c)) :
    (FormulaSignSlotCircularBoundedCover.projectedIndex c i).val = i.val := rfl
attribute [local irreducible] CanonicalAuxiliaryCandidateCover.dimension CanonicalAuxiliaryCandidateCover.equation
  Term.finitePolynomial IntegralMixedAuxiliaryCandidate.pointAt FormulaSignSlotRadialProviderAtomic.field
  FormulaSignSlotRadialProviderAtomic.Valid
  FormulaSignSlotCircularBoundedCover.projectedIndex sourceSample
private theorem projected_index_lt (c : List Bool) (i : Fin (FormulaSignSlotSource.dimension c)) :
    i.val < N c := by
  rw [circle_dimension]
  have HH := (FormulaSignSlotCircularBoundedCover.projectedIndex c i).isLt
  rw [projected_index_val] at HH
  exact HH
private theorem sample_coordinate (c label : List Bool) (hg : AuxiliaryCandidateComponentCover.Good hn ht ha c label)
    (i : Fin (FormulaSignSlotSource.dimension c)) :
    (FormulaSignSlotCircularBoundedCover.projectedPoint c (sourceSample c label hg)).val i =
      IntegralMixedAuxiliaryCandidate.pointAt hn ht ha c label (Classical.choose hg) ⟨i.val,projected_index_lt c i⟩ := by
  rw [FormulaSignSlotCircularBoundedCover.projectedPoint_coordinate]
  have HE := congrFun (sourceSample_forward c label hg) ⟨i.val,projected_index_lt c i⟩
  rw [homeomorph_coordinate] at HE
  have Hidx : FormulaSignSlotCircularBoundedCover.projectedIndex c i =
      Fin.cast (circle_dimension c) ⟨i.val,projected_index_lt c i⟩ := by
    apply Fin.ext
    simpa only [Fin.val_cast] using projected_index_val c i
  exact (congrArg (sourceSample c label hg).val Hidx).trans HE

private theorem initial_index (side : Bool) (H q : List Bool)
    (hc : FormulaSignSlotRadialProviderAtomic.provider q = LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.context side H)
    (i : Fin (LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.dimension H)) : i.val < FormulaSignSlotRadialProviderAtomic.initial q := by
  have HI := projected_index_lt (FormulaSignSlotRadialJointLayout.source side H)
    (Fin.cast (dimension_eq side H).symm i)
  have HE := FormulaSignSlotRadialProviderAtomic.initial_provider q
  rw [hc] at HE
  change FormulaSignSlotRadialProviderAtomic.initial q =
    FormulaSignSlotRadialExternalContext.number (LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.context side H)+8 at HE
  have HN : FormulaSignSlotRadialExternalContext.number (LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.context side H) =
      N (FormulaSignSlotRadialJointLayout.source side H) :=
    by simpa only [LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.context] using
      FormulaSignSlotRadialOldProviderRealization.number_context (FormulaSignSlotRadialJointLayout.source side H)
        (LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.candidate side H) []
  rw [HN] at HE
  simp only [Fin.val_cast] at HI
  omega

private theorem scalar_index (q : List Bool) (i : ℕ) (hi : i < FormulaSignSlotRadialProviderAtomic.initial q) :
    i < FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context q) := by
  rw [FormulaSignSlotRadialProviderFieldEquality.count_eq]
  simp only [FormulaSignSlotRadialProviderAtomic.context, pairFst_pair]
  change i < FormulaSignSlotRadialProviderAtomic.initial q + IntegralMixedCausalRecordPlanBits.count
    (FormulaSignSlotRadialProviderAtomic.root q)
  omega

theorem projectedSample_fields (side : Bool) (H q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hc : FormulaSignSlotRadialProviderAtomic.provider q = LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.context side H) (hg : Good side H)
    (i : Fin (LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.dimension H)) : projectedSample side H hg i = FormulaSignSlotRadialProviderAtomic.field q hv i.val := by
  let u := FormulaSignSlotRadialJointLayout.source side H
  let j := Fin.cast (dimension_eq side H).symm i
  have HP := sample_coordinate u (LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.candidate side H) hg j
  have hc' : FormulaSignSlotRadialProviderAtomic.provider q = FormulaSignSlotRadialOldProviderRealization.context
      u (LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.candidate side H) [] := hc
  obtain ⟨hV,HF⟩ := FormulaSignSlotRadialProviderOldLabelGeometry.pointAt_fields u
    (LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.candidate side H) [] q hv hc'
  exact HP.trans (HF ⟨i.val,projected_index_lt u j⟩)

theorem good_of_valid (side : Bool) (H q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hc : FormulaSignSlotRadialProviderAtomic.provider q = LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.context side H) : Good side H :=
  FormulaSignSlotRadialProviderOldLabelGeometry.good_of_valid _ _ [] q hv hc

attribute [local irreducible] FormulaSignSlotRadialProviderFieldEquality.point
  FormulaSignSlotRadialProviderFieldEquality.language IntegralFramedPhysicalBankTerm.env

private theorem field_packet_iff (a b : List Bool)
    (haV : FormulaSignSlotRadialProviderAtomic.Valid a) (hbV : FormulaSignSlotRadialProviderAtomic.Valid b)
    (i : ℕ) (hai : i < FormulaSignSlotRadialProviderAtomic.initial a)
    (hbi : i < FormulaSignSlotRadialProviderAtomic.initial b) :
    LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.fieldPacket a b i ∈ FormulaSignSlotRadialProviderFieldEquality.language ↔
      FormulaSignSlotRadialProviderAtomic.field a haV i = FormulaSignSlotRadialProviderAtomic.field b hbV i := by
  have HA := scalar_index a i hai
  have HB := scalar_index b i hbi
  have HE := FormulaSignSlotRadialProviderFieldEquality.language_packet_iff
    (FormulaSignSlotRadialProviderAtomic.context a) (FormulaSignSlotRadialProviderAtomic.word a)
    (FormulaSignSlotRadialProviderAtomic.context b) (FormulaSignSlotRadialProviderAtomic.word b)
    (FormulaSignSlotRadialProviderAtomic.full_valid a haV) (FormulaSignSlotRadialProviderAtomic.full_valid b hbV) i i HA HB
  have HPa : FormulaSignSlotRadialProviderFieldEquality.point (FormulaSignSlotRadialProviderAtomic.context a)
      (FormulaSignSlotRadialProviderAtomic.word a) (FormulaSignSlotRadialProviderAtomic.full_valid a haV) i =
      FormulaSignSlotRadialProviderAtomic.field a haV i := by
    simpa only [FormulaSignSlotRadialProviderAtomic.field, FormulaSignSlotRadialProviderAtomic.bankField] using
      FormulaSignSlotRadialProviderFieldEquality.point_env _ _ (FormulaSignSlotRadialProviderAtomic.full_valid a haV) i HA
  have HPb : FormulaSignSlotRadialProviderFieldEquality.point (FormulaSignSlotRadialProviderAtomic.context b)
      (FormulaSignSlotRadialProviderAtomic.word b) (FormulaSignSlotRadialProviderAtomic.full_valid b hbV) i =
      FormulaSignSlotRadialProviderAtomic.field b hbV i := by
    simpa only [FormulaSignSlotRadialProviderAtomic.field, FormulaSignSlotRadialProviderAtomic.bankField] using
      FormulaSignSlotRadialProviderFieldEquality.point_env _ _ (FormulaSignSlotRadialProviderAtomic.full_valid b hbV) i HB
  exact HE.trans ⟨fun h => HPa.symm.trans (h.trans HPb), fun h => HPa.trans (h.trans HPb.symm)⟩

theorem holds_iff (H a b : List Bool)
    (haV : FormulaSignSlotRadialProviderAtomic.Valid a) (hbV : FormulaSignSlotRadialProviderAtomic.Valid b)
    (hca : FormulaSignSlotRadialProviderAtomic.provider a = LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.context false H)
    (hcb : FormulaSignSlotRadialProviderAtomic.provider b = LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.context true H)
    (hL : Good false H) (hR : Good true H) :
    LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.Holds H a b ↔ projectedSample false H hL = projectedSample true H hR := by
  constructor
  · intro HT
    funext i
    rw [projectedSample_fields false H a haV hca hL i, projectedSample_fields true H b hbV hcb hR i]
    exact (field_packet_iff a b haV hbV i.val (initial_index false H a hca i) (initial_index true H b hcb i)).mp
      (HT i.val i.isLt)
  · intro HE i hi
    let j : Fin (LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.dimension H) := ⟨i,hi⟩
    apply (field_packet_iff a b haV hbV i (initial_index false H a hca j) (initial_index true H b hcb j)).mpr
    exact (projectedSample_fields false H a haV hca hL j).symm.trans
      ((congrFun HE j).trans (projectedSample_fields true H b hbV hcb hR j))

private theorem exists_valid (side : Bool) (H : List Bool) (hg : Good side H) :
    ∃ q : List Bool, ∃ _hv : FormulaSignSlotRadialProviderAtomic.Valid q,
      FormulaSignSlotRadialProviderAtomic.provider q = LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.context side H := by
  obtain ⟨_,w,hV,_⟩ := FormulaSignSlotRadialProviderFirstSeed.exists_old_seed
    (FormulaSignSlotRadialJointLayout.source side H) (LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.candidate side H) [] hg
  exact ⟨_,hV,FormulaSignSlotRadialProviderFirstSeed.provider_packet _ w⟩

theorem language_iff (H : List Bool) : H ∈ LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.language ↔
    ∃ hL : Good false H, ∃ hR : Good true H, projectedSample false H hL = projectedSample true H hR := by
  rw [LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.language_iff]
  constructor
  · rintro ⟨a,b,haV,hbV,hca,hcb,HT⟩
    have hL := good_of_valid false H a haV hca
    have hR := good_of_valid true H b hbV hcb
    exact ⟨hL,hR,(holds_iff H a b haV hbV hca hcb hL hR).mp HT⟩
  · rintro ⟨hL,hR,HE⟩
    obtain ⟨a,haV,hca⟩ := exists_valid false H hL
    obtain ⟨b,hbV,hcb⟩ := exists_valid true H hR
    exact ⟨a,b,haV,hbV,hca,hcb,(holds_iff H a b haV hbV hca hcb hL hR).mpr HE⟩

theorem mem_iff (H : List Bool) (hL : Good false H) (hR : Good true H) :
    H ∈ LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.language ↔ projectedSample false H hL = projectedSample true H hR := by
  rw [language_iff]
  exact ⟨fun ⟨_,_,h⟩ => h, fun h => ⟨hL,hR,h⟩⟩

end LeanCanny.Connectivity.FormulaSignSlotProjectedSampleEquality
