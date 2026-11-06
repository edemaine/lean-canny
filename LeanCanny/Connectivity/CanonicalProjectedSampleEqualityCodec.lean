/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryJointHeader
public import LeanCanny.Connectivity.CanonicalAuxiliaryCandidateSample
public import LeanCanny.Connectivity.FormulaSignSlotProjectedSampleEquality
/-! # The native joint-header equality test compares the typed original samples -/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalProjectedSampleEqualityCodec
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "hn" => CanonicalAuxiliaryCandidateCover.dimension_unary
local notation "ht" => CanonicalAuxiliaryCandidateCover.equation_FP
local notation "ha" => CanonicalAuxiliaryCandidateCover.equation_scope

private theorem cast_vector_heq {m n : ℕ} (h : m=n) (p : Fin m → ℝ) :
    HEq (fun i : Fin n => p (Fin.cast h.symm i)) p := by cases h; rfl
private theorem homeomorph_vector_heq {m n : ℕ} (h : m=n) (p : Fin m → ℝ) :
    HEq (CanonicalSignRefinement.dimensionHomeomorph h p) p := by cases h; rfl
private theorem vector_eq_iff {m n : ℕ} (h : m=n) (p q : Fin m → ℝ) (x y : Fin n → ℝ)
    (hx : HEq p x) (hy : HEq q y) : p=q ↔ x=y := by
  cases h
  cases eq_of_heq hx
  cases eq_of_heq hy
  rfl

private noncomputable def projection (c label : List Bool)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha c label) : Fin (FormulaSignSlotSource.dimension c) → ℝ :=
  (FormulaSignSlotCircularBoundedCover.projectedPoint c
    (FormulaSignSlotRadialProviderLabelClosedGeometry.sourceSample c label hg)).val
private theorem projection_transport (c e label tag : List Bool) (hc : c=e) (hl : label=tag)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha c label)
    (he : AuxiliaryCandidateComponentCover.Good hn ht ha e tag) :
    HEq (projection c label hg) (projection e tag he) := by cases hc; cases hl; rfl
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotCircularBoundedCover.root
  FormulaSignSlotCircularInterior.description ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count
  ClosedFormulaGateMetadata.kind Input.field FormulaView.normalize
private theorem projected_heq (side : Bool) (H : List Bool)
    (hg : FormulaSignSlotProjectedSampleEquality.Good side H) :
    HEq (FormulaSignSlotProjectedSampleEquality.projectedSample side H hg)
      (projection (FormulaSignSlotRadialJointLayout.source side H)
        (LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.candidate side H) hg) := by
  unfold FormulaSignSlotProjectedSampleEquality.projectedSample
  exact cast_vector_heq (FormulaSignSlotProjectedSampleEquality.dimension_eq side H)
    (projection (FormulaSignSlotRadialJointLayout.source side H)
      (LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.candidate side H) hg)

noncomputable abbrev Good (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d) :=
  AuxiliaryCandidateComponentCover.Good hn ht ha (CanonicalSignRefinement.source d i.1) i.2.val

theorem dimension_header (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.dimension (CanonicalAuxiliaryJointHeader.header d i j) = d.dimension := by
  unfold LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.dimension FormulaSignSlotRadialJointLayout.centerCount
  rw [CanonicalAuxiliaryJointHeader.source_true, CanonicalSignRefinement.source_dimension]
theorem good_false_iff (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    FormulaSignSlotProjectedSampleEquality.Good false (CanonicalAuxiliaryJointHeader.header d i j) ↔ Good d i := by
  unfold FormulaSignSlotProjectedSampleEquality.Good LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.candidate
  rw [CanonicalAuxiliaryJointHeader.source_false, CanonicalAuxiliaryJointHeader.candidate_false]
theorem good_true_iff (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    FormulaSignSlotProjectedSampleEquality.Good true (CanonicalAuxiliaryJointHeader.header d i j) ↔ Good d j := by
  unfold FormulaSignSlotProjectedSampleEquality.Good LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.candidate
  rw [CanonicalAuxiliaryJointHeader.source_true, CanonicalAuxiliaryJointHeader.candidate_true]

private theorem raw_heq (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d) (hi : Good d i) :
    HEq (CanonicalAuxiliaryCandidateCover.rawSample d i hi)
      (projection (CanonicalSignRefinement.source d i.1) i.2.val hi) := by
  change HEq (CanonicalSignRefinement.dimensionHomeomorph (CanonicalSignRefinement.source_dimension d i.1)
    (projection (CanonicalSignRefinement.source d i.1) i.2.val hi)) _
  exact homeomorph_vector_heq _ _

attribute [local irreducible] projection CanonicalAuxiliaryCandidateCover.rawSample
  FormulaSignSlotProjectedSampleEquality.projectedSample
  LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.language
  CanonicalSignRefinement.source CanonicalAuxiliaryJointHeader.header

theorem projected_false_heq (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d)
    (hg : FormulaSignSlotProjectedSampleEquality.Good false (CanonicalAuxiliaryJointHeader.header d i j))
    (hi : Good d i) :
    HEq (FormulaSignSlotProjectedSampleEquality.projectedSample false (CanonicalAuxiliaryJointHeader.header d i j) hg)
      (CanonicalAuxiliaryCandidateCover.rawSample d i hi) := by
  have HC := projection_transport _ _ _ _ (CanonicalAuxiliaryJointHeader.source_false d i j)
    (CanonicalAuxiliaryJointHeader.candidate_false d i j) hg hi
  exact (projected_heq false _ hg).trans (HC.trans (raw_heq d i hi).symm)

theorem projected_true_heq (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d)
    (hg : FormulaSignSlotProjectedSampleEquality.Good true (CanonicalAuxiliaryJointHeader.header d i j))
    (hj : Good d j) :
    HEq (FormulaSignSlotProjectedSampleEquality.projectedSample true (CanonicalAuxiliaryJointHeader.header d i j) hg)
      (CanonicalAuxiliaryCandidateCover.rawSample d j hj) := by
  have HC := projection_transport _ _ _ _ (CanonicalAuxiliaryJointHeader.source_true d i j)
    (CanonicalAuxiliaryJointHeader.candidate_true d i j) hg hj
  exact (projected_heq true _ hg).trans (HC.trans (raw_heq d j hj).symm)

theorem mem_iff (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d) (hi : Good d i) (hj : Good d j) :
    CanonicalAuxiliaryJointHeader.header d i j ∈ LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.language ↔
      CanonicalAuxiliaryCandidateCover.rawSample d i hi = CanonicalAuxiliaryCandidateCover.rawSample d j hj := by
  let hL := (good_false_iff d i j).mpr hi
  let hR := (good_true_iff d i j).mpr hj
  exact (FormulaSignSlotProjectedSampleEquality.mem_iff _ hL hR).trans
    (vector_eq_iff (dimension_header d i j) _ _ _ _ (projected_false_heq d i j hL hi) (projected_true_heq d i j hR hj))

theorem language_iff (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    CanonicalAuxiliaryJointHeader.header d i j ∈ LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.language ↔
      ∃ hi : Good d i, ∃ hj : Good d j,
        CanonicalAuxiliaryCandidateCover.rawSample d i hi = CanonicalAuxiliaryCandidateCover.rawSample d j hj := by
  constructor
  · intro H
    obtain ⟨hL,hR,HE⟩ := (FormulaSignSlotProjectedSampleEquality.language_iff _).mp H
    let hi := (good_false_iff d i j).mp hL
    let hj := (good_true_iff d i j).mp hR
    exact ⟨hi,hj,(vector_eq_iff (dimension_header d i j) _ _ _ _
      (projected_false_heq d i j hL hi) (projected_true_heq d i j hR hj)).mp HE⟩
  · rintro ⟨hi,hj,HE⟩
    exact (mem_iff d i j hi hj).mpr HE

end LeanCanny.Connectivity.CanonicalProjectedSampleEqualityCodec
