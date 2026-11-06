/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryRadialCodec
public import LeanCanny.Connectivity.CanonicalProjectedSampleEqualityCodec
/-! # The original frontier edge is equality or oriented joint feasibility -/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryFrontierJointCodec
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- This uses the original cover, candidate labels and original description.
Both radial alternatives retain every grid and cut condition. -/
theorem edge_iff (d : Description) (hd : d.WellFormed)
    (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    CanonicalAuxiliaryCandidateCover.edge d i j ↔
      CanonicalAuxiliaryJointHeader.header d i j ∈ FormulaSignSlotProjectedSampleEquality.language ∨
      FormulaSignSlotRadialJointFeasibility.Feasible (CanonicalAuxiliaryJointHeader.header d i j) ∨
      FormulaSignSlotRadialJointFeasibility.Feasible (CanonicalAuxiliaryJointHeader.header d j i) := by
  rw [CanonicalAuxiliaryProjectedSamples.incident_iff d hd i j,
    CanonicalProjectedSampleEqualityCodec.language_iff d i j,
    CanonicalAuxiliaryRadialCodec.feasible_iff_raw_descriptor d i j,
    CanonicalAuxiliaryRadialCodec.feasible_iff_raw_descriptor d j i]
  constructor
  · rintro ⟨hi,hj,H⟩
    rcases H with HE | HL | HR
    · exact Or.inl ⟨hi,hj,HE⟩
    · exact Or.inr (Or.inl HL)
    · exact Or.inr (Or.inr HR)
  · rintro (⟨hi,hj,HE⟩ | HL | HR)
    · exact ⟨hi,hj,Or.inl HE⟩
    · obtain ⟨x,hx,hD⟩ := HL
      exact ⟨CanonicalAuxiliaryProjectedSamples.good_of_raw_nonempty d i ⟨x,hx⟩,
        hD.elim (fun D => D.good),Or.inr (Or.inl ⟨x,hx,hD⟩)⟩
    · obtain ⟨x,hx,hD⟩ := HR
      exact ⟨hD.elim (fun D => D.good),
        CanonicalAuxiliaryProjectedSamples.good_of_raw_nonempty d j ⟨x,hx⟩,
        Or.inr (Or.inr ⟨x,hx,hD⟩)⟩

end LeanCanny.Connectivity.CanonicalAuxiliaryFrontierJointCodec
