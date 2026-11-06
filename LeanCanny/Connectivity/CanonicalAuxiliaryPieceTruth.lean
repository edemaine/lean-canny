/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryProjectedSamples
public import LeanCanny.Connectivity.FormulaSignSlotTruth
/-! # Original subformula truth is constant on each actual auxiliary piece -/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryPieceTruth
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- The actual raw piece retains its literal original sign stratum. -/
theorem raw_stratum (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d)
    (x : Fin d.dimension → ℝ) (hx : x ∈ (CanonicalAuxiliaryCandidateCover.data d).rawPiece i) :
    (FormulaSignSlotSource.stratum (CanonicalSignRefinement.source d i.1)).Holds (Formula.extend x) := by
  obtain ⟨a,ha,rfl⟩ := hx
  rw [CanonicalSignRefinement.extend_tuple]
  exact FormulaSignSlotRadialAccess.projectedPiece_selected _ _ ha

/-- Any literal subformula has the same truth at every point of the piece.
The prefix/suffix identify its actual position in the original formula. -/
theorem holds_iff (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d)
    (p : Formula) (pre suffix : List Bool)
    (hc : FormulaView.normalize (Input.field 2 (CanonicalSignRefinement.original d)) =
      pre ++ p.encode ++ suffix)
    (hp : p.arity ≤ ClosedFormulaGateMetadata.dimension (CanonicalSignRefinement.original d))
    (x y : Fin d.dimension → ℝ)
    (hx : x ∈ (CanonicalAuxiliaryCandidateCover.data d).rawPiece i)
    (hy : y ∈ (CanonicalAuxiliaryCandidateCover.data d).rawPiece i) :
    p.Holds (Formula.extend x) ↔ p.Holds (Formula.extend y) := by
  have HX := FormulaSignSlotTruth.wire_truth (CanonicalSignRefinement.original d) i.1.val
    (Formula.extend x) (raw_stratum d i x hx) p pre suffix hc hp
  have HY := FormulaSignSlotTruth.wire_truth (CanonicalSignRefinement.original d) i.1.val
    (Formula.extend y) (raw_stratum d i y hy) p pre suffix hc hp
  simpa only [decide_eq_true_eq] using Bool.eq_iff_iff.mp (HX.symm.trans HY)

/-- When a subformula denotes a singleton, every point of a piece meeting it
is that singleton. In particular its already accepted sample is the endpoint. -/
theorem sample_eq_of_denotes (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d)
    (hi : CanonicalAuxiliaryProjectedSamples.Good d i) (p : Formula) (pre suffix : List Bool)
    (hc : FormulaView.normalize (Input.field 2 (CanonicalSignRefinement.original d)) =
      pre ++ p.encode ++ suffix)
    (hp : p.arity ≤ ClosedFormulaGateMetadata.dimension (CanonicalSignRefinement.original d))
    (x : Fin d.dimension → ℝ) (hx : Denotes d.dimension p x)
    (hm : x ∈ (CanonicalAuxiliaryCandidateCover.data d).rawPiece i) :
    CanonicalAuxiliaryCandidateCover.rawSample d i hi = x := by
  apply (hx.2 _).mp
  exact (holds_iff d i p pre suffix hc hp x _ hm
    (CanonicalAuxiliaryCandidateCover.rawSample_mem d i hi)).mp ((hx.2 x).mpr rfl)

end LeanCanny.Connectivity.CanonicalAuxiliaryPieceTruth
