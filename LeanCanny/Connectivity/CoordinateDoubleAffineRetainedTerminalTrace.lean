/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.CoordinateDoubleAffineRetainedTerminalReachability
public import LeanCanny.Connectivity.CoordinateDoubleAffineTraceFiberPointGeometry

/-! # The terminal base evaluates the actual emitted retained-point query

The generic stage decoder agrees with the two references emitted by the
common-fiber request. At terminal rank, the native child-label search therefore
decides exactly the requested connection of the original two critical points.
The finite slice can contain several points; membership and equality are
checked by the search, rather than inferred from rank zero.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CoordinateDoubleAffineRetainedTerminalTrace
open Set LeanCanny.Algebra LeanCanny.Encoding
open CoordinateDoubleAffineTrace
open CoordinateDoubleAffineTraceFiberPointGeometry (queryRoot decodedPoint)
open scoped Classical
attribute [local irreducible] objective levels depth append seedCoordinate

noncomputable def outputStage (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool) (right : Bool) : Fin (depth d (append true q)) :=
  ⟨CoordinateDoubleAffineTraceFiberPointRequests.reference right
    (CoordinateDoubleAffineTraceFiberPointRequests.query P d old level (LeanCanny.pair q w)), by
    simpa only [CoordinateDoubleAffineTraceFiberPointRequests.source,
      CoordinateDoubleAffineTraceFiberPointRequests.query, LeanCanny.pairFst_pair] using
      CoordinateDoubleAffineTraceFiberPointRequests.query_references_lt P d old level (LeanCanny.pair q w) right⟩

theorem output_record (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool) :
    FlatAffineRetainedPointChildMatch.record (append true q) (midpointFrameWord P d old level (LeanCanny.pair q w))
      (outputStage P d old level q w false).val (outputStage P d old level q w true).val =
      CoordinateDoubleAffineTraceFiberPointRequests.query P d old level (LeanCanny.pair q w) := by
  simp only [FlatAffineRetainedPointChildMatch.record, outputStage,
    CoordinateDoubleAffineTraceFiberPointRequests.reference, CoordinateDoubleAffineTraceFiberPointRequests.query,
    CoordinateDoubleAffineTraceFiberPointRequests.references, CoordinateDoubleAffineTraceHeightRequests.samplePacket,
    LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair, Bool.false_eq_true, ite_false, ite_true,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem point_decoded (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool)
    (hq : LeanCanny.pair q w ∈ CoordinateDoubleAffineTraceFiberPointRequests.ready P d old level)
    (right : Bool) :
    FlatAffineRetainedPointChildMatch.point (inputs P d old level) (append true q)
      (queryRoot P d old level q w hq) (outputStage P d old level q w right) =
      decodedPoint P d old level q w hq right := by
  have hdim : FlatAffineFullSourceTower.arity (inputs P d old level) (append true q) = (readers P).dim q + 4 :=
    (congrArg (fun F => FlatAffineFullSourceTower.arity F q) (extendedInputs_eq_context true P d old level)).symm
  funext i
  unfold FlatAffineRetainedPointChildMatch.point decodedPoint
    CoordinateDoubleAffineTraceFiberPointGeometry.liftPoint CoordinateDoubleAffineFiberPointGeometry.retainedPoint
  simp only [Function.comp_apply]
  apply congrArg (queryRoot P d old level q w hq).val
  apply Fin.ext
  change i.val + FlatAffineCriticalTower.width (FlatAffineFullSourceTower.arity (inputs P d old level) (append true q)) *
      (outputStage P d old level q w right).val =
    (CoordinateDoubleAffineTraceFiberPointGeometry.stageIndex P d old level q w right).val *
      FlatAffineCriticalTower.width ((readers P).dim q + 4) + i.val
  rw [congrArg FlatAffineCriticalTower.width hdim]
  ac_rfl

theorem packet (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool)
    (hq : LeanCanny.pair q w ∈ CoordinateDoubleAffineTraceFiberPointRequests.ready P d old level)
    (hmax : (readers P).dim (append true q) + 3 ≤
      objective d old (FlatAffineFullSourceTower.stage (append true q) (depth d (append true q)))) :
    CoordinateDoubleAffineTraceFiberPointRequests.query P d old level (LeanCanny.pair q w) ∈
      CoordinateDoubleAffineRetainedTerminalReachability.language (readers P) (depth d) (objective d old)
        (levels P d old level) ↔
      JoinedIn (CoordinateDoubleAffineFiberPointGeometry.Pair.fiber (readers P) (depth d)
        (objective d old) (levels P d old level) q w
          (CoordinateDoubleAffineTraceFiberPointGeometry.pair_valid P d old level q w hq))
        (CoordinateDoubleAffineFiberPointGeometry.Pair.point (readers P) (depth d)
          (objective d old) (levels P d old level) false q w
            (CoordinateDoubleAffineTraceFiberPointGeometry.pair_valid P d old level q w hq))
        (CoordinateDoubleAffineFiberPointGeometry.Pair.point (readers P) (depth d)
          (objective d old) (levels P d old level) true q w
            (CoordinateDoubleAffineTraceFiberPointGeometry.pair_valid P d old level q w hq)) := by
  have hv : FlatAffineCompleteVertices.Valid (inputs P d old level)
      (FlatAffineCompleteChildLabels.parentCone (inputs P d old level)
        (CoordinateDoubleAffineSliceRegularity.cone (readers P) (depth d) (objective d old) (levels P d old level)))
      (append true q) (midpointFrameWord P d old level (LeanCanny.pair q w)) :=
    midpointFrameWord_valid P d old level q w
      (CoordinateDoubleAffineTraceFiberPointGeometry.frame_valid P d old level q w hq)
      (CoordinateDoubleAffineTraceFiberPointGeometry.pair_valid P d old level q w hq)
      (CoordinateDoubleAffineTraceFiberPointGeometry.shared P d old level q w hq)
  have HB := CoordinateDoubleAffineRetainedTerminalReachability.packet (readers P) (depth d) (objective d old)
    (levels P d old level) (append true q) (midpointFrameWord P d old level (LeanCanny.pair q w)) hmax hv
    (outputStage P d old level q w false) (outputStage P d old level q w true)
  have HI := Iff.of_eq (congrArg (fun r => r ∈
    CoordinateDoubleAffineRetainedTerminalReachability.language (readers P) (depth d) (objective d old)
      (levels P d old level)) (output_record P d old level q w))
  have HP := Iff.of_eq (congrArg₂ (fun a b => JoinedIn
    (FlatAffineCompleteComponentSamples.slice (inputs P d old level) (append true q)
      (queryRoot P d old level q w hq)) a b)
        (point_decoded P d old level q w hq false) (point_decoded P d old level q w hq true))
  exact HI.symm.trans (HB.trans (HP.trans (CoordinateDoubleAffineTraceFiberPointGeometry.joined_iff P d old level q w hq)))

end LeanCanny.Connectivity.CoordinateDoubleAffineRetainedTerminalTrace
