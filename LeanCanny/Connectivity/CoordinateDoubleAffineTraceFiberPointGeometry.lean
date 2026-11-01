/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceFiberPointRequests
public import LeanCanny.Connectivity.CoordinateDoubleAffineFiberPointGeometry
public import LeanCanny.Connectivity.CoordinateDoubleAffineTraceChildConnectivity

/-! # The retained point references of an emitted fiber query

Transporting the child parent to the uniform trace context preserves both
retained spatial points. Decoding the two stage references therefore recovers
the original critical points, rather than newly chosen component samples.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CoordinateDoubleAffineTraceFiberPointGeometry
open Set LeanCanny.Algebra LeanCanny.Encoding
open CoordinateDoubleAffineTrace
open CoordinateDoubleAffineFiberPointGeometry (retainedPoint)
open scoped Classical
attribute [local irreducible] objective levels depth append seedCoordinate

def rootIndex (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) :
    Fin (FlatAffineFullSourceTower.count
      (CoordinateDoubleAffineChildRecords.inputs true (readers P) (depth d) (objective d old) (levels P d old level)) q) →
      Fin (FlatAffineFullSourceTower.count (inputs P d old level) (append true q)) :=
  Fin.cast (congrArg (fun F => FlatAffineFullSourceTower.count F q)
    (extendedInputs_eq_context true P d old level))

theorem originalRoot_pullback (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (x : FlatAffinePowerSampleInput.OriginalRoots
      (CoordinateDoubleAffineChildRecords.inputs true (readers P) (depth d) (objective d old) (levels P d old level)) q) :
    (originalRoot true P d old level q hv x).val ∘ rootIndex P d old level q = x.val := by
  unfold originalRoot
  rw [FlatAffineOriginalRootTransport.context_val, FlatAffineOriginalRootTransport.transport_val,
    extendedOriginalRoot_val]
  funext i
  apply congrArg x.val
  apply Fin.ext
  rfl

def liftPoint (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (x : Fin ((readers P).dim q + 4) → ℝ) :
    Fin (FlatAffineFullSourceTower.arity (inputs P d old level) (append true q)) → ℝ :=
  x ∘ Fin.cast (congrArg (fun F => FlatAffineFullSourceTower.arity F q)
    (extendedInputs_eq_context true P d old level)).symm

theorem liftPoint_comp (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (x : Fin ((readers P).dim q + 4) → ℝ) :
    liftPoint P d old level q x ∘ ambientIndex true P d old level q = x := by
  funext i
  apply congrArg x
  apply Fin.ext
  rfl

section Query
variable (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
  (level : List Bool → List Bool) (q w : List Bool)
  (hq : LeanCanny.pair q w ∈ CoordinateDoubleAffineTraceFiberPointRequests.ready P d old level)

include hq

theorem frame_valid : Valid P (seedCoordinate d old) q := by
  simpa only [CoordinateDoubleAffineTraceHeightRequests.frameGuard, LeanCanny.pairFst_pair] using hq.1.1

theorem pair_valid : SquareSampleCompleteVertices.Valid
    (CoordinateDoubleAffineCriticalPairs.input (readers P) (depth d) (objective d old) (levels P d old level)) q w := by
  simpa only [CoordinateDoubleAffineCriticalPairs.sharedLanguage, SquareSampleCompleteVertices.language,
    CoordinateDoubleAffineTraceHeightRequests.samplePacket, Set.mem_ofPred_eq,
    LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair] using hq.2.1.1

theorem shared : LeanCanny.pair q w ∈ CoordinateDoubleAffineCriticalPairs.sharedLanguage
    (readers P) (depth d) (objective d old) (levels P d old level) := by
  simpa only [CoordinateDoubleAffineTraceHeightRequests.samplePacket,
    LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair] using hq.2.1

noncomputable def queryRoot : FlatAffinePowerSampleInput.OriginalRoots (inputs P d old level) (append true q) :=
  FlatAffineCompleteVertices.vertexEquiv (inputs P d old level) (cone P d old level) (append true q)
    ⟨midpointFrameWord P d old level (LeanCanny.pair q w),
      midpointFrameWord_valid P d old level q w (frame_valid P d old level q w hq)
        (pair_valid P d old level q w hq) (shared P d old level q w hq)⟩

theorem queryRoot_eq : queryRoot P d old level q w hq = originalRoot true P d old level q
    (frame_valid P d old level q w hq)
      (CoordinateDoubleAffineCriticalPairs.midpointRoot (readers P) (depth d) (objective d old)
        (levels P d old level) q w (pair_valid P d old level q w hq) (shared P d old level q w hq)) := by
  have hw := CoordinateDoubleAffineCriticalPairs.midpointWord_valid (readers P) (depth d) (objective d old)
    (levels P d old level) q w (pair_valid P d old level q w hq) (shared P d old level q w hq)
  have HR := reencodeChild_root true P d old level q
    (CoordinateDoubleAffineCriticalPairs.midpointWord (readers P) (depth d) (objective d old)
      (levels P d old level) (LeanCanny.pair q w)) (frame_valid P d old level q w hq) hw
  have HM := CoordinateDoubleAffineCriticalPairs.midpointWord_root (readers P) (depth d) (objective d old)
    (levels P d old level) q w (pair_valid P d old level q w hq) (shared P d old level q w hq)
  rw [HM] at HR
  simpa only [queryRoot, midpointFrameWord, LeanCanny.pairFst_pair] using HR

theorem queryRoot_pullback :
    (queryRoot P d old level q w hq).val ∘ rootIndex P d old level q =
      (CoordinateDoubleAffineCriticalPairs.midpointRoot (readers P) (depth d) (objective d old)
        (levels P d old level) q w (pair_valid P d old level q w hq) (shared P d old level q w hq)).val :=
  (congrArg (fun root => root.val ∘ rootIndex P d old level q)
    (queryRoot_eq P d old level q w hq)).trans
      (originalRoot_pullback P d old level q (frame_valid P d old level q w hq) _)

noncomputable def stageIndex (right : Bool) : Fin (depth d q + 2) :=
  ⟨CoordinateDoubleAffineTraceFiberPointRequests.reference right
    (CoordinateDoubleAffineTraceFiberPointRequests.query P d old level (LeanCanny.pair q w)), by
    have h := CoordinateDoubleAffineTraceFiberPointRequests.query_references P d old level (LeanCanny.pair q w)
    simp only [LeanCanny.pairFst_pair] at h
    cases right <;> omega⟩

omit hq in
theorem stageIndex_false : stageIndex P d old level q w false = ⟨depth d q, by omega⟩ :=
  Fin.ext (by
    simpa only [stageIndex, LeanCanny.pairFst_pair] using
      (CoordinateDoubleAffineTraceFiberPointRequests.query_references P d old level (LeanCanny.pair q w)).1)

omit hq in
theorem stageIndex_true : stageIndex P d old level q w true = ⟨depth d q + 1, by omega⟩ :=
  Fin.ext (by
    simpa only [stageIndex, LeanCanny.pairFst_pair] using
      (CoordinateDoubleAffineTraceFiberPointRequests.query_references P d old level (LeanCanny.pair q w)).2)

noncomputable def decodedPoint (right : Bool) :
    Fin (FlatAffineFullSourceTower.arity (inputs P d old level) (append true q)) → ℝ :=
  liftPoint P d old level q
    (retainedPoint ((readers P).dim q + 4) (depth d q + 2)
      (stageIndex P d old level q w right)
      ((queryRoot P d old level q w hq).val ∘ rootIndex P d old level q))

theorem decodedPoint_eq (right : Bool) : decodedPoint P d old level q w hq right =
    liftPoint P d old level q (CoordinateDoubleAffineFiberPointGeometry.Pair.point
      (readers P) (depth d) (objective d old) (levels P d old level) right q w (pair_valid P d old level q w hq)) := by
  unfold decodedPoint
  refine (congrArg (fun z => liftPoint P d old level q
    (retainedPoint ((readers P).dim q + 4) (depth d q + 2)
      (stageIndex P d old level q w right) z)) (queryRoot_pullback P d old level q w hq)).trans ?_
  unfold CoordinateDoubleAffineCriticalPairs.midpointRoot
  cases right
  · rw [stageIndex_false, CoordinateDoubleAffineFiberPointGeometry.midpointRoot_left_point]
    rfl
  · rw [stageIndex_true, CoordinateDoubleAffineFiberPointGeometry.midpointRoot_right_point]
    rfl

/-- The emitted parent and its two decoded stage references ask exactly for
the connection of the original pair inside their common-height fiber. -/
theorem joined_iff :
    JoinedIn (FlatAffineCompleteComponentSamples.slice (inputs P d old level) (append true q)
      (queryRoot P d old level q w hq))
      (decodedPoint P d old level q w hq false) (decodedPoint P d old level q w hq true) ↔
    JoinedIn (CoordinateDoubleAffineFiberPointGeometry.Pair.fiber (readers P) (depth d)
      (objective d old) (levels P d old level) q w (pair_valid P d old level q w hq))
      (CoordinateDoubleAffineFiberPointGeometry.Pair.point (readers P) (depth d)
        (objective d old) (levels P d old level) false q w (pair_valid P d old level q w hq))
      (CoordinateDoubleAffineFiberPointGeometry.Pair.point (readers P) (depth d)
        (objective d old) (levels P d old level) true q w (pair_valid P d old level q w hq)) := by
  have hv := frame_valid P d old level q w hq
  have hw := pair_valid P d old level q w hq
  have hs := shared P d old level q w hq
  let z := CoordinateDoubleAffineCriticalPairs.midpointRoot (readers P) (depth d) (objective d old)
    (levels P d old level) q w hw hs
  have Hstart := Iff.of_eq (congrArg (fun root =>
    JoinedIn (FlatAffineCompleteComponentSamples.slice (inputs P d old level) (append true q) root)
      (decodedPoint P d old level q w hq false) (decodedPoint P d old level q w hq true))
        (queryRoot_eq P d old level q w hq))
  have Htransport := CoordinateDoubleAffineTraceChildConnectivity.originalRoot_joined true P d old level q hv z
    (decodedPoint P d old level q w hq false) (decodedPoint P d old level q w hq true)
  have HL := (congrArg (fun f => f ∘ ambientIndex true P d old level q)
    (decodedPoint_eq P d old level q w hq false)).trans (liftPoint_comp P d old level q _)
  have HR := (congrArg (fun f => f ∘ ambientIndex true P d old level q)
    (decodedPoint_eq P d old level q w hq true)).trans (liftPoint_comp P d old level q _)
  have Hpoints := Iff.of_eq (congrArg₂ (fun x y => JoinedIn
    (FlatAffineCompleteComponentSamples.slice
      (CoordinateDoubleAffineChildRecords.inputs true (readers P) (depth d) (objective d old) (levels P d old level)) q z) x y)
        HL HR)
  have hn : objective d old (FlatAffineFullSourceTower.stage q (depth d q)) < (readers P).dim q + 3 := by
    rw [objective_current]
    change coordinate (seedCoordinate d old) q < P.dim (base q) + 3
    simpa only [CoordinateDoubleAffineTraceHeightRequests.frameGuard, LeanCanny.pairFst_pair] using hq.1.2
  have hh : LeanCanny.pair q w ∈ CoordinateDoubleAffineCriticalFiberPairs.language
      (readers P) (depth d) (objective d old) (levels P d old level) := by
    simpa only [CoordinateDoubleAffineTraceHeightRequests.samplePacket,
      LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair] using hq.2.2
  have Hslice := Iff.of_eq (congrArg (fun S => JoinedIn S
    (CoordinateDoubleAffineFiberPointGeometry.Pair.point (readers P) (depth d) (objective d old)
      (levels P d old level) false q w hw)
    (CoordinateDoubleAffineFiberPointGeometry.Pair.point (readers P) (depth d) (objective d old)
      (levels P d old level) true q w hw))
    (CoordinateDoubleAffineFiberPointGeometry.Pair.midpoint_slice_eq_fiber (readers P) (depth d)
      (objective d old) (levels P d old level) q w hn hw hs hh))
  exact Hstart.trans (Htransport.trans (Hpoints.trans Hslice))

end Query
end LeanCanny.Connectivity.CoordinateDoubleAffineTraceFiberPointGeometry
