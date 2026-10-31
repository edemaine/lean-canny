/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceChildWords
public import LeanCanny.Encoding.CoordinateDoubleAffineMidpointWords

/-! # Native height and midpoint factories in one coordinate trace family -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
open LeanCanny.Algebra LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] objective levels depth append seedCoordinate

noncomputable def heightFrameWord (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (p : List Bool) : List Bool :=
  reencodeChild false P d old level (LeanCanny.pair (LeanCanny.pairFst p)
    (CoordinateDoubleAffineChildRecords.heightWord (readers P) (depth d) (objective d old) (levels P d old level) p))

noncomputable def midpointFrameWord (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (p : List Bool) : List Bool :=
  reencodeChild true P d old level (LeanCanny.pair (LeanCanny.pairFst p)
    (CoordinateDoubleAffineCriticalPairs.midpointWord (readers P) (depth d) (objective d old) (levels P d old level) p))

theorem heightFrameWord_evaluator {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) : SpaceFunction (heightFrameWord P d old level) := by
  have H := CoordinateDoubleAffineChildRecords.heightWord_evaluator (readers_polyTime hP) (depth_unary hd)
    (objective_unary hd ho) (levels_evaluator hP hd ho hl) (fun q => hA (base q))
  exact (((SpaceFunction.ofFP LeanCanny.pairFst pairFst_mem_FP).pairOutputs H).chain
    (reencodeChild_evaluator false hP hd ho hl hA)).congr (funext fun _ => rfl)

theorem midpointFrameWord_evaluator {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) : SpaceFunction (midpointFrameWord P d old level) := by
  have H := CoordinateDoubleAffineCriticalPairs.midpointWord_evaluator (readers_polyTime hP) (depth_unary hd)
    (objective_unary hd ho) (levels_evaluator hP hd ho hl) (fun q => hA (base q))
  exact (((SpaceFunction.ofFP LeanCanny.pairFst pairFst_mem_FP).pairOutputs H).chain
    (reencodeChild_evaluator true hP hd ho hl hA)).congr (funext fun _ => rfl)

attribute [local irreducible] heightFrameWord midpointFrameWord SquareSampleCompleteVertices.Valid

theorem heightFrameWord_valid (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (hw : SquareSampleCompleteVertices.Valid
      (CoordinateDoubleAffineChildRecords.criticalInput (readers P) (depth d) (objective d old) (levels P d old level)) q w) :
    SquareSampleCompleteVertices.Valid (sampleInput P d old level) (append false q)
      (heightFrameWord P d old level (LeanCanny.pair q w)) := by
  unfold heightFrameWord
  simp only [LeanCanny.pairFst_pair]
  exact reencodeChild_valid false P d old level q _ hv
    (CoordinateDoubleAffineChildRecords.heightWord_valid (readers P) (depth d) (objective d old) (levels P d old level) q w hw)

theorem midpointFrameWord_valid (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (hw : SquareSampleCompleteVertices.Valid
      (CoordinateDoubleAffineCriticalPairs.input (readers P) (depth d) (objective d old) (levels P d old level)) q w)
    (hs : LeanCanny.pair q w ∈ CoordinateDoubleAffineCriticalPairs.sharedLanguage (readers P) (depth d) (objective d old) (levels P d old level)) :
    SquareSampleCompleteVertices.Valid (sampleInput P d old level) (append true q)
      (midpointFrameWord P d old level (LeanCanny.pair q w)) := by
  unfold midpointFrameWord
  simp only [LeanCanny.pairFst_pair]
  exact reencodeChild_valid true P d old level q _ hv
    (CoordinateDoubleAffineCriticalPairs.midpointWord_valid (readers P) (depth d) (objective d old) (levels P d old level) q w hw hs)

theorem heightFrameWord_point (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (hw : SquareSampleCompleteVertices.Valid
      (CoordinateDoubleAffineChildRecords.criticalInput (readers P) (depth d) (objective d old) (levels P d old level)) q w) :
    (SquareSampleCompleteVertices.candidate (sampleInput P d old level) (append false q)
      (heightFrameWord P d old level (LeanCanny.pair q w)) (heightFrameWord_valid P d old level q w hv hw)).val =
        (SquareSampleCompleteVertices.candidate
          (CoordinateDoubleAffineChildRecords.criticalInput (readers P) (depth d) (objective d old) (levels P d old level)) q w hw).val ∘
            childProjection false P d old level q := by
  have HV := CoordinateDoubleAffineChildRecords.heightWord_valid (readers P) (depth d) (objective d old) (levels P d old level) q w hw
  have H := reencodeChild_point false P d old level q _ hv HV
  have HS := congrArg (fun z => z ∘ childProjection false P d old level q)
    (CoordinateDoubleAffineChildRecords.heightWord_point (readers P) (depth d) (objective d old) (levels P d old level) q w hw)
  unfold heightFrameWord
  simp only [LeanCanny.pairFst_pair]
  exact H.trans HS

theorem midpointFrameWord_point (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (hw : SquareSampleCompleteVertices.Valid
      (CoordinateDoubleAffineCriticalPairs.input (readers P) (depth d) (objective d old) (levels P d old level)) q w)
    (hs : LeanCanny.pair q w ∈ CoordinateDoubleAffineCriticalPairs.sharedLanguage (readers P) (depth d) (objective d old) (levels P d old level)) :
    (SquareSampleCompleteVertices.candidate (sampleInput P d old level) (append true q)
      (midpointFrameWord P d old level (LeanCanny.pair q w)) (midpointFrameWord_valid P d old level q w hv hw hs)).val =
        ((SquareSampleCompleteVertices.candidate
          (CoordinateDoubleAffineCriticalPairs.input (readers P) (depth d) (objective d old) (levels P d old level)) q w hw).val ∘
            CoordinateDoubleAffineCriticalPairs.midpointProjection (readers P) (depth d) (objective d old) (levels P d old level) q) ∘
              childProjection true P d old level q := by
  have HV := CoordinateDoubleAffineCriticalPairs.midpointWord_valid (readers P) (depth d) (objective d old) (levels P d old level) q w hw hs
  have H := reencodeChild_point true P d old level q _ hv HV
  have HS := congrArg (fun z => z ∘ childProjection true P d old level q)
    (CoordinateDoubleAffineCriticalPairs.midpointWord_point (readers P) (depth d) (objective d old) (levels P d old level) q w hw hs)
  unfold midpointFrameWord
  simp only [LeanCanny.pairFst_pair]
  exact H.trans HS

end LeanCanny.Encoding.CoordinateDoubleAffineTrace
