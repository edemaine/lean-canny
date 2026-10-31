/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceRootTransport
public import LeanCanny.Encoding.CoordinateDoubleAffineChildSamples
public import LeanCanny.Encoding.SquareSampleContextProjectionChoiceAt

/-! # Native child labels in the same shared-source trace sampler

The native search re-encodes a child sample at its appended history. Every
powered coordinate is preserved; no equality of native word encodings is
assumed between contexts. Correctness is guarded by the native frame check.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
open LeanCanny.Algebra LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] objective levels depth append seedCoordinate

noncomputable def sampleInput (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) : SquareSampleInput.Inputs :=
  FlatAffinePowerSampleInput.input (inputs P d old level) (cone P d old level)

theorem sampleAccess {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) : (sampleInput P d old level).Access :=
  FlatAffinePowerSampleInput.access (access hP hd ho hl hA) (cone P d old level)

theorem child_sampleAccess (midpoint : Bool) {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    (CoordinateDoubleAffineChildRecords.childInput midpoint (readers P) (depth d) (objective d old) (levels P d old level)).Access :=
  FlatAffinePowerSampleInput.access
    (CoordinateDoubleAffineChildRecords.access midpoint (readers_polyTime hP) (depth_unary hd) (objective_unary hd ho)
      (levels_evaluator hP hd ho hl) (fun q => hA (base q)))
    (CoordinateDoubleAffineChildRecords.cone midpoint (readers P) (depth d) (objective d old) (levels P d old level))

theorem childProjection_coordinate_unary (midpoint : Bool) {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    UnaryFn (fun z => (SquareSampleContextThom.coordinate
      (CoordinateDoubleAffineChildRecords.childInput midpoint (readers P) (depth d) (objective d old) (levels P d old level))
      (sampleInput P d old level) (append midpoint) (childProjection midpoint P d old level)
      (LeanCanny.pairFst z) (LeanCanny.pairSnd z)).val) := by
  have hi : (fun z => LeanCanny.pairFst (LeanCanny.pairSnd (LeanCanny.pairSnd z))) ∈ FP :=
    mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
  exact UnaryFn.fromBitsLE_min hi
    ((((sampleAccess hP hd ho hl hA).count.comp (append_FP midpoint)).comp pairFst_mem_FP).sub (UnaryFn.const 1))

noncomputable def reencodeChild (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) : List Bool → List Bool :=
  SquareSampleContextProjectionChoice.value
    (CoordinateDoubleAffineChildRecords.childInput midpoint (readers P) (depth d) (objective d old) (levels P d old level))
    (sampleInput P d old level) (append midpoint) (childProjection midpoint P d old level)

theorem reencodeChild_evaluator (midpoint : Bool) {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) : SpaceFunction (reencodeChild midpoint P d old level) :=
  SquareSampleContextProjectionChoice.evaluator (child_sampleAccess midpoint hP hd ho hl hA)
    (sampleAccess hP hd ho hl hA) (append_FP midpoint) (childProjection midpoint P d old level)
    (childProjection_coordinate_unary midpoint hP hd ho hl hA)

theorem reencodeChild_projects (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (x : SquareSampleComplete.Roots
      (CoordinateDoubleAffineChildRecords.childInput midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q) :
    ∀ i, ((sampleInput P d old level).system (append midpoint q) i).eval₂ (Int.castRingHom ℝ)
      (x.val ∘ childProjection midpoint P d old level q) = 0 := by
  intro i
  have HE := congrArg (fun z : Fin ((sampleInput P d old level).count (append midpoint q)) → ℝ =>
    ((sampleInput P d old level).system (append midpoint q) i).eval₂ (Int.castRingHom ℝ) z)
      (powerRoot_val midpoint P d old level q hv x)
  exact HE.symm.trans ((powerRoot midpoint P d old level q hv x).property i)

attribute [local irreducible] reencodeChild SquareSampleCompleteVertices.Valid

theorem reencodeChild_valid (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (hw : SquareSampleCompleteVertices.Valid
      (CoordinateDoubleAffineChildRecords.childInput midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q w) :
    SquareSampleCompleteVertices.Valid (sampleInput P d old level) (append midpoint q)
      (reencodeChild midpoint P d old level (LeanCanny.pair q w)) := by
  unfold reencodeChild
  exact SquareSampleContextProjectionChoice.value_valid_at
    (CoordinateDoubleAffineChildRecords.childInput midpoint (readers P) (depth d) (objective d old) (levels P d old level))
    (sampleInput P d old level) (FlatAffinePowerSampleInput.complete (inputs P d old level) (cone P d old level))
    (append midpoint) (childProjection midpoint P d old level) q w hw
    (reencodeChild_projects midpoint P d old level q hv (SquareSampleCompleteVertices.candidate _ q w hw))

theorem reencodeChild_point (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (hw : SquareSampleCompleteVertices.Valid
      (CoordinateDoubleAffineChildRecords.childInput midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q w) :
    (SquareSampleCompleteVertices.candidate (sampleInput P d old level) (append midpoint q)
      (reencodeChild midpoint P d old level (LeanCanny.pair q w)) (reencodeChild_valid midpoint P d old level q w hv hw)).val =
        (SquareSampleCompleteVertices.candidate
          (CoordinateDoubleAffineChildRecords.childInput midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q w hw).val ∘
            childProjection midpoint P d old level q := by
  unfold reencodeChild
  exact SquareSampleContextProjectionChoice.value_point_at
    (CoordinateDoubleAffineChildRecords.childInput midpoint (readers P) (depth d) (objective d old) (levels P d old level))
    (sampleInput P d old level) (FlatAffinePowerSampleInput.complete (inputs P d old level) (cone P d old level))
    (append midpoint) (childProjection midpoint P d old level) q w hw
    (reencodeChild_projects midpoint P d old level q hv (SquareSampleCompleteVertices.candidate _ q w hw))

end LeanCanny.Encoding.CoordinateDoubleAffineTrace
