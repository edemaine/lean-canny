/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscMomentEntry
public import LeanCanny.Algebra.IntegralMixedMatrixFrames
/-! # Custom phase-zero PSC entry writers for the augmented-moment routes -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscMomentTasks
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralBerkowitzBlockBits

abbrev Source := IntegralBerkowitzBlockBits.Source

def entryWriter (P : Parameters) (S : Source) : List Bool → List Bool :=
  IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient ∘ IntegralCriticalFlatBerkowitzQuery.entryPacket S

theorem entryWriter_FP (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S) : entryWriter P S ∈ FP :=
  mem_FP_comp (IntegralCriticalFlatBerkowitzQuery.entryPacket_FP S h)
    (IntegralCriticalFlatMatrixQuery.writer_FP P a .originalCoefficient)

theorem entryWriter_frame (P : Parameters) (S : Source) (z : List Bool) (hp : 0 < phase (original z)) :
    IntegralMixedRoutineTaskBits.Frame P (original z) (entryWriter P S z) := by
  have H := IntegralMixedMatrixFrames.matrix_frame P .originalCoefficient
    (IntegralCriticalFlatBerkowitzQuery.entryPacket S z) (by rw [IntegralCriticalFlatBerkowitzQuery.entry_parent]; exact hp)
  simpa only [entryWriter, Function.comp_apply, IntegralCriticalFlatBerkowitzQuery.entry_parent] using H

def task (P : Parameters) (S : Source) (route : List Bool → List Bool) : List Bool → List Bool :=
  entryWriter P S ∘ route ∘
    IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet P)

theorem task_FP (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S) (route : List Bool → List Bool) (hr : route ∈ FP) : task P S route ∈ FP :=
  mem_FP_comp (mem_FP_comp (IntegralBlockPowerBits.requeryEntry_FP _ (IntegralCriticalFlatMomentBits.packet_FP P a)) hr)
    (entryWriter_FP P a S h)

theorem requery_original (f : List Bool → List Bool) (p : List Bool) :
    original (IntegralBlockPowerBits.requeryEntry f p) = f (original p) := by
  simp only [IntegralBlockPowerBits.requeryEntry, original, pairFst_pair]

theorem row_parent (S : Source) (p : List Bool) : original (rowQuery S p) = original (original p) := by
  simp only [rowQuery, sourceContext, original, pairFst_pair]
theorem column_parent (S : Source) (p : List Bool) : original (columnQuery S p) = original (original p) := by
  simp only [columnQuery, sourceContext, original, pairFst_pair]
theorem matrix_parent (S : Source) (p : List Bool) : original (matrixQuery S p) = original (original p) := by
  simp only [matrixQuery, sourceContext, original, pairFst_pair]

theorem task_parent (P : Parameters) (route : List Bool → List Bool)
    (hr : ∀ p, original (route p) = original (original p)) (p : List Bool) :
    original (route (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet P) p)) = original p := by
  rw [hr, requery_original, IntegralCriticalFlatMomentBits.packet_parent]

theorem task_frame (P : Parameters) (S : Source) (route : List Bool → List Bool)
    (hr : ∀ p, original (route p) = original (original p)) (p : List Bool) (hp : 0 < phase (original p)) :
    IntegralMixedRoutineTaskBits.Frame P (original p) (task P S route p) := by
  have HF := entryWriter_frame P S (route (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet P) p))
    (by rw [task_parent P route hr]; exact hp)
  simpa only [task, Function.comp_apply, task_parent P route hr p] using HF

def rowTask (P : Parameters) (S : Source) := task P S (rowQuery S)
def columnTask (P : Parameters) (S : Source) := task P S (columnQuery S)
def matrixTask (P : Parameters) (S : Source) := task P S (matrixQuery S)

theorem rowTask_FP (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S) : rowTask P S ∈ FP :=
  task_FP P a S h _ (rowQuery_FP S h)
theorem columnTask_FP (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S) : columnTask P S ∈ FP :=
  task_FP P a S h _ (columnQuery_FP S h)
theorem matrixTask_FP (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S) : matrixTask P S ∈ FP :=
  task_FP P a S h _ (matrixQuery_FP S h)

end LeanCanny.Algebra.IntegralMixedPscMomentTasks
