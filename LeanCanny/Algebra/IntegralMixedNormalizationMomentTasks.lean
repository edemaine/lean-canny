/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeMomentPower
/-! # Fresh normalization top-entry requests from augmented rows and columns -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationMomentTasks
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false

abbrev Source := IntegralBerkowitzBlockBits.Source

def task (P : Parameters) (_S : Source) (route : List Bool → List Bool) : List Bool → List Bool :=
  IntegralMixedNormalizationTopBits.entryTask P .clearedHeight ∘ route ∘
    IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet P)

theorem task_FP (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (S : Source)
    (_h : IntegralBerkowitzBlockBits.Access S) (route : List Bool → List Bool) (hr : route ∈ FP) : task P S route ∈ FP :=
  mem_FP_comp (mem_FP_comp (IntegralBlockPowerBits.requeryEntry_FP _ (IntegralCriticalFlatMomentBits.packet_FP P a)) hr)
    (IntegralMixedNormalizationTopBits.entryTask_FP P a .clearedHeight)

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
    (hr : ∀ p, original (route p) = original (original p)) (p : List Bool) (hp : 2 < phase (original p)) :
    IntegralMixedRoutineTaskBits.Frame P (original p) (task P S route p) := by
  have HF := IntegralMixedNormalizationTopBits.entryTask_frame P .clearedHeight
    (route (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet P) p))
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

end LeanCanny.Algebra.IntegralMixedNormalizationMomentTasks
