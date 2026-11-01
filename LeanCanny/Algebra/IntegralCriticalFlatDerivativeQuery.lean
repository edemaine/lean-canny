/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatOriginalCoefficient
public import LeanCanny.Algebra.IntegralDerivativeController

/-! # Fresh original-coefficient tasks for bumped derivative queries -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatDerivativeQuery
open LeanCanny.Encoding LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks
attribute [local irreducible] IntegralCriticalFlatGridBits.writer IntegralCriticalFlatMatrixQuery.writer

def writer (P : IntegralCriticalHistoryTask.Parameters) (p : List Bool) : List Bool :=
  IntegralCriticalFlatGridBits.writer P .originalCoefficient
    (pair (IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient (pairFst p)) (pairSnd p))

theorem writer_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P) : writer P ∈ FP :=
  mem_FP_comp (f := fun p => pair (IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient (pairFst p)) (pairSnd p))
    (g := IntegralCriticalFlatGridBits.writer P .originalCoefficient)
    (mem_FP_pair (mem_FP_comp (f := pairFst) (g := IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient)
      pairFst_mem_FP (IntegralCriticalFlatMatrixQuery.writer_FP P a .originalCoefficient)) pairSnd_mem_FP)
    (IntegralCriticalFlatGridBits.writer_FP P a .originalCoefficient)

theorem writer_root (P : IntegralCriticalHistoryTask.Parameters) (p : List Bool) :
    RankedHistoryTask.root (writer P p) = RankedHistoryTask.root (IntegralDerivativeBits.original p) := by
  simp only [writer, IntegralCriticalFlatGridBits.writer_root, pairFst_pair, IntegralCriticalFlatMatrixQuery.writer_root,
    IntegralDerivativeBits.original]

theorem writer_birth (P : IntegralCriticalHistoryTask.Parameters) (p : List Bool) :
    IntegralCriticalHistoryTask.birth P (writer P p) = IntegralCriticalHistoryTask.birth P (IntegralDerivativeBits.original p) := by
  simp only [writer, IntegralCriticalFlatGridBits.writer_birth, pairFst_pair, IntegralCriticalFlatMatrixQuery.writer_birth,
    IntegralDerivativeBits.original]

theorem writer_phase (P : IntegralCriticalHistoryTask.Parameters) (p : List Bool) :
    IntegralCriticalHistoryTask.phase (writer P p) = 0 := by
  simpa only [writer, IntegralCriticalHistoryTask.Phase.code] using IntegralCriticalFlatGridBits.writer_phase P .originalCoefficient
    (pair (IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient (pairFst p)) (pairSnd p))

theorem writer_modulus (P : IntegralCriticalHistoryTask.Parameters) (p : List Bool) :
    IntegralCriticalHistoryTask.modulus P (writer P p) = IntegralCriticalHistoryTask.modulus P (IntegralDerivativeBits.original p) := by
  simp only [writer, IntegralCriticalFlatGridBits.writer_modulus, pairFst_pair,
    IntegralCriticalFlatMatrixQuery.writer_modulus, IntegralDerivativeBits.original]

theorem writer_get (P : IntegralCriticalHistoryTask.Parameters) (p : List Bool) (f : IntegralCriticalHistoryTask.Field) :
    IntegralCriticalHistoryTask.get P f (writer P p) =
      if f = .sourceIndex then min (Nat.fromBitsLE (pairSnd p))
        (IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root (IntegralDerivativeBits.original p))) else
      if f = .row then min (Nat.fromBitsLE (pairFst (pairSnd (pairFst p))))
        (IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root (IntegralDerivativeBits.original p))) else
      if f = .col then min (Nat.fromBitsLE (pairSnd (pairSnd (pairFst p))))
        (IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root (IntegralDerivativeBits.original p))) else
        IntegralCriticalHistoryTask.get P f (IntegralDerivativeBits.original p) := by
  rw [writer, IntegralCriticalFlatGridBits.writer_get]
  simp only [pairFst_pair, pairSnd_pair, IntegralCriticalFlatMatrixQuery.writer_root]
  by_cases hf : f = .sourceIndex
  · simp only [hf, ite_true]
    rfl
  · rw [ite_eq_right hf, IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [ite_eq_right hf, IntegralDerivativeBits.original]

theorem writer_packet_fields (P : IntegralCriticalHistoryTask.Parameters) (c : List Bool) (k r t : ℕ)
    (hk : k ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c))
    (hr : r ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c))
    (ht : t ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c)) :
    let w := writer P (pair (IntegralClearedCoefficientBits.context c r t) (BinaryNatCode.encode k))
    IntegralCriticalHistoryTask.get P .sourceIndex w = k ∧
      IntegralCriticalHistoryTask.get P .row w = r ∧ IntegralCriticalHistoryTask.get P .col w = t := by
  dsimp only
  simp only [writer_get, IntegralDerivativeBits.original, IntegralClearedCoefficientBits.context,
    pairFst_pair, pairSnd_pair, reduceCtorEq, ite_true, ite_false, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact ⟨min_eq_left hk, min_eq_left hr, min_eq_left ht⟩

theorem writer_other (P : IntegralCriticalHistoryTask.Parameters) (p : List Bool)
    (f : IntegralCriticalHistoryTask.Field) (hk : f ≠ .sourceIndex) (hr : f ≠ .row) (ht : f ≠ .col) :
    IntegralCriticalHistoryTask.get P f (writer P p) = IntegralCriticalHistoryTask.get P f (IntegralDerivativeBits.original p) := by
  rw [writer_get, ite_eq_right hk, ite_eq_right hr, ite_eq_right ht]

theorem writer_tasks (P : IntegralCriticalHistoryTask.Parameters) (r p : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P r (IntegralDerivativeBits.original p)) :
    IntegralCriticalHistoryTask.Tasks P r (writer P p) := by
  apply IntegralCriticalFlatGridBits.writer_tasks
  simp only [pairFst_pair]
  exact IntegralCriticalFlatMatrixQuery.writer_tasks P .originalCoefficient r (pairFst p) ht

theorem writer_lower_rank (P : IntegralCriticalHistoryTask.Parameters) (p : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .derivativeCoefficient (IntegralDerivativeBits.original p)) :
    IntegralCriticalHistoryTask.rank P (writer P p) < IntegralCriticalHistoryTask.rank P (IntegralDerivativeBits.original p) := by
  have HB := writer_birth P p
  have HP := writer_phase P p
  unfold IntegralCriticalHistoryTask.birth at HB
  unfold IntegralCriticalHistoryTask.phase at HP
  change IntegralCriticalHistoryTask.phase (IntegralDerivativeBits.original p) = 1 at hp
  unfold IntegralCriticalHistoryTask.phase at hp
  unfold IntegralCriticalHistoryTask.rank RankedHistoryTask.rank
  rw [HB, HP, hp]
  omega

theorem writer_length (P : IntegralCriticalHistoryTask.Parameters) (p : List Bool) :
    (writer P p).length ≤ IntegralCriticalHistoryTask.wordBudget P (IntegralDerivativeBits.original p) := by
  have H := IntegralCriticalFlatGridBits.writer_length P .originalCoefficient
    (pair (IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient (pairFst p)) (pairSnd p))
  simpa only [writer, IntegralDerivativeBits.original, pairFst_pair, IntegralCriticalHistoryTask.wordBudget, RankedHistoryTask.wordBudget,
    IntegralCriticalFlatMatrixQuery.writer_root] using H

end LeanCanny.Algebra.IntegralCriticalFlatDerivativeQuery
