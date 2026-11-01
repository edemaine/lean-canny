/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueGramProductNative

/-! # Bounded native term requests for the actual negative Gram sum -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueGramSumTasks
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps
open scoped Classical

noncomputable def rows (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  IntegralMixedValueMacaulayMatrix.rows (IntegralMixedVirtualTaskBits.family P F) q
noncomputable def count (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  rows P F q * IntegralMixedValueGramProductTasks.rank P F q

theorem rows_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (rows P F) :=
  (IntegralMixedValueGramEntry.controls _ _ (IntegralMixedVirtualTaskBits.metadata P a F h)).rows
theorem count_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (count P F) :=
  (rows_binary P a F h).mul (IntegralMixedValueGramProductTasks.rank_binary P a F h)

theorem rows_lt_scalar (P : Parameters) (F : Family) (q : List Bool) :
    rows P F q < 2 ^ F.width (IntegralMixedVirtualTaskBits.saved P q) := by
  have HD := IntegralMixedValueTaskBounds.dimension_lt_scalar (IntegralMixedVirtualTaskBits.family P F) q
  change (_ + 3) * _ < _ at HD
  apply lt_of_le_of_lt _ HD
  change ((IntegralMixedVirtualTaskBits.family P F).ambient q -
    ((IntegralMixedVirtualTaskBits.family P F).rule q).critical.offset.val + 1 + 2) * _ ≤ _
  apply Nat.mul_le_mul_right
  omega

theorem count_cap (P : Parameters) (F : Family) (g : RootGeometry P F) (q : List Bool) (hv : valid P q) :
    count P F q ≤ numericCap P (RankedHistoryTask.root q) := by
  have HS : 2 ^ F.width (IntegralMixedVirtualTaskBits.saved P q) ≤ rankCap P (RankedHistoryTask.root q) := by
    rw [g.width]
    change 2 ^ P.width _ ≤ (2 ^ P.width _) ^ (P.cap _ + 1)
    conv_lhs => rw [← pow_one (2 ^ P.width (RankedHistoryTask.root q))]
    exact Nat.pow_le_pow_right (Nat.two_pow_pos _) (by omega)
  have HR := auxiliary_rank_le P F g q hv 2 (by decide)
  have HH : count P F q ≤ (rankCap P (RankedHistoryTask.root q)) ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul ((rows_lt_scalar P F q).le.trans HS) HR
  apply HH.trans
  apply le_trans _ (IntegralCriticalQueryBounds.retained_grid_le _ _ _ _ _ _ _ _)
  apply Nat.pow_le_pow_right
  · exact Nat.pow_pos (Nat.two_pow_pos _)
  · omega

noncomputable def query (P : Parameters) : List Bool → List Bool :=
  IntegralMixedValueFieldQuery.query P pairFst .pscEntry .criticalCoefficient .slot10 (fun z => Nat.fromBitsLE (pairSnd z))
theorem query_FP (P : Parameters) (a : Access P) : query P ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a pairFst pairFst_mem_FP _ _ _ _ (BinaryFn.fromBits pairSnd_mem_FP)

theorem query_saved (P : Parameters) (q : List Bool) (k : ℕ) :
    IntegralMixedVirtualTaskBits.saved P (query P (pair q (BinaryNatCode.encode k))) = IntegralMixedVirtualTaskBits.saved P q := by
  have H := IntegralMixedValueFieldQuery.query_saved P pairFst .pscEntry .criticalCoefficient .slot10
    (fun z => Nat.fromBitsLE (pairSnd z)) (pair q (BinaryNatCode.encode k)) (by decide)
  simpa only [query, pairFst_pair] using H
theorem query_modulus (P : Parameters) (q : List Bool) (k : ℕ) :
    modulus P (query P (pair q (BinaryNatCode.encode k))) = modulus P q := by
  have H := IntegralMixedValueFieldQuery.query_modulus P pairFst .pscEntry .criticalCoefficient .slot10
    (fun z => Nat.fromBitsLE (pairSnd z)) (pair q (BinaryNatCode.encode k)) (by decide)
  simpa only [query, pairFst_pair] using H
theorem rank_query (P : Parameters) (F : Family) (q : List Bool) (k : ℕ) :
    IntegralMixedValueGramProductTasks.rank P F (query P (pair q (BinaryNatCode.encode k))) =
      IntegralMixedValueGramProductTasks.rank P F q := by
  change FixedWidthPolynomial.count (F.birth (IntegralMixedVirtualTaskBits.saved P _) + 2)
      (F.width (IntegralMixedVirtualTaskBits.saved P _)) = _
  rw [query_saved]
  rfl
theorem query_get (P : Parameters) (q : List Bool) (k : ℕ) (hk : k ≤ numericCap P (RankedHistoryTask.root q)) (f : Field) :
    get P f (query P (pair q (BinaryNatCode.encode k))) =
      if f = .slot14 then 2 else if f = .slot10 then k else get P f q := by
  rw [query, IntegralMixedValueFieldQuery.query_get]
  simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, min_eq_left hk]
  rfl

theorem query_frame (P : Parameters) (q : List Bool) (k : ℕ)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 2) (hp : phase q = 26) :
    IntegralMixedRoutineTaskBits.Frame P q (query P (pair q (BinaryNatCode.encode k))) := by
  have HF := IntegralMixedValueFieldQuery.query_frame_phase P pairFst .pscEntry .criticalCoefficient .slot10
    (fun z => Nat.fromBitsLE (pairSnd z)) (pair q (BinaryNatCode.encode k))
    (by simpa only [pairFst_pair, IntegralMixedRoutineTaskBits.Routine.code] using hr)
    (by simp only [pairFst_pair]; change 25 < phase q; omega)
  simpa only [query, pairFst_pair] using HF

end LeanCanny.Algebra.IntegralMixedValueGramSumTasks
