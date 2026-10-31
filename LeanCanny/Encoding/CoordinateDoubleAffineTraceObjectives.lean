/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceStages

/-! # One native objective reader for every recursive coordinate frame -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
open LeanCanny.Computation
open FlatAffineFullSourceTower (stage)
set_option backward.isDefEq.respectTransparency false

def seedCoordinate (d old : List Bool → ℕ) (u : List Bool) : ℕ := old (stage u (d u))

theorem seedCoordinate_unary {d old : List Bool → ℕ} (hd : UnaryFn d) (ho : UnaryFn old) :
    UnaryFn (seedCoordinate d old) :=
  ho.comp (mem_FP_pair id_mem_FP (BinaryFn.ofUnary hd).bits_mem_FP)

def sourceStage (q : List Bool) : List Bool :=
  stage (base (LeanCanny.pairFst q)) (Nat.fromBitsLE (LeanCanny.pairSnd q))

theorem sourceStage_FP : sourceStage ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (BinaryFn.fromBits pairSnd_mem_FP).bits_mem_FP

def objective (d old : List Bool → ℕ) (q : List Bool) : ℕ :=
  if Nat.fromBitsLE (LeanCanny.pairSnd q) < d (base (LeanCanny.pairFst q)) then old (sourceStage q) else
    seedCoordinate d old (base (LeanCanny.pairFst q)) +
      completed (d (base (LeanCanny.pairFst q))) (history (LeanCanny.pairFst q))
        (Nat.fromBitsLE (LeanCanny.pairSnd q))

theorem objective_unary {d old : List Bool → ℕ} (hd : UnaryFn d) (ho : UnaryFn old) : UnaryFn (objective d old) := by
  have hs : (fun q => base (LeanCanny.pairFst q)) ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have ht : (fun q => history (LeanCanny.pairFst q)) ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hk := BinaryFn.fromBits pairSnd_mem_FP
  exact UnaryFn.ite (hk.lt (BinaryFn.ofUnary (hd.comp hs))) (ho.comp sourceStage_FP)
    (((seedCoordinate_unary hd ho).comp hs).add (completed_unary (hd.comp hs) ht hk))

theorem objective_stage (d old : List Bool → ℕ) (q : List Bool) (k : ℕ) :
    objective d old (stage q k) = objectiveAt (d (base q))
      (fun i => old (stage (base q) i)) (history q) k := by
  simp only [objective, sourceStage, objectiveAt, seedCoordinate, stage,
    LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem objective_current (d old : List Bool → ℕ) (q : List Bool) :
    objective d old (stage q (depth d q)) = coordinate (seedCoordinate d old) q :=
  (objective_stage d old q _).trans (objectiveAt_depth _ _ _)

theorem child_objective_stage (midpoint : Bool) (d old : List Bool → ℕ) (q : List Bool) (k : ℕ) :
    CoordinateDoubleAffineChildRecords.objective midpoint d old (stage q k) =
      if k < d q then old (stage q k) else old (stage q (d q)) +
        if k = CoordinateDoubleAffineChildRecords.childDepth midpoint d q then 1 else 0 := by
  simp only [CoordinateDoubleAffineChildRecords.objective, CoordinateDoubleAffineChildRecords.originalStage,
    stage, LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem objective_append (midpoint : Bool) (d old : List Bool → ℕ) (q : List Bool) (k : ℕ)
    (hk : k ≤ depth d (append midpoint q)) :
    objective d old (stage (append midpoint q) k) =
      CoordinateDoubleAffineChildRecords.objective midpoint (depth d) (objective d old) (stage q k) := by
  rw [objective_stage, base_append, history_append, child_objective_stage]
  simp only [objective_stage, depth, CoordinateDoubleAffineChildRecords.childDepth]
  have hk' : k ≤ d (base q) + offset (history q ++ [midpoint]) := by
    simpa only [depth, base_append, history_append] using hk
  have H := objectiveAt_append (d (base q)) (fun i => old (stage (base q) i)) (history q) midpoint k hk'
  rw [offset_append] at H
  simpa only [Nat.add_assoc] using H

end LeanCanny.Encoding.CoordinateDoubleAffineTrace
