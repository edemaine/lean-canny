/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualTaskBackend
public import LeanCanny.Algebra.IntegralCriticalFlatMoment
/-! # Actual virtual-source dimensions fit the original task cap

The root geometry refers only to original source metadata. A valid producer
prefix leaves room for two formal nilpotent digits under the same cap.
Neither digit creates a physical sample or changes the spatial degree.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualCaps
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

structure RootGeometry (P : Parameters) (F : Family) : Prop where
  ambient : ∀ q, F.ambient (IntegralMixedVirtualTaskBits.saved P q) ≤ P.ambient (RankedHistoryTask.root q)
  degree : ∀ q, (F.spatial (IntegralMixedVirtualTaskBits.saved P q)).degree ≤ P.degree (RankedHistoryTask.root q)
  sourceWidth : ∀ q, (F.spatial (IntegralMixedVirtualTaskBits.saved P q)).degree.size ≤ P.sourceWidth (RankedHistoryTask.root q)
  width : ∀ q, F.width (IntegralMixedVirtualTaskBits.saved P q) = P.width (RankedHistoryTask.root q)
  birth : ∀ q, F.birth (IntegralMixedVirtualTaskBits.saved P q) = birth P q

def valid (P : Parameters) (q : List Bool) : Prop := birth P q < P.cap (RankedHistoryTask.root q)

theorem valid_FP (P : Parameters) (a : Access P) : FPPred (valid P) :=
  (BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (birthCap_unary P a))).lt
    ((BinaryFn.ofUnary a.cap).comp RankedHistoryTask.root_FP)

theorem auxiliary_rank_le (P : Parameters) (F : Family) (h : RootGeometry P F)
    (q : List Bool) (hv : valid P q) (d : ℕ) (hd : d ≤ 2) :
    count (F.birth (IntegralMixedVirtualTaskBits.saved P q) + d)
      (F.width (IntegralMixedVirtualTaskBits.saved P q)) ≤ rankCap P (RankedHistoryTask.root q) := by
  rw [h.birth, h.width]
  exact Nat.pow_le_pow_right (Nat.two_pow_pos _) (by change birth P q < P.cap _ at hv; omega)

theorem rank_le (P : Parameters) (F : Family) (h : RootGeometry P F)
    (q : List Bool) (hv : valid P q) :
    (IntegralMixedVirtualTaskBits.source P F).rank q ≤ rankCap P (RankedHistoryTask.root q) :=
  auxiliary_rank_le P F h q hv 1 (by decide)

theorem free_le (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool) :
    (IntegralMixedVirtualTaskBits.source P F).free q ≤ P.ambient (RankedHistoryTask.root q) + 1 :=
  (Nat.add_le_add_right (Nat.sub_le _ _) 1).trans (Nat.add_le_add_right (h.ambient q) 1)

theorem degree_le (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool) :
    (IntegralMixedVirtualTaskBits.source P F).degree q ≤ P.degree (RankedHistoryTask.root q) := h.degree q

theorem dimension_le (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool) :
    PurePowerReductionBounds.dimension ((IntegralMixedVirtualTaskBits.source P F).free q)
      ((IntegralMixedVirtualTaskBits.source P F).degree q) ≤
        PurePowerReductionBounds.dimension (P.ambient (RankedHistoryTask.root q) + 1) (P.degree (RankedHistoryTask.root q)) :=
  IntegralCriticalFactorCeiling.dimension_mono (free_le P F h q) (degree_le P F h q)

theorem rank_cap (P : Parameters) (F : Family) (h : RootGeometry P F)
    (q : List Bool) (hv : valid P q) :
    (IntegralMixedVirtualTaskBits.source P F).rank q ≤ numericCap P (RankedHistoryTask.root q) :=
  (rank_le P F h q hv).trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.1

theorem source_grid_cap (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool) :
    count ((IntegralMixedVirtualTaskBits.source P F).arity q) ((IntegralMixedVirtualTaskBits.source P F).sourceWidth q) ≤
      numericCap P (RankedHistoryTask.root q) :=
  IntegralCriticalQueryBounds.source_grid_le_of_le _ _ _ _ _ _ _ _ (Nat.add_le_add_right (h.ambient q) 1) (h.sourceWidth q)

theorem coefficient_block_cap (P : Parameters) (F : Family) (h : RootGeometry P F)
    (q : List Bool) (hv : valid P q) :
    IntegralCoefficientBlocks.dimension
      (PurePowerReductionBounds.dimension ((IntegralMixedVirtualTaskBits.source P F).free q)
        ((IntegralMixedVirtualTaskBits.source P F).degree q)) ((IntegralMixedVirtualTaskBits.source P F).rank q) ≤
      numericCap P (RankedHistoryTask.root q) :=
  IntegralCriticalQueryBounds.coefficient_block_le_of_le _ _ _ _ _ _ _ _
    (dimension_le P F h q) (rank_le P F h q hv)

theorem moment_block_cap (P : Parameters) (F : Family) (h : RootGeometry P F)
    (q : List Bool) (hv : valid P q) :
    (PurePowerReductionBounds.dimension ((IntegralMixedVirtualTaskBits.source P F).free q)
      ((IntegralMixedVirtualTaskBits.source P F).degree q) + 2) * (IntegralMixedVirtualTaskBits.source P F).rank q ≤
        numericCap P (RankedHistoryTask.root q) :=
  IntegralCriticalQueryBounds.moment_block_le_of_le _ _ _ _ _ _ _ _
    (dimension_le P F h q) (rank_le P F h q hv)

end LeanCanny.Algebra.IntegralMixedVirtualCaps
