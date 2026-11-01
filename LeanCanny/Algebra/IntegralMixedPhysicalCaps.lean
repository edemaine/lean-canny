/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalTaskBackend
public import LeanCanny.Algebra.IntegralCriticalFlatMoment
/-! # Actual physical-source dimensions fit the original task cap

The source uses the actual old prefix rank, without any formal digit.
Task birth is clipped at cap plus one, so the rank bound holds on every
word, including malformed queries. Only original root metadata is used.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalCaps
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits
set_option backward.isDefEq.respectTransparency false

structure RootGeometry (P : Parameters) (F : Family) : Prop where
  ambient : ∀ q, F.ambient (IntegralMixedPhysicalTaskBits.saved P q) ≤ P.ambient (RankedHistoryTask.root q)
  degree : ∀ q, (F.spatial (IntegralMixedPhysicalTaskBits.saved P q)).degree ≤ P.degree (RankedHistoryTask.root q)
  sourceWidth : ∀ q, (F.spatial (IntegralMixedPhysicalTaskBits.saved P q)).degree.size ≤ P.sourceWidth (RankedHistoryTask.root q)
  width : ∀ q, F.width (IntegralMixedPhysicalTaskBits.saved P q) = P.width (RankedHistoryTask.root q)
  birth : ∀ q, F.birth (IntegralMixedPhysicalTaskBits.saved P q) = birth P q

theorem rank_le (P : Parameters) (F : Family) (h : RootGeometry P F)
    (q : List Bool) :
    (IntegralMixedPhysicalTaskBits.source P F).rank q ≤ rankCap P (RankedHistoryTask.root q) := by
  change count (F.birth (IntegralMixedPhysicalTaskBits.saved P q))
    (F.width (IntegralMixedPhysicalTaskBits.saved P q)) ≤ _
  rw [h.birth, h.width]
  exact Nat.pow_le_pow_right (Nat.two_pow_pos _) (min_le_right _ _)

theorem free_le (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool) :
    (IntegralMixedPhysicalTaskBits.source P F).free q ≤ P.ambient (RankedHistoryTask.root q) + 1 :=
  (Nat.add_le_add_right (Nat.sub_le _ _) 1).trans (Nat.add_le_add_right (h.ambient q) 1)

theorem degree_le (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool) :
    (IntegralMixedPhysicalTaskBits.source P F).degree q ≤ P.degree (RankedHistoryTask.root q) := h.degree q

theorem dimension_le (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool) :
    PurePowerReductionBounds.dimension ((IntegralMixedPhysicalTaskBits.source P F).free q)
      ((IntegralMixedPhysicalTaskBits.source P F).degree q) ≤
        PurePowerReductionBounds.dimension (P.ambient (RankedHistoryTask.root q) + 1) (P.degree (RankedHistoryTask.root q)) :=
  IntegralCriticalFactorCeiling.dimension_mono (free_le P F h q) (degree_le P F h q)

theorem rank_cap (P : Parameters) (F : Family) (h : RootGeometry P F)
    (q : List Bool) :
    (IntegralMixedPhysicalTaskBits.source P F).rank q ≤ numericCap P (RankedHistoryTask.root q) :=
  (rank_le P F h q).trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.1

theorem source_grid_cap (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool) :
    count ((IntegralMixedPhysicalTaskBits.source P F).arity q) ((IntegralMixedPhysicalTaskBits.source P F).sourceWidth q) ≤
      numericCap P (RankedHistoryTask.root q) :=
  IntegralCriticalQueryBounds.source_grid_le_of_le _ _ _ _ _ _ _ _ (Nat.add_le_add_right (h.ambient q) 1) (h.sourceWidth q)

theorem coefficient_block_cap (P : Parameters) (F : Family) (h : RootGeometry P F)
    (q : List Bool) :
    IntegralCoefficientBlocks.dimension
      (PurePowerReductionBounds.dimension ((IntegralMixedPhysicalTaskBits.source P F).free q)
        ((IntegralMixedPhysicalTaskBits.source P F).degree q)) ((IntegralMixedPhysicalTaskBits.source P F).rank q) ≤
      numericCap P (RankedHistoryTask.root q) :=
  IntegralCriticalQueryBounds.coefficient_block_le_of_le _ _ _ _ _ _ _ _
    (dimension_le P F h q) (rank_le P F h q)

theorem moment_block_cap (P : Parameters) (F : Family) (h : RootGeometry P F)
    (q : List Bool) :
    (PurePowerReductionBounds.dimension ((IntegralMixedPhysicalTaskBits.source P F).free q)
      ((IntegralMixedPhysicalTaskBits.source P F).degree q) + 2) * (IntegralMixedPhysicalTaskBits.source P F).rank q ≤
        numericCap P (RankedHistoryTask.root q) :=
  IntegralCriticalQueryBounds.moment_block_le_of_le _ _ _ _ _ _ _ _
    (dimension_le P F h q) (rank_le P F h q)

end LeanCanny.Algebra.IntegralMixedPhysicalCaps
