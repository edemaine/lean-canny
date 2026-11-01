/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralReductionLowerPacket
public import LeanCanny.Algebra.IntegralMixedPhysicalUpperSources
public import LeanCanny.Algebra.IntegralMixedPhysicalSpatialModel
/-! # Actual physical lower replies under the reduction-entry writer -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalLowerChildBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalUpperBits IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false

theorem low_snapshot (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) (p : List Bool) :
    (relativeAccess P a F h).low p = IntegralMixedPhysicalSpatialBits.lowerEntryAt F
      (IntegralMixedPhysicalTaskBits.saved P (original p))
      (Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex p)) (Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex p))
      (Nat.fromBitsLE (basisRowCode p)) (Nat.fromBitsLE (basisColCode p))
      (modulus P (original p)) (modulus_ne_zero P (original p)) := rfl

attribute [local irreducible] relative relativeAccess IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

noncomputable def input (P : Parameters) (F : Family) := IntegralReductionLowerPacketBits.input P (relative P F)
noncomputable def child (P : Parameters) (F : Family) (q : List Bool) := IntegralCriticalFlatLowerQuery.writer P (input P F q)

theorem input_parent (P : Parameters) (F : Family) (q : List Bool) : original (input P F q) = q :=
  IntegralReductionLowerPacketBits.input_parent P (relative P F) q

theorem input_bounds (P : Parameters) (F : Family) (h : IntegralMixedPhysicalCaps.RootGeometry P F)
    (q : List Bool) :
    Nat.fromBitsLE (basisRowCode (input P F q)) ≤ numericCap P (RankedHistoryTask.root q) ∧
    Nat.fromBitsLE (basisColCode (input P F q)) ≤ numericCap P (RankedHistoryTask.root q) ∧
    Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex (input P F q)) ≤ numericCap P (RankedHistoryTask.root q) ∧
    Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex (input P F q)) ≤ numericCap P (RankedHistoryTask.root q) := by
  have HR : (relative P F).rank q ≤ numericCap P (RankedHistoryTask.root q) := by
    unfold relative
    exact IntegralMixedPhysicalCaps.rank_cap P F h q
  have HP : 0 < (relative P F).rank q := (Nat.zero_le ((relative P F).basisRow q).val).trans_lt ((relative P F).basisRow q).isLt
  have HF : (relative P F).layout.arity q ≤ numericCap P (RankedHistoryTask.root q) := by
    have HC : P.ambient (RankedHistoryTask.root q) + 1 ≤ numericCap P (RankedHistoryTask.root q) := by
      unfold numericCap
      exact (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.1
    unfold relative
    exact (IntegralMixedPhysicalCaps.free_le P F h q).trans HC
  have HG : count ((relative P F).layout.arity q) ((relative P F).layout.width q) ≤ numericCap P (RankedHistoryTask.root q) := by
    have HC : PurePowerReductionBounds.dimension (P.ambient (RankedHistoryTask.root q) + 1)
        (P.degree (RankedHistoryTask.root q)) ≤ numericCap P (RankedHistoryTask.root q) := by
      unfold numericCap
      exact IntegralCriticalQueryBounds.spatial_grid_le _ _ _ _ _ _ _ _
    unfold relative
    exact (IntegralMixedPhysicalCaps.dimension_le P F h q).trans HC
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [input, IntegralReductionLowerPacketBits.input_row]
    exact (Nat.mod_lt _ HP).le.trans HR
  · rw [input, IntegralReductionLowerPacketBits.input_col]
    exact (Nat.mod_lt _ HP).le.trans HR
  · exact (IntegralReductionLowerPacketBits.input_derivative_le P (relative P F) q).trans HF
  · exact (IntegralReductionLowerPacketBits.input_target_lt P (relative P F) q).le.trans HG

theorem child_root (P : Parameters) (F : Family) (q : List Bool) : RankedHistoryTask.root (child P F q) = RankedHistoryTask.root q :=
  (IntegralCriticalFlatLowerQuery.writer_root P _).trans (congrArg RankedHistoryTask.root (input_parent P F q))
theorem child_birth (P : Parameters) (F : Family) (q : List Bool) : birth P (child P F q) = birth P q :=
  (IntegralCriticalFlatLowerQuery.writer_birth P _).trans (congrArg (birth P) (input_parent P F q))
theorem child_modulus (P : Parameters) (F : Family) (q : List Bool) : modulus P (child P F q) = modulus P q :=
  (IntegralCriticalFlatLowerQuery.writer_modulus P _).trans (congrArg (modulus P) (input_parent P F q))
theorem child_context (P : Parameters) (F : Family) (q : List Bool) : get P .slot15 (child P F q) = get P .slot15 q := by
  simp only [child, IntegralCriticalFlatLowerQuery.writer_get, reduceCtorEq, ite_false, input_parent]

theorem child_fields (P : Parameters) (F : Family) (h : IntegralMixedPhysicalCaps.RootGeometry P F)
    (q : List Bool) :
    get P .derivative (child P F q) = Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex (input P F q)) ∧
    get P .target (child P F q) = Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex (input P F q)) ∧
    get P .row (child P F q) = Nat.fromBitsLE (basisRowCode (input P F q)) ∧
    get P .col (child P F q) = Nat.fromBitsLE (basisColCode (input P F q)) := by
  have HB := input_bounds P F h q
  simp only [child, IntegralCriticalFlatLowerQuery.writer_get, input_parent, reduceCtorEq, ite_true, ite_false]
  exact ⟨min_eq_left HB.2.2.1, min_eq_left HB.2.2.2, min_eq_left HB.1, min_eq_left HB.2.1⟩

theorem child_value (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (q : List Bool) :
    IntegralMixedPhysicalSnapshotBits.lower P F (child P F q) = (relativeAccess P a F h).low (input P F q) := by
  have HF := child_fields P F g q
  have H := IntegralMixedPhysicalSpatialBits.lower_transport P F q (child P F q)
    (Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex (input P F q)))
    (Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex (input P F q)))
    (Nat.fromBitsLE (basisRowCode (input P F q))) (Nat.fromBitsLE (basisColCode (input P F q)))
    (child_root P F q) (child_birth P F q) (child_context P F q) (child_modulus P F q)
    HF.1 HF.2.1 HF.2.2.1 HF.2.2.2
  exact H.trans (by simpa only [input_parent] using (low_snapshot P a F h (input P F q)).symm)

end LeanCanny.Algebra.IntegralMixedPhysicalLowerChildBits
