/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleDirectionPacket
public import LeanCanny.Connectivity.CriticalSampleOriginalSlice

/-! # Selected common directions make the original child systems regular

The packet adapter preserves the exact normalized direction used by the
native search. Its acceptance supplies the critical-regularity premise of
the original-slice component sampling and connectivity reductions.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CriticalSampleSelectedDirection
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding LeanCanny.ETR MvPolynomial
open BoundedCriticalSampleDirectionChoice (Inputs width direction record Good)
open BoundedCriticalSampleDirectionPacket
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair pairFst pairSnd BoundedCriticalSampleBlockScaling.original

private def vectorData {n : ℕ} (w : ℕ) (bits : List Bool) (i : Fin n) : ℝ :=
  FixedWidthQuery.coordinate (fun _ => w) (fun _ => bits) [] i.val

private theorem normalized_vector (F : Inputs) (c r : List Bool) :
    (vectorData (n := F.free c + 1) (width F c) (normalized F (pair c r))) =
      Fin.cons 1 (fun i => (direction F c r i.val : ℝ)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have H := normalized_zero F c r
    simp only [FixedWidthQuery.coordinate, Function.comp_apply, pairFst_pair] at H
    simpa only [vectorData, FixedWidthQuery.coordinate, Fin.val_zero, Fin.cons_zero, Nat.cast_one]
      using congrArg (fun k : ℕ => (k : ℝ)) H
  · have H := normalized_succ F c r j.val
    simp only [FixedWidthQuery.coordinate, Function.comp_apply, pairFst_pair] at H
    simpa only [vectorData, FixedWidthQuery.coordinate, Fin.val_succ, Fin.cons_succ,
      direction, Int.cast_natCast] using congrArg (fun k : ℕ => (k : ℝ)) H

private theorem child_direction_data (F : Inputs) (u : List Bool) :
    CriticalSampleChildCoverage.direction (child F) u =
      vectorData (width F (pairFst u)) (pairSnd u) := by
  funext i
  have hi : i.val < F.free (pairFst u) + 1 := i.isLt
  simp only [CriticalSampleChildCoverage.direction, child, BoundedCriticalSampleBlockCriticalSource.direction,
    FixedWidthQuery.entry, hi, ite_true, vectorData, FixedWidthQuery.coordinate, Function.comp_apply]

theorem critical_regular (F : Inputs) (u : List Bool)
    (hpacket : pairSnd u = normalized F (pair (pairFst u) (record F (pairFst u))))
    (hgood : Good F (pairFst u) (record F (pairFst u)))
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :
    ∀ y, (∀ i, (ProjectionCriticalFamily.spatialEquation (CriticalSampleOriginalSlice.polynomial (child F) u p)
      ((child F).pivot u) (CriticalSampleChildCoverage.direction (child F) u) i).eval y = 0) →
        (fderiv ℝ (fun z => fun i => (ProjectionCriticalFamily.spatialEquation
          (CriticalSampleOriginalSlice.polynomial (child F) u p) ((child F).pivot u)
          (CriticalSampleChildCoverage.direction (child F) u) i).eval z) y).IsInvertible := by
  have hd := child_direction_data F u
  rw [hpacket, normalized_vector] at hd
  have hpiv : (child F).pivot u = (0 : Fin (F.free (pairFst u) + 1)) := Fin.ext rfl
  have he : ProjectionCriticalFamily.spatialEquation (CriticalSampleOriginalSlice.polynomial (child F) u p)
      ((child F).pivot u) (CriticalSampleChildCoverage.direction (child F) u) =
      BoundedCriticalSampleBlockData.rows (F.source (pairFst u)) (F.offset (pairFst u)) (F.free (pairFst u))
        (direction F (pairFst u) (record F (pairFst u))) p.val := by
    rw [hd, hpiv]
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;>
      simp only [ProjectionCriticalFamily.spatialEquation, child, Fin.succ_ne_zero, ite_true, ite_false,
        Fin.cons_succ, BoundedCriticalSampleBlockData.rows, ETR.ComplexCircuit.CriticalKernel.finiteRows,
        Fin.cons_zero, CriticalSampleOriginalSlice.polynomial, Function.comp_apply]
  rw [he]
  exact hgood p

theorem prepare_is_packet (F : Inputs) (c : List Bool) :
    pairSnd (prepare F c) = normalized F (pair (pairFst (prepare F c)) (record F (pairFst (prepare F c)))) := by
  rw [prepare_source, prepare_direction]

end LeanCanny.Connectivity.CriticalSampleSelectedDirection
