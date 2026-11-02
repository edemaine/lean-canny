/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCutHeightProfile
/-! # One original-data factor bounds every actual raw-cut coefficient -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutHeightProfile
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
open IntegralMixedCutSource IntegralMixedCoordinateBounds IntegralMixedVirtualSweepSource IntegralMixedHeightScaling
set_option backward.isDefEq.respectTransparency false

theorem columns_le (F : Family) (H : OriginalBounds F) (q : List Bool) :
    IntegralMixedValueHeightBounds.columns F q ≤ columns (F.ambient q) (H.spatialDegree q) := by
  have HW := (IntegralMixedExceptionalBounds.value_width_le (F.spatial q) (F.rule q)).trans
    (boxWidth_mono (n := F.ambient q + 1) (H.degree_bound q))
  have HN : F.ambient q - (F.rule q).critical.offset.val + 1 + 1 ≤ F.ambient q + 2 := by omega
  unfold IntegralMixedValueHeightBounds.columns columns count
  rw [← pow_mul, ← pow_mul]
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul HW HN)

theorem rows_le (F : Family) (H : OriginalBounds F) (q : List Bool) :
    IntegralMixedValueHeightBounds.rows F q ≤ rows (F.ambient q) (H.spatialDegree q) := by
  have HN : F.ambient q - (F.rule q).critical.offset.val + 1 + 2 ≤ F.ambient q + 3 := by omega
  exact Nat.mul_le_mul HN (columns_le F H q)

theorem system_scaled (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool) :
    IntegralMixedValueSystemBounds.height F I H q ≤
      system (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (F.cap q) (H.nodes q) * H.bankHeight q := by
  have HC := coordinate_scaled (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (F.cap q) (H.nodes q) (H.bankHeight q)
  have HR := row_scaled F I H q
  have hG : 1 ≤ H.bankHeight q := by have := H.source_le_bank q; omega
  calc
    _ ≤ coordinate (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (F.cap q) (H.nodes q) * H.bankHeight q +
        row (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (F.cap q) (H.nodes q) * H.bankHeight q + 1 * H.bankHeight q :=
      Nat.add_le_add (Nat.add_le_add HC.le HR) (by simpa only [Nat.one_mul] using hG)
    _ = _ := by unfold system; ring

theorem value_scaled (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool)
    (hR : count (F.birth q + 2) (F.width q) ≤ H.rank q) :
    IntegralMixedValueHeightBounds.height F I H q ≤
      value (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (F.cap q) (H.nodes q) * H.bankHeight q := by
  have hG : 1 ≤ H.bankHeight q := by have := H.source_le_bank q; omega
  let A := system (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (F.cap q) (H.nodes q)
  have HG := (gram_mono (rows_le F H q) hR (system_scaled F I H q)).trans
    (gram_scaled (rows (F.ambient q) (H.spatialDegree q)) (H.rank q) A (H.bankHeight q) hG)
  exact (determinant_mono (columns_le F H q) hR HG).trans
    (determinant_scaled (columns (F.ambient q) (H.spatialDegree q)) (H.rank q)
      (IntegralMacaulayGramBounds.gramHeight (rows (F.ambient q) (H.spatialDegree q)) (H.rank q) A) (H.bankHeight q) hG)

theorem height_le (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool)
    (hR : count (F.birth q + 2) (F.width q) ≤ H.rank q) :
    IntegralMixedAllRawHeightBounds.height F I H q ≤
      factor (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (F.cap q) (H.nodes q) * H.bankHeight q := by
  have hG : 1 ≤ H.bankHeight q := by have := H.source_le_bank q; omega
  have HC := coordinate_scaled (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (F.cap q) (H.nodes q) (H.bankHeight q)
  have HP : IntegralMixedSquarefreeHeightBounds.height (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q)
      (F.cap q) (H.nodes q) (H.bankHeight q) ≤
      IntegralPrincipalHeightBounds.height (IntegralMixedExceptionalBounds.K (F.ambient q + 1) (H.spatialDegree q)) (H.rank q)
        (coordinate (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (F.cap q) (H.nodes q)) * H.bankHeight q := by
    unfold IntegralMixedSquarefreeHeightBounds.height
    rw [HC]
    exact principal_scaled _ _ _ _ hG
  have HV := value_scaled F I H q hR
  unfold IntegralMixedAllRawHeightBounds.height
  apply max_le
  · exact HC.le.trans (Nat.mul_le_mul_right _ (le_max_left _ _))
  · apply max_le
    · exact HP.trans (Nat.mul_le_mul_right _ ((le_max_left _ _).trans (le_max_right _ _)))
    · exact HV.trans (Nat.mul_le_mul_right _ ((le_max_right _ _).trans (le_max_right _ _)))

theorem coefficient_height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool)
    (hR : count (F.birth q + 2) (F.width q) ≤ H.rank q) (k : ℕ) (u v : Fin (count (F.birth q) (F.width q))) :
    (IntegralMixedCutMatrix.coefficientMatrix (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) k u v).natAbs ≤
      2 ^ (factor (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (F.cap q) (H.nodes q) * H.bankHeight q) :=
  (IntegralMixedAllRawHeightBounds.coefficient_height F I H q k u v).trans (Nat.pow_le_pow_right (by decide) (height_le F I H q hR))
end LeanCanny.Algebra.IntegralMixedCutHeightProfile
