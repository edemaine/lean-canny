/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalLayeredModel
public import LeanCanny.Algebra.IntegralMixedPhysicalGridModel
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeMonomial
/-! # Canonical physical low matrix residues -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalCanonicalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits
set_option backward.isDefEq.respectTransparency false

theorem entryBits_canonical {m n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod m)) (r t : ℕ) :
    ∃ z : ZMod m, residueBits z = IntegralCriticalActualLowMatrixModel.entryBits M r t := by
  unfold IntegralCriticalActualLowMatrixModel.entryBits
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
  · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩

theorem productEntry_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalLayeredBits.productEntry P F q := by
  unfold IntegralMixedPhysicalLayeredBits.productEntry
  rw [IntegralMixedPhysicalLayeredBits.layered_snapshot]
  exact entryBits_canonical _ _ _

theorem product_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalGridBits.product P F q := by
  unfold IntegralMixedPhysicalGridBits.product IntegralMonomialTermBits.Source.value
  rw [IntegralMixedPhysicalGridBits.source_modulus]
  exact ⟨_, rfl⟩

theorem term_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalGridBits.term P F q := by
  rw [IntegralMixedPhysicalGridBits.term_as_product]
  split_ifs
  · exact product_canonical P F q
  · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
theorem original_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalNativeLowerBits.original P F q := by
  rw [IntegralMixedPhysicalCoefficientBits.original_snapshot]
  unfold IntegralMixedPhysicalCoefficientBits.originalAt
  exact ⟨_, rfl⟩

theorem derivative_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalCoefficientBits.derivative P F q := by
  unfold IntegralMixedPhysicalCoefficientBits.derivative IntegralMixedPhysicalCoefficientBits.derivativeAt
  exact ⟨_, rfl⟩

theorem height_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalNativeLowerBits.height P F q := by
  rw [IntegralMixedPhysicalNativeLowerBits.height_eq]
  exact ⟨_, rfl⟩

theorem power_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalFactorBits.power P F q := by
  unfold IntegralMixedPhysicalFactorBits.power
  rw [IntegralMixedPhysicalFactorBits.power_snapshot]
  exact entryBits_canonical _ _ _

theorem cleared_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalSpatialBits.cleared P F q := by
  unfold IntegralMixedPhysicalSpatialBits.cleared IntegralClearedCoefficientBits.Source.value
  exact ⟨_, rfl⟩
end LeanCanny.Algebra.IntegralMixedPhysicalCanonicalBits
