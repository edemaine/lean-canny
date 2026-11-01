/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationInverseSum
public import LeanCanny.Algebra.IntegralMixedNormalizationProductModel
/-! # Frozen natural-index inverse and raw coefficient values -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

noncomputable def inverseMatrixAt (F : Family) (key : List Bool) (m r t : ℕ) : List Bool :=
  residueBits (inverseMatrix F key
    ⟨r % dimension F key, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨t % dimension F key, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩ : ZMod m)

noncomputable def rawAt (F : Family) (key : List Bool) (m k r t : ℕ) : List Bool :=
  residueBits (IntegralCriticalTotalSnapshotBits.integerEntry (rawCoefficient F key k) r t : ZMod m)

theorem inverseMatrix_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    inverseMatrixValue P F q = inverseMatrixAt F (IntegralMixedVirtualTaskBits.saved P q)
      (modulus P q) (get P .row q) (get P .col q) := rfl

theorem rawAt_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    rawCutValue P F q = rawAt F (IntegralMixedVirtualTaskBits.saved P q)
      (modulus P q) (get P .coefficient q) (get P .row q) (get P .col q) := rfl

noncomputable def productTermValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  let h : Fin (matrixDimension P F q) :=
    ⟨get P .target q % matrixDimension P F q, Nat.mod_lt _ (matrixDimension_pos P F q)⟩
  residueBits ((inverseMatrix F (IntegralMixedVirtualTaskBits.saved P q) (topRow P F q) h *
    rawCoefficient F (IntegralMixedVirtualTaskBits.saved P q) (get P .coefficient q) h (topCol P F q) : ℤ) : ZMod (modulus P q))

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
