/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationInverseMatrix
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeEntries
/-! # Exact normalized coefficients split into scalar and inverse/raw branches -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

noncomputable def rawCoefficient (F : Family) (key : List Bool) (k : ℕ) :
    Matrix (Fin (FixedWidthPolynomial.count (F.birth key) (F.width key)))
      (Fin (FixedWidthPolynomial.count (F.birth key) (F.width key))) ℤ :=
  Algebra.leftMulMatrix (F.state key).sampler.scalarPrefix.basis.finBasis
    ((IntegralMixedCutMatrix.raw (F.state key) (F.birth_bound key) (F.rule key) (F.kind key) (F.degree key)).coeff k)

theorem rawCoefficient_eq (F : Family) (key : List Bool) (k : ℕ) :
    rawCoefficient F key k = if k ≤ F.degree key then
      IntegralMixedCutMatrix.coefficientMatrix (F.state key) (F.birth_bound key) (F.rule key) (F.kind key) k else 0 :=
  IntegralMixedCutMatrix.raw_coefficient_matrix _ _ _ _ _ _

theorem rawCutValue_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    rawCutValue P F q = residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
      (rawCoefficient F (IntegralMixedVirtualTaskBits.saved P q) (get P .coefficient q))
      (get P .row q) (get P .col q) : ZMod (modulus P q)) := rfl

theorem normalized_matrix_split (F : Family) (key : List Bool) (k : ℕ) :
    IntegralMixedCutNormalizedSource.matrix F key k =
      if k = F.degree key then IntegralParameterInverse.denominator (top F key).charpoly • 1 else
      if k ≤ F.degree key then inverseMatrix F key * rawCoefficient F key k else 0 := by
  rw [IntegralMixedCutNormalizedSource.matrix_eq, top_normalized_leading, rawCoefficient_eq]
  by_cases HE : k = F.degree key
  · rw [ite_eq_left HE, ite_eq_left HE]
  · rw [ite_eq_right HE, ite_eq_right HE]
    by_cases HL : k ≤ F.degree key
    · rw [ite_eq_left HL, ite_eq_left HL, ite_eq_left HL]
      rfl
    · rw [ite_eq_right HL, ite_eq_right HL]

noncomputable def normalizedValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
    (IntegralMixedCutNormalizedSource.matrix F (IntegralMixedVirtualTaskBits.saved P q) (get P .coefficient q))
    (get P .row q) (get P .col q) : ZMod (modulus P q))

noncomputable def productValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
    (inverseMatrix F (IntegralMixedVirtualTaskBits.saved P q) *
      rawCoefficient F (IntegralMixedVirtualTaskBits.saved P q) (get P .coefficient q))
    (get P .row q) (get P .col q) : ZMod (modulus P q))

theorem normalizedValue_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = normalizedValue P F q := ⟨_, rfl⟩

theorem productValue_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = productValue P F q := ⟨_, rfl⟩

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
