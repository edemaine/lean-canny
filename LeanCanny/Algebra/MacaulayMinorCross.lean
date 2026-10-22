/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixSelectedMinorCross
public import LeanCanny.Algebra.MacaulayHigherDenominators

/-! # Cross identities for arbitrary full Macaulay minors

The determinant identities for selectors give a polynomial cross identity
between every maximal minor, the universal quotient, and the higher
relation factor. This is the identity needed before cancelling the higher
denominator family across all orderings.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def minorRelationFactor (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hW : level d < 2 ^ W) (f : activeIndices d W → MultiplierIndex d W) : R :=
  Matrix.det (Function.extend (selectedMultiplier d W) (MatrixMinorSection.rowSelection (R := R) f)
    (fullMatrix p d W * MatrixMinorSection.rowSelection f + divisionRelations p d W hW) :
      Matrix (MultiplierIndex d W) (MultiplierIndex d W) R)

theorem fullMinor_relation_cross [IsDomain R] (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W)
    (hnum : (activeMinor p d W).det ≠ 0) (hrel : (relationMinor p d W hW).det ≠ 0)
    (f : activeIndices d W → MultiplierIndex d W) :
    ((fullMatrix p d W).submatrix f id).det * (relationMinor p d W hW).det =
      (activeMinor p d W).det * minorRelationFactor p d W hW f := by
  have h₁ := MatrixSelectedMinorCross.contraction_det_of_ne_zero (fullMatrix p d W) (divisionRelations p d W hW)
    (selectedMultiplier d W) (selectedMultiplier_injective d W) (divisionRelations_selected p d W hW)
    (divisionRelations_mul_fullMatrix p d W hW hp) (by rwa [fullMatrix_selected]) hrel (MatrixMinorSection.rowSelection f)
  rw [MatrixMinorSection.rowSelection_mul] at h₁
  have h₂ := MatrixSelectedMinorCross.contraction_factorization (fullMatrix p d W) (divisionRelations p d W hW)
    (selectedMultiplier d W) (selectedMultiplier_injective d W) (divisionRelations_selected p d W hW) (MatrixMinorSection.rowSelection f)
  rw [fullMatrix_selected] at h₂
  exact h₁.symm.trans h₂

end LeanCanny.Algebra.Macaulay

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def fullMinor (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n))
    (f : Macaulay.activeIndices (d ∘ π) W → Macaulay.MultiplierIndex (d ∘ π) W) : CoefficientRing n R :=
  ((Macaulay.fullMatrix (system (R := R) d W π) (d ∘ π) W).submatrix f id).det

theorem fullMinor_quotient_cross (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W) (π : Equiv.Perm (Fin (n + 1)))
    (hπ : Macaulay.level (d ∘ π) < 2 ^ W)
    (f : Macaulay.activeIndices (d ∘ π) W → Macaulay.MultiplierIndex (d ∘ π) W) :
    fullMinor (R := ℤ) d W π f * higherDenominator d W π hπ = integerQuotient d W hdegree hW *
      Macaulay.minorRelationFactor (system (R := ℤ) d W π) (d ∘ π) W hπ f := by
  have hnum : numerator (R := ℤ) d W π ≠ 0 := by
    intro hz
    have he := numerator_power_specialization (R := ℤ) d W hdegree π
    rw [hz, map_zero] at he
    exact zero_ne_one he
  have hh : higherDenominator (R := ℤ) d W π hπ ≠ 0 := by
    intro hz
    have he := higherDenominator_power_specialization (R := ℤ) d W hdegree π hπ
    rw [hz, map_zero] at he
    exact zero_ne_one he
  have hrel : (Macaulay.relationMinor (system (R := ℤ) d W π) (d ∘ π) W hπ).det ≠ 0 := by
    rw [Macaulay.relationMinor_det_eq_extraneous_mul]
    exact mul_ne_zero (denominator_ne_zero (R := ℤ) d W hdegree π) hh
  have hc := Macaulay.fullMinor_relation_cross (system (R := ℤ) d W π) (d ∘ π) W
    (system_homogeneous d W π) hπ hnum hrel f
  rw [Macaulay.relationMinor_det_eq_extraneous_mul] at hc
  change fullMinor d W π f * (denominator d W π * higherDenominator d W π hπ) =
    numerator d W π * Macaulay.minorRelationFactor (system (R := ℤ) d W π) (d ∘ π) W hπ f at hc
  rw [(integerQuotient_spec d W hdegree hW).1 π] at hc
  apply mul_left_cancel₀ (denominator_ne_zero (R := ℤ) d W hdegree π)
  calc
    _ = fullMinor d W π f * (denominator d W π * higherDenominator d W π hπ) := by ring
    _ = _ := hc
    _ = _ := by ring

end LeanCanny.Algebra.MacaulayUniversal
