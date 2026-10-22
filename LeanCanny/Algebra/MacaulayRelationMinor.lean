/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayKoszulContraction
public import LeanCanny.Algebra.MatrixSelectedBlock
public import Mathlib.LinearAlgebra.Basis.Basic

/-! # The complementary square Koszul relation block

Selected multiplier rows give zero division relations. The remaining rows
and their matching columns form a square relation minor. For coordinate
powers it is the identity; its characteristic shift is therefore invertible
over the generic coefficient field.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical Matrix
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

abbrev RelationIndex (d : Fin n → ℕ) (W : ℕ) :=
  {a : MultiplierIndex d W // a ∉ Set.range (selectedMultiplier d W)}

theorem divisionRelations_selected (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (r : activeIndices d W) :
    divisionRelations p d W hW (selectedMultiplier d W r) = 0 := by
  have he : divisionRow d W hW (selectedMultiplier d W r) = selectedMultiplier d W r := by
    unfold divisionRow
    rw [productIndex_selected]
  simp only [divisionRelations, he, ite_true]

noncomputable def relationMinor (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) : Matrix (RelationIndex d W) (RelationIndex d W) R :=
  (divisionRelations p d W hW).submatrix Subtype.val Subtype.val

noncomputable def independentRelations (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) : Matrix (RelationIndex d W) (MultiplierIndex d W) R :=
  (divisionRelations p d W hW).submatrix Subtype.val id

theorem relationMinor_powers (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    relationMinor (powers (R := R) d) d W hW = 1 := by
  funext a b
  change divisionRelations (powers (R := R) d) d W hW a.val b.val = _
  rw [divisionRelations_powers]
  have hb : b.val ≠ divisionRow d W hW a.val := by
    intro h
    exact b.property ⟨productIndex d W hW a.val, h.symm⟩
  simp only [Pi.sub_apply, Pi.single_apply, ite_eq_right hb, sub_zero, Matrix.one_apply,
    Subtype.val_injective.eq_iff, eq_comm]

theorem relationMinor_map (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    (relationMinor p d W hW).map φ = relationMinor (fun i => (p i).map φ) d W hW := by
  funext a b
  exact congrFun (congrFun (divisionRelations_map φ p d W hW) a.val) b.val

theorem relationMinor_subtractiveSystem (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    relationMinor (subtractiveSystem p d) d W hW = AffineCharacteristic.subtractiveMatrix (relationMinor p d W hW) := by
  funext a b
  have h := congrFun (congrFun (divisionRelations_subtractiveSystem p d W hW) a.val) b.val
  change relationMinor (subtractiveSystem p d) d W hW a b = Polynomial.C (relationMinor p d W hW a b) -
    Polynomial.X * Polynomial.C (relationMinor (powers (R := R) d) d W hW a b) at h
  rw [relationMinor_powers] at h
  exact h

theorem contraction_determinant (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    (fullMatrix p d W * MatrixMinorSection.rowSelection (selectedMultiplier d W) + divisionRelations p d W hW).det =
      (activeMinor p d W).det * (relationMinor p d W hW).det := by
  rw [MatrixSelectedBlock.determinant _ _ _ (selectedMultiplier_injective d W)
    (divisionRelations_selected p d W hW), fullMatrix_selected]
  rfl

theorem contraction_characteristic_determinant (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    (AffineCharacteristic.subtractiveMatrix
      (fullMatrix p d W * MatrixMinorSection.rowSelection (R := R) (selectedMultiplier d W) +
        divisionRelations p d W hW)).det = (AffineCharacteristic.subtractiveMatrix (activeMinor p d W)).det *
      (AffineCharacteristic.subtractiveMatrix (relationMinor p d W hW)).det := by
  rw [← subtractive_division_contraction, contraction_determinant, activeMinor_subtractiveSystem,
    relationMinor_subtractiveSystem]

theorem vecMul_independentRelations (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (w : MultiplierIndex d W → R) :
    Matrix.vecMul (fun a : RelationIndex d W => w a.val) (independentRelations p d W hW) =
      Matrix.vecMul w (divisionRelations p d W hW) := by
  funext b
  change (∑ a : RelationIndex d W, w a.val * divisionRelations p d W hW a.val b) =
    ∑ a, w a * divisionRelations p d W hW a b
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (fun a : MultiplierIndex d W => a ∉ Set.range (selectedMultiplier d W))
    (fun a => w a * divisionRelations p d W hW a b)
  have hz : (∑ a : {a : MultiplierIndex d W // ¬a ∉ Set.range (selectedMultiplier d W)},
      w a.val * divisionRelations p d W hW a.val b) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    obtain ⟨r, hr⟩ := not_not.mp a.property
    rw [← hr, divisionRelations_selected, Pi.zero_apply, mul_zero]
  rw [hz, add_zero] at hsum
  exact hsum

theorem independentRelations_mul_fullMatrix (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (hp : ∀ i, (p i).IsHomogeneous (d i)) :
    independentRelations p d W hW * fullMatrix p d W = 0 := by
  funext a r
  exact congrFun (congrFun (divisionRelations_mul_fullMatrix p d W hW hp) a.val) r

variable [IsDomain R]

theorem genericShift_relationMinor_det_ne_zero (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    (relationMinor (genericShift p d) d W hW).det ≠ 0 := by
  have h : (relationMinor (subtractiveSystem p d) d W hW).map (algebraMap (Polynomial R) (RatFunc R)) =
      relationMinor (genericShift p d) d W hW :=
    relationMinor_map (algebraMap (Polynomial R) (RatFunc R)) _ d W hW
  rw [← h, relationMinor_subtractiveSystem]
  have hm : (algebraMap (Polynomial R) (RatFunc R))
      (AffineCharacteristic.subtractiveMatrix (relationMinor p d W hW)).det =
      ((AffineCharacteristic.subtractiveMatrix (relationMinor p d W hW)).map
        (algebraMap (Polynomial R) (RatFunc R))).det :=
    (algebraMap (Polynomial R) (RatFunc R)).map_det _
  rw [← hm]
  exact RatFunc.algebraMap_ne_zero (AffineCharacteristic.subtractive_det_ne_zero _)

theorem genericShift_independentRelations_injective (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    Function.Injective (Matrix.vecMul · (independentRelations (genericShift p d) d W hW)) := by
  intro v w hvw
  have he : Matrix.vecMul v (relationMinor (genericShift p d) d W hW) =
      Matrix.vecMul w (relationMinor (genericShift p d) d W hW) := by
    funext b
    exact congrFun hvw b.val
  exact Matrix.vecMul_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
      (genericShift_relationMinor_det_ne_zero p d W hW))) he

theorem genericShift_independentRows_linearIndependent (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    LinearIndependent (RatFunc R) (independentRelations (genericShift p d) d W hW).row :=
  Matrix.vecMul_injective_iff.mp (genericShift_independentRelations_injective p d W hW)

theorem genericShift_independent_kernel_iff (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (v : MultiplierIndex d W → RatFunc R) :
    Matrix.vecMul v (fullMatrix (genericShift p d) d W) = 0 ↔
      ∃ w : RelationIndex d W → RatFunc R, Matrix.vecMul w (independentRelations (genericShift p d) d W hW) = v := by
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := (genericShift_kernel_iff p d W hW hp v).mp hv
    exact ⟨fun a => w a.val, (vecMul_independentRelations _ d W hW w).trans hw⟩
  · rintro ⟨w, rfl⟩
    rw [Matrix.vecMul_vecMul, independentRelations_mul_fullMatrix _ d W hW
      (genericShift_homogeneous p d hp), Matrix.vecMul_zero]

theorem genericShift_kernel_iff_existsUnique (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (v : MultiplierIndex d W → RatFunc R) :
    Matrix.vecMul v (fullMatrix (genericShift p d) d W) = 0 ↔
      ∃! w : RelationIndex d W → RatFunc R, Matrix.vecMul w (independentRelations (genericShift p d) d W hW) = v := by
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := (genericShift_independent_kernel_iff p d W hW hp v).mp hv
    refine ⟨w, hw, ?_⟩
    intro w' hw'
    exact genericShift_independentRelations_injective p d W hW (hw'.trans hw.symm)
  · rintro ⟨w, hw, _⟩
    exact (genericShift_independent_kernel_iff p d W hW hp v).mpr ⟨w, hw⟩

theorem genericShift_kernel_eq_span_independentRows (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (hp : ∀ i, (p i).IsHomogeneous (d i)) :
    LinearMap.ker (fullMatrix (genericShift p d) d W).vecMulLinear =
      Submodule.span (RatFunc R) (Set.range (independentRelations (genericShift p d) d W hW).row) := by
  rw [← range_vecMulLinear]
  ext v
  exact genericShift_independent_kernel_iff p d W hW hp v

noncomputable def genericShift_kernelBasis (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (hp : ∀ i, (p i).IsHomogeneous (d i)) :
    Module.Basis (RelationIndex d W) (RatFunc R) (LinearMap.ker (fullMatrix (genericShift p d) d W).vecMulLinear) :=
  (Module.Basis.span (genericShift_independentRows_linearIndependent p d W hW)).map
    (LinearEquiv.ofEq _ _ (genericShift_kernel_eq_span_independentRows p d W hW hp).symm)

theorem genericShift_kernelBasis_apply (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (a : RelationIndex d W) :
    (genericShift_kernelBasis p d W hW hp a : MultiplierIndex d W → RatFunc R) =
      independentRelations (genericShift p d) d W hW a := by
  simp only [genericShift_kernelBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply]
  rfl

end LeanCanny.Algebra.Macaulay
