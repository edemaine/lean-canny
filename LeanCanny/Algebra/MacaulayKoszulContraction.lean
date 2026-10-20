/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayMonomialDivision
public import LeanCanny.Algebra.MacaulayGenericShift
public import LeanCanny.Algebra.MatrixKernelContraction

/-! # Transporting the coordinate-power Koszul contraction

The division relations commute with coefficient maps and depend linearly on
the input polynomials. Their characteristic shift therefore transports the
coordinate-power contraction to an invertible generic contraction matrix.
This proves that the degree-compatible Koszul relations span the kernel of
the generic shifted full multiplication matrix at the Macaulay level.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixMinorSection

theorem rowSelection_map {R S I J : Type*} [CommRing R] [CommRing S] [DecidableEq I]
    (φ : R →+* S) (f : J → I) :
    (rowSelection (R := R) f).map φ = rowSelection (R := S) f := by
  funext i j
  change φ ((1 : Matrix I I R) (f i) j) = (1 : Matrix I I S) (f i) j
  simp only [Matrix.one_apply]
  split_ifs <;> simp

end LeanCanny.Algebra.MatrixMinorSection

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical Matrix
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

theorem fullMatrix_map (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) :
    (fullMatrix p d W).map φ = fullMatrix (fun i => (p i).map φ) d W := by
  funext a r
  have hrow : (sourceRow p d W a).map φ = sourceRow (fun i => (p i).map φ) d W a := by
    simp only [sourceRow, map_mul, MvPolynomial.map_monomial, map_one]
  change φ ((sourceRow p d W a).coeff (FixedWidthPolynomial.vector n W r.val)) =
    (sourceRow (fun i => (p i).map φ) d W a).coeff (FixedWidthPolynomial.vector n W r.val)
  rw [← hrow, MvPolynomial.coeff_map]

theorem koszulMultipliers_map (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R)
    (i j k : Fin n) (m : Fin n →₀ ℕ) :
    (koszulMultipliers p i j m k).map φ = koszulMultipliers (fun a => (p a).map φ) i j m k := by
  simp only [koszulMultipliers, Pi.sub_apply, map_sub, Pi.single_apply]
  split_ifs <;> simp only [map_mul, MvPolynomial.map_monomial, map_one, map_zero]

theorem divisionRelations_map (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    (divisionRelations p d W hW).map φ = divisionRelations (fun i => (p i).map φ) d W hW := by
  funext a b
  by_cases ha : a.1 = (divisionRow d W hW a).1
  · simp only [Matrix.map_apply, divisionRelations, ite_eq_left ha, Pi.zero_apply, map_zero]
  · simp only [Matrix.map_apply, divisionRelations, ite_eq_right ha, sourceCoefficients]
    rw [← koszulMultipliers_map, MvPolynomial.coeff_map]

theorem sourceRow_subtractiveSystem (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (a : MultiplierIndex d W) :
    sourceRow (subtractiveSystem p d) d W a = (sourceRow p d W a).map Polynomial.C -
      MvPolynomial.monomial (productExponent d W a) Polynomial.X := by
  simp only [sourceRow, subtractiveSystem, mul_sub, map_mul, MvPolynomial.map_monomial,
    map_one, MvPolynomial.monomial_mul_monomial, one_mul, productExponent]

theorem fullMatrix_subtractiveSystem (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) :
    fullMatrix (subtractiveSystem p d) d W = (fullMatrix p d W).map Polynomial.C -
      (Polynomial.X : Polynomial R) • (fullMatrix (powers (R := R) d) d W).map Polynomial.C := by
  funext a r
  change (sourceRow (subtractiveSystem p d) d W a).coeff (FixedWidthPolynomial.vector n W r.val) =
    Polynomial.C ((sourceRow p d W a).coeff (FixedWidthPolynomial.vector n W r.val)) -
      Polynomial.X * Polynomial.C ((sourceRow (powers (R := R) d) d W a).coeff
        (FixedWidthPolynomial.vector n W r.val))
  rw [sourceRow_subtractiveSystem, MvPolynomial.coeff_sub, MvPolynomial.coeff_map, sourceRow_powers]
  simp only [MvPolynomial.coeff_monomial]
  split_ifs <;> simp

theorem koszulMultipliers_subtractiveSystem (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (i j k : Fin n) (m : Fin n →₀ ℕ) :
    koszulMultipliers (subtractiveSystem p d) i j m k =
      (koszulMultipliers p i j m k).map Polynomial.C -
        MvPolynomial.C Polynomial.X * (koszulMultipliers (powers (R := R) d) i j m k).map Polynomial.C := by
  simp only [koszulMultipliers, Pi.sub_apply, Pi.single_apply]
  split_ifs <;>
    simp only [subtractiveSystem, powers, map_sub, map_mul, MvPolynomial.map_monomial,
      map_one, map_zero, mul_sub, MvPolynomial.monomial_mul_monomial, one_mul,
      MvPolynomial.C_mul_monomial, mul_one] <;> ring

theorem divisionRelations_subtractiveSystem (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    divisionRelations (subtractiveSystem p d) d W hW = (divisionRelations p d W hW).map Polynomial.C -
      (Polynomial.X : Polynomial R) • (divisionRelations (powers (R := R) d) d W hW).map Polynomial.C := by
  funext a b
  by_cases ha : a.1 = (divisionRow d W hW a).1
  · simp [divisionRelations, ha]
  · change (divisionRelations (subtractiveSystem p d) d W hW a) b =
      Polynomial.C (divisionRelations p d W hW a b) -
        Polynomial.X * Polynomial.C (divisionRelations (powers (R := R) d) d W hW a b)
    simp only [divisionRelations, ite_eq_right ha, sourceCoefficients,
      koszulMultipliers_subtractiveSystem, MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_map]

private theorem mapped_contraction {I J : Type*} [Fintype J]
    (φ : R →+* S) (D : Matrix I J R) (H : Matrix J I R) (E : Matrix I I R) :
    D.map φ * H.map φ + E.map φ = (D * H + E).map φ := by
  rw [← Matrix.map_mul]
  funext a b
  exact (φ.map_add _ _).symm

private theorem subtractive_contraction {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (D D₀ : Matrix I J R) (H : Matrix J I R) (E E₀ : Matrix I I R) (h₀ : D₀ * H + E₀ = 1) :
    (D.map Polynomial.C - (Polynomial.X : Polynomial R) • D₀.map Polynomial.C) * H.map Polynomial.C +
        (E.map Polynomial.C - (Polynomial.X : Polynomial R) • E₀.map Polynomial.C) =
      AffineCharacteristic.subtractiveMatrix (D * H + E) := by
  rw [Matrix.sub_mul, Matrix.smul_mul]
  have hbase := mapped_contraction (Polynomial.C : R →+* Polynomial R) D H E
  have hcoord := mapped_contraction (Polynomial.C : R →+* Polynomial R) D₀ H E₀
  rw [h₀, Matrix.map_one Polynomial.C (map_zero _) (map_one _)] at hcoord
  calc
    _ = (D.map Polynomial.C * H.map Polynomial.C + E.map Polynomial.C) -
        (Polynomial.X : Polynomial R) • (D₀.map Polynomial.C * H.map Polynomial.C + E₀.map Polynomial.C) := by
      rw [smul_add]
      abel
    _ = (D * H + E).map Polynomial.C - (Polynomial.X : Polynomial R) • (1 : Matrix I I (Polynomial R)) := by
      rw [hbase, hcoord]
    _ = _ := by
      funext a b
      change Polynomial.C ((D * H + E) a b) - Polynomial.X * (1 : Matrix I I (Polynomial R)) a b =
        Polynomial.C ((D * H + E) a b) - Polynomial.X * Polynomial.C ((1 : Matrix I I R) a b)
      simp only [Matrix.one_apply]
      split_ifs <;> simp

theorem subtractive_division_contraction (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    fullMatrix (subtractiveSystem p d) d W *
        MatrixMinorSection.rowSelection (R := Polynomial R) (selectedMultiplier d W) +
        divisionRelations (subtractiveSystem p d) d W hW =
      AffineCharacteristic.subtractiveMatrix
        (fullMatrix p d W * MatrixMinorSection.rowSelection (R := R) (selectedMultiplier d W) +
          divisionRelations p d W hW) := by
  rw [fullMatrix_subtractiveSystem, divisionRelations_subtractiveSystem,
    ← MatrixMinorSection.rowSelection_map (Polynomial.C : R →+* Polynomial R)]
  exact subtractive_contraction _ _ _ _ _ (powers_division_contraction d W hW)

noncomputable def koszulSpan (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    Submodule R (MultiplierIndex d W → R) :=
  Submodule.span R {v | ∃ (i j : Fin n) (m : Fin n →₀ ℕ), i ≠ j ∧
    m.degree + d i + d j = level d ∧ v = sourceCoefficients (koszulMultipliers p i j m) d W}

theorem koszulSpan_le_kernel (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (hp : ∀ i, (p i).IsHomogeneous (d i)) :
    koszulSpan p d W ≤ LinearMap.ker (fullMatrix p d W).vecMulLinear := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, j, m, hij, hm, rfl⟩
  exact koszul_vecMul_eq_zero p d W hp hW i j hij m hm

theorem divisionRelations_mem_koszulSpan (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (a : MultiplierIndex d W) :
    divisionRelations p d W hW a ∈ koszulSpan p d W := by
  by_cases ha : a.1 = (divisionRow d W hW a).1
  · rw [divisionRelations, ite_eq_left ha]
    exact Submodule.zero_mem _
  · rw [divisionRelations, ite_eq_right ha]
    exact Submodule.subset_span ⟨a.1, (divisionRow d W hW a).1, divisionExponent d W hW a,
      ha, divisionExponent_grade d W hW a ha, rfl⟩

variable [IsDomain R]

noncomputable def genericDivisionContraction (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    Matrix (MultiplierIndex d W) (MultiplierIndex d W) (RatFunc R) :=
  fullMatrix (genericShift p d) d W * MatrixMinorSection.rowSelection (selectedMultiplier d W) +
    divisionRelations (genericShift p d) d W hW

theorem genericDivisionContraction_eq (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    genericDivisionContraction p d W hW =
      (AffineCharacteristic.subtractiveMatrix
        (fullMatrix p d W * MatrixMinorSection.rowSelection (R := R) (selectedMultiplier d W) +
          divisionRelations p d W hW)).map (algebraMap (Polynomial R) (RatFunc R)) := by
  have h := mapped_contraction (algebraMap (Polynomial R) (RatFunc R))
    (fullMatrix (subtractiveSystem p d) d W)
    (MatrixMinorSection.rowSelection (R := Polynomial R) (selectedMultiplier d W))
    (divisionRelations (subtractiveSystem p d) d W hW)
  rw [fullMatrix_map, MatrixMinorSection.rowSelection_map, divisionRelations_map] at h
  change genericDivisionContraction p d W hW = _ at h
  rw [subtractive_division_contraction] at h
  exact h

theorem genericDivisionContraction_det_ne_zero (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    (genericDivisionContraction p d W hW).det ≠ 0 := by
  rw [genericDivisionContraction_eq]
  let A := fullMatrix p d W * MatrixMinorSection.rowSelection (R := R) (selectedMultiplier d W) +
    divisionRelations p d W hW
  change ((AffineCharacteristic.subtractiveMatrix A).map (algebraMap (Polynomial R) (RatFunc R))).det ≠ 0
  have h : (algebraMap (Polynomial R) (RatFunc R)) (AffineCharacteristic.subtractiveMatrix A).det =
      ((AffineCharacteristic.subtractiveMatrix A).map (algebraMap (Polynomial R) (RatFunc R))).det :=
    (algebraMap (Polynomial R) (RatFunc R)).map_det _
  rw [← h]
  exact RatFunc.algebraMap_ne_zero (AffineCharacteristic.subtractive_det_ne_zero _)

theorem genericShift_kernel_iff (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (v : MultiplierIndex d W → RatFunc R) :
    Matrix.vecMul v (fullMatrix (genericShift p d) d W) = 0 ↔
      ∃ w : MultiplierIndex d W → RatFunc R, Matrix.vecMul w (divisionRelations (genericShift p d) d W hW) = v := by
  have htarget : IsUnit (MatrixMinorSection.rowSelection (R := RatFunc R) (selectedMultiplier d W) *
      fullMatrix (genericShift p d) d W).det := by
    rw [MatrixMinorSection.rowSelection_mul]
    exact isUnit_iff_ne_zero.mpr (genericShift_selected_det_ne_zero p d W)
  exact MatrixKernelContraction.vecMul_eq_zero_iff _ _ _
    (divisionRelations_mul_fullMatrix _ d W hW (genericShift_homogeneous p d hp))
    (isUnit_iff_ne_zero.mpr (genericDivisionContraction_det_ne_zero p d W hW)) htarget v

theorem genericShift_kernel_eq_span (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (hp : ∀ i, (p i).IsHomogeneous (d i)) :
    LinearMap.ker (fullMatrix (genericShift p d) d W).vecMulLinear =
      Submodule.span (RatFunc R) (Set.range (divisionRelations (genericShift p d) d W hW).row) := by
  rw [← range_vecMulLinear]
  ext v
  exact genericShift_kernel_iff p d W hW hp v

theorem genericShift_kernel_eq_koszulSpan (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (hp : ∀ i, (p i).IsHomogeneous (d i)) :
    LinearMap.ker (fullMatrix (genericShift p d) d W).vecMulLinear = koszulSpan (genericShift p d) d W := by
  apply le_antisymm
  · rw [genericShift_kernel_eq_span p d W hW hp]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact divisionRelations_mem_koszulSpan _ d W hW a
  · exact koszulSpan_le_kernel _ d W hW (genericShift_homogeneous p d hp)

end LeanCanny.Algebra.Macaulay
