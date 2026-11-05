/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldQueryBounds
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldPhysical
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutPhysical
public import LeanCanny.Algebra.DiagonalPolynomialParameterSpace
public import LeanCanny.Algebra.CoefficientFinitePhysicalQuery
/-! # Actual complete finite columns of default retained-field queries -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFieldVariables
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem toMv_variables {R : Type*} [CommRing R] (p : R[X]) (c N : ℕ) (hc : c < N) :
    ∀ v ∈ (p.toMvPolynomial c).vars, v < N := by
  intro v hv
  rw [← MvPolynomial.rename_toMvPolynomial (fun _ : Unit => c) () p] at hv
  obtain ⟨j, _, rfl⟩ := MvPolynomial.mem_vars_rename (fun _ : Unit => c) (p.toMvPolynomial ()) hv
  exact hc

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def count (right : Bool) (z : List Bool) :=
  (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha (CoefficientMarkedRecordFieldQuery.rightRoot right z)).count

theorem count_unary (right : Bool) : UnaryFn (count hn ht ha right) :=
  (CoefficientMarkedRecordFullCutPhysical.count_unary hn ht ha).comp (CoefficientMarkedRecordFieldQuery.rightRoot_FP right)

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic

theorem column_lt (right : Bool) (z : List Bool) :
    CoefficientMarkedRecordFieldQuery.column hn ht ha right z < count hn ht ha right z := by
  unfold CoefficientMarkedRecordFieldQuery.column CoefficientMarkedRecordFieldQuery.scalarAt
  split_ifs with hi
  · exact ((CoefficientMarkedRecordRows.symbolic hn ht ha (CoefficientMarkedRecordFieldQuery.rightRoot right z)
      (IntegralMixedCausalRecordPlanBits.count (CoefficientMarkedRecordFieldQuery.rightRoot right z)) le_rfl).scalar
      ⟨IntegralMixedPhysicalFieldEquality.catalogSelected n right z, hi⟩).isLt
  · exact CoefficientMarkedRecordFullCutPhysical.count_pos hn ht ha _

theorem variable_box (right : Bool) (z : List Bool) (k : ℕ) :
    ∀ i ∈ (CoefficientMarkedRecordFieldQuery.physical hn ht ha right z k).vars, i < count hn ht ha right z :=
  toMv_variables _ _ _ (column_lt hn ht ha right z)

noncomputable def polynomial (right : Bool) (z : List Bool) (k : ℕ) :
    MvPolynomial (Fin (count hn ht ha right z)) ℤ[X] :=
  CoefficientFinitePhysicalQuery.polynomial _ (CoefficientMarkedRecordFieldQuery.physical hn ht ha right z k)
    (variable_box hn ht ha right z k)

theorem rename_polynomial (right : Bool) (z : List Bool) (k : ℕ) :
    MvPolynomial.rename Fin.val (polynomial hn ht ha right z k) = CoefficientMarkedRecordFieldQuery.physical hn ht ha right z k :=
  CoefficientFinitePhysicalQuery.rename_polynomial _ _ _

theorem degree (right : Bool) (z : List Bool) (k : ℕ) :
    (polynomial hn ht ha right z k).totalDegree ≤
      2*IntegralMixedPhysicalFieldEquality.catalogDegree hn ht ha (CoefficientMarkedRecordFieldSource.root z)*
        IntegralMixedPhysicalFieldEquality.catalogPower hn ht ha right z := by
  unfold polynomial
  rw [CoefficientFinitePhysicalQuery.degree_eq]
  exact (UnivariateInfinity.degree_le _ _).trans (CoefficientMarkedRecordFieldQuery.target_degree hn ht ha right z k)

theorem coefficient_degree_mass (right : Bool) (z : List Bool) (k : ℕ) (e : Fin (count hn ht ha right z) →₀ ℕ) :
    ((polynomial hn ht ha right z k).coeff e).natDegree ≤ CoefficientMarkedRecordFieldQuery.slope hn ht ha right z ∧
    coefficientMass ((polynomial hn ht ha right z k).coeff e) ≤ 2^CoefficientMarkedRecordFieldQuery.coefficientBudget hn ht ha right z := by
  unfold polynomial
  rw [CoefficientFinitePhysicalQuery.coefficient]
  unfold CoefficientMarkedRecordFieldQuery.physical
  rw [DiagonalParameterBits.coefficient]
  split_ifs
  · exact CoefficientMarkedRecordFieldQuery.coefficient_degree_mass hn ht ha right z k _
  · simp only [Polynomial.natDegree_zero, coefficientMass_zero, Nat.zero_le, and_self]

end LeanCanny.Encoding.CoefficientMarkedRecordFieldVariables
