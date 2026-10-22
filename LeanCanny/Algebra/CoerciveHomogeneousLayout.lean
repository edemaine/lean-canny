/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoerciveHomogeneousCoefficient
public import LeanCanny.Algebra.FixedWidthPolynomialLayout

/-! # Native fixed-width coefficient layout for the coercive homogeneous rows -/

@[expose] public section
namespace LeanCanny.Algebra.CoerciveHomogeneousLayout
open CoerciveCriticalHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

@[simp] lemma layout_none : layout (n := n) none = 0 := by
  apply Fin.ext
  simp [layout]
@[simp] lemma layout_some (j : Fin n) : layout (some j) = j.succ := by
  apply Fin.ext
  simp [layout]
@[simp] lemma layout_symm_zero : (layout (n := n)).symm 0 = none := by
  apply (layout (n := n)).injective
  simp
@[simp] lemma layout_symm_succ (j : Fin n) : layout.symm j.succ = some j := by
  apply (layout (n := n)).injective
  simp

lemma finDegree_eq (D : ℕ) (i : Fin (n + 1)) :
    finDegree D i = if i.val = 0 then 1 else 2 * D + 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [finDegree, nativeDegree]
  · simp [finDegree, nativeDegree]

lemma finSystem_coeff_rank (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (coordinate : Fin n)
    (row : Fin (n + 1)) (W r : ℕ) :
    (finSystem q D coordinate row).coeff
      (RationalSubstitution.Indexed.exponentVector (n + 1) (FixedWidthPolynomial.entry W r)) =
    (system q D coordinate (layout.symm row)).coeff (FixedWidthPolynomial.nativeExponent (layout (n := n)) W r) :=
  FixedWidthPolynomial.coeff_rename_rank layout _ W r

lemma native_none (W r : ℕ) :
    FixedWidthPolynomial.nativeExponent (layout (n := n)) W r none = FixedWidthPolynomial.entry W r 0 := by
  simp only [FixedWidthPolynomial.nativeExponent, Finsupp.coe_equivFunOnFinite_symm, layout_none, Fin.val_zero]

lemma native_some_apply (W r : ℕ) (j : Fin n) :
    FixedWidthPolynomial.nativeExponent (layout (n := n)) W r (some j) = FixedWidthPolynomial.entry W r (j.val + 1) := by
  simp only [FixedWidthPolynomial.nativeExponent, Finsupp.coe_equivFunOnFinite_symm, layout_some, Fin.val_succ]

lemma native_some (W r : ℕ) :
    (FixedWidthPolynomial.nativeExponent (layout (n := n)) W r).some =
      FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin n)) W (Nat.fromBitsLE (r.bits.drop W)) :=
  HomogenizationLayout.native_some (Equiv.refl _) W r

/-- The ordinary homogeneous gradient and the pure leading monomial occupy
separate parameter bidegrees. -/
lemma fin_gradient (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (coordinate j : Fin n) (W r s t : ℕ) :
    ((((finSystem q D coordinate j.succ).coeff
      (RationalSubstitution.Indexed.exponentVector (n + 1) (FixedWidthPolynomial.entry W r))).coeff s).coeff t) =
    (if s = 0 ∧ t = 0 then
      (WeightedHomogenization.homogenize (fun _ : Fin n => 1) (2 * D + 1)
        (MvPolynomial.pderiv j (q ^ 2))).coeff (FixedWidthPolynomial.nativeExponent (layout (n := n)) W r) else 0) +
    (if s = 1 ∧ t = 0 then
      (MvPolynomial.monomial (Finsupp.single (some j) (2 * D + 1)) ((2 * D + 2 : ℕ) : ℤ)).coeff
        (FixedWidthPolynomial.nativeExponent (layout (n := n)) W r) else 0) := by
  rw [finSystem_coeff_rank, layout_symm_succ, CoerciveHomogeneousCoefficient.gradient,
    WeightedHomogenization.coefficient, MvPolynomial.coeff_monomial]
  simp only [ite_and, eq_comm]

lemma fin_coordinate (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (coordinate : Fin n) (W r s t : ℕ) :
    ((((finSystem q D coordinate 0).coeff
      (RationalSubstitution.Indexed.exponentVector (n + 1) (FixedWidthPolynomial.entry W r))).coeff s).coeff t) =
    (if s = 0 ∧ t = 1 ∧ FixedWidthPolynomial.nativeExponent (layout (n := n)) W r = Finsupp.single none 1 then (1 : ℤ) else 0) -
    (if s = 0 ∧ t = 0 ∧ FixedWidthPolynomial.nativeExponent (layout (n := n)) W r = Finsupp.single (some coordinate) 1 then (1 : ℤ) else 0) := by
  rw [finSystem_coeff_rank, layout_symm_zero, CoerciveHomogeneousCoefficient.coordinate]
  split_ifs <;> rfl

lemma fin_coordinate_coeff (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (coordinate : Fin n) (W r s t : ℕ) :
    ((((finSystem q D coordinate 0).coeff
      (RationalSubstitution.Indexed.exponentVector (n + 1) (FixedWidthPolynomial.entry W r))).coeff s).coeff t) =
    (if s = 0 ∧ t = 1 then
      (MvPolynomial.monomial (Finsupp.single (none : Option (Fin n)) 1) (1 : ℤ)).coeff
        (FixedWidthPolynomial.nativeExponent (layout (n := n)) W r) else 0) -
    (if s = 0 ∧ t = 0 then
      (MvPolynomial.monomial (Finsupp.single (some coordinate) 1) (1 : ℤ)).coeff
        (FixedWidthPolynomial.nativeExponent (layout (n := n)) W r) else 0) := by
  rw [fin_coordinate, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  simp only [ite_and, eq_comm]

end LeanCanny.Algebra.CoerciveHomogeneousLayout
