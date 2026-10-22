/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveMinorEliminant
public import LeanCanny.Algebra.CoerciveCriticalHomogenization
public import LeanCanny.Algebra.CoerciveCriticalBounds

/-! # Bounded integer coordinate annihilants for coercive critical fibers

A nonzero full Macaulay maximal minor is selected at a root-free complex
specialization of the actual homogenized gradients and coordinate equation.
It annihilates the coordinate at every critical point of every positive
real perturbation. Bounds depend only on dimension, original degree and mass.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace LeanCanny.Algebra.CoerciveCoordinateEliminant
open scoped Classical
open CoerciveCriticalHomogenization

variable {n : ℕ}

def width (n D : ℕ) : ℕ :=
  (max (Macaulay.level (finDegree (n := n) D)) (2 * D + 1)).size

theorem level_lt (n D : ℕ) :
    Macaulay.level (finDegree (n := n) D) < 2 ^ width n D :=
  (le_max_left _ _).trans_lt (Nat.lt_size_self _)

theorem degree_lt (n D : ℕ) (j : Fin (n + 1)) :
    finDegree D j < 2 ^ width n D := by
  have h : finDegree D j ≤ 2 * D + 1 := by
    unfold finDegree
    cases layout.symm j <;> simp [nativeDegree]
  exact (h.trans (le_max_right _ _)).trans_lt (Nat.lt_size_self _)

def columnBound (n D : ℕ) : ℕ := FixedWidthPolynomial.count (n + 1) (width n D)

noncomputable def massBound (q : MvPolynomial (Fin n) ℤ) (D : ℕ) : ℕ :=
  (columnBound n D).factorial * CoerciveCriticalBounds.coefficientBudget q D ^ columnBound n D

/-- An actual nonzero integer bivariate annihilator, with no supplied
finiteness, simplicity, root curve, or elimination certificate. -/
theorem exists_annihilator (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) :
    ∃ H : Polynomial (Polynomial ℤ), H ≠ 0 ∧
      H.natDegree ≤ columnBound n D ∧
      (∀ j, (H.coeff j).natDegree ≤ columnBound n D) ∧
      NestedMass.mass H ≤ massBound q D ∧
      ∀ (s : ℝ) (x : Fin n → ℝ),
        (∀ j, MvPolynomial.eval x (MvPolynomial.pderiv j
          (CoerciveCriticalFibers.polynomial (q.map (Int.castRingHom ℝ)) D s)) = 0) →
        parameterMap s (x i) H = 0 := by
  obtain ⟨t, ht⟩ := finSystem_exists_no_projective_root q D hD i
  have hentry := CoerciveCriticalBounds.finSystem_entryBounds q D hD i
  obtain ⟨f, hf, hs, hT, hm⟩ := ProjectiveMinorEliminant.exists_bounded_minor
    (finSystem q D i) (finDegree D) (width n D) (level_lt n D)
    (finSystem_homogeneous q D i) (finDegree_pos D) (parameterMap 1 t) ht
    1 1 (CoerciveCriticalBounds.coefficientBudget q D)
    (fun j e => (hentry j e).outerDegree)
    (fun j e k => (hentry j e).innerDegree k)
    (fun j e => (hentry j e).mass)
  let H := ((Macaulay.fullMatrix (finSystem q D i) (finDegree D) (width n D)).submatrix f id).det
  have hC : Fintype.card (Macaulay.activeIndices (finDegree (n := n) D) (width n D)) ≤
      columnBound n D := by
    simpa only [columnBound, Fintype.card_coe, Fintype.card_fin] using
      (Finset.card_le_univ (s := Macaulay.activeIndices (finDegree (n := n) D) (width n D)))
  have hM : 1 ≤ CoerciveCriticalBounds.coefficientBudget q D := by
    unfold CoerciveCriticalBounds.coefficientBudget
    have h := Nat.mul_le_mul (show 1 ≤ 2 * D + 2 by omega)
      (show 1 ≤ MvMass.mass q ^ 2 + 1 by omega)
    simpa only [one_mul] using h
  refine ⟨H, hf, ?_, ?_, ?_, ?_⟩
  · apply le_trans _ hC
    simpa only [mul_one] using hs
  · intro j
    apply le_trans _ hC
    simpa only [mul_one] using hT j
  · exact hm.trans (Nat.mul_le_mul (Nat.factorial_le hC) (Nat.pow_le_pow_right hM hC))
  · intro s x hx
    exact ProjectiveMinorEliminant.minor_eval_eq_zero (finSystem q D i) (finDegree D)
      (width n D) (degree_lt n D) (level_lt n D) (finSystem_homogeneous q D i)
      (finDegree_pos D) f (parameterMap s (x i)) (finPoint x)
      (finSystem_critical_root q D hD i s x hx) (finPoint_nonzero x)

end LeanCanny.Algebra.CoerciveCoordinateEliminant
