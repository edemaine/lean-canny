/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveBoxGramEliminant
public import LeanCanny.Algebra.MacaulayFullBoxFinite
public import LeanCanny.Algebra.CoerciveCoordinateEliminant

/-! # Canonical integer Gram annihilants of coercive critical coordinates

These fixed determinants replace selected maximal minors. Their construction
contains no choice of matrix rows, and the actual homogeneous critical system
supplies both annihilation and a real specialization proving nonvanishing.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoerciveBoxGramEliminant
open CoerciveCriticalHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

noncomputable def polynomial (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (coordinate : Fin n) : Coefficient :=
  ProjectiveBoxGramEliminant.polynomial (finSystem q D coordinate) (finDegree D)
    (CoerciveCoordinateEliminant.width n D)

theorem ne_zero (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (coordinate : Fin n) : polynomial q D coordinate ≠ 0 := by
  obtain ⟨t, ht⟩ := finSystem_exists_real_no_complex_projective_root q D hD coordinate
  apply ProjectiveBoxGramEliminant.ne_zero_of_real_specialization (finSystem q D coordinate)
    (finDegree D) (CoerciveCoordinateEliminant.width n D) (CoerciveCoordinateEliminant.level_lt n D)
    (finSystem_homogeneous q D coordinate) (finDegree_pos D) (parameterMap 1 t)
  have he : Complex.ofRealHom.comp (parameterMap (1 : ℝ) t) = parameterMap 1 (t : ℂ) := by
    ext <;> simp [parameterMap]
  intro x hx
  rw [he] at hx
  exact ht x hx

/-- Every critical point annihilates the same fixed integer polynomial. -/
theorem eval_eq_zero (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (coordinate : Fin n) (s : ℝ) (x : Fin n → ℝ)
    (hx : ∀ j, MvPolynomial.eval x (MvPolynomial.pderiv j
      (CoerciveCriticalFibers.polynomial (q.map (Int.castRingHom ℝ)) D s)) = 0) :
    parameterMap s (x coordinate) (polynomial q D coordinate) = 0 :=
  ProjectiveBoxGramEliminant.eval_eq_zero_of_common_root (finSystem q D coordinate) (finDegree D)
    (CoerciveCoordinateEliminant.width n D) (CoerciveCoordinateEliminant.level_lt n D)
    (finSystem_homogeneous q D coordinate) (parameterMap s (x coordinate)) (finPoint x)
    (finSystem_critical_root q D hD coordinate s x hx) (finPoint_nonzero x)

def columnCount (n D : ℕ) : ℕ :=
  FixedWidthPolynomial.count (n + 1) (CoerciveCoordinateEliminant.width n D)

def blockDimension (n D : ℕ) : ℕ := (n + 3) * columnCount n D

/-- The canonical square matrix with source rows, inactive padding, and Gram
columns in consecutive numeric ranges. -/
noncomputable def numericMatrix (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (coordinate : Fin n) :
    Matrix (Fin (blockDimension n D)) (Fin (blockDimension n D)) Coefficient :=
  MacaulayFullBoxFinite.matrix (finSystem q D coordinate) (finDegree D)
    (CoerciveCoordinateEliminant.width n D)

lemma det_numericMatrix (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (coordinate : Fin n) :
    (numericMatrix q D coordinate).det = polynomial q D coordinate :=
  MacaulayFullBoxFinite.det_matrix (finSystem q D coordinate) (finDegree D)
    (CoerciveCoordinateEliminant.width n D)

lemma numericMatrix_inner_degree (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (coordinate : Fin n)
    (a b : Fin (blockDimension n D)) (k : ℕ) :
    ((numericMatrix q D coordinate a b).coeff k).natDegree ≤ 1 :=
  MacaulayFullBoxFinite.matrix_inner_degree (finSystem q D coordinate) (finDegree D)
    (CoerciveCoordinateEliminant.width n D) 1
    (fun j e k => (CoerciveCriticalBounds.finSystem_entryBounds q D hD coordinate j e).innerDegree k) a b k

noncomputable def massBound (q : MvPolynomial (Fin n) ℤ) (D : ℕ) : ℕ :=
  (columnCount n D).factorial *
    ((n + 2) * columnCount n D * CoerciveCriticalBounds.coefficientBudget q D ^ 2) ^ columnCount n D

theorem mass_le (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (coordinate : Fin n) : NestedMass.mass (polynomial q D coordinate) ≤ massBound q D :=
  ProjectiveBoxGramEliminant.mass_le (finSystem q D coordinate) (finDegree D)
    (CoerciveCoordinateEliminant.width n D) (CoerciveCriticalBounds.coefficientBudget q D)
    (by unfold CoerciveCriticalBounds.coefficientBudget; nlinarith [Nat.zero_le (MvMass.mass q ^ 2)])
    (fun j e => (CoerciveCriticalBounds.finSystem_entryBounds q D hD coordinate j e).mass)

theorem outer_degree (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (coordinate : Fin n) : (polynomial q D coordinate).natDegree ≤ blockDimension n D := by
  simpa [polynomial, blockDimension, columnCount, Nat.add_assoc] using
    ProjectiveBoxGramEliminant.outer_degree (finSystem q D coordinate) (finDegree D)
      (CoerciveCoordinateEliminant.width n D) 1
      (fun j e => (CoerciveCriticalBounds.finSystem_entryBounds q D hD coordinate j e).outerDegree)

theorem inner_degree (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (coordinate : Fin n) (j : ℕ) : ((polynomial q D coordinate).coeff j).natDegree ≤ blockDimension n D := by
  simpa [polynomial, blockDimension, columnCount, Nat.add_assoc] using
    ProjectiveBoxGramEliminant.inner_degree (finSystem q D coordinate) (finDegree D)
      (CoerciveCoordinateEliminant.width n D) 1
      (fun j e k => (CoerciveCriticalBounds.finSystem_entryBounds q D hD coordinate j e).innerDegree k) j

end LeanCanny.Algebra.CoerciveBoxGramEliminant
