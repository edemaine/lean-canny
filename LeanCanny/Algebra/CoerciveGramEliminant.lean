/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveGramEliminant
public import LeanCanny.Algebra.CoerciveCoordinateEliminant

/-! # Canonical integer Gram annihilants of coercive critical coordinates

These fixed determinants replace selected maximal minors. Their construction
contains no choice of matrix rows, and the actual homogeneous critical system
supplies both annihilation and a real specialization proving nonvanishing.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoerciveGramEliminant
open CoerciveCriticalHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

noncomputable def polynomial (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (coordinate : Fin n) : Coefficient :=
  ProjectiveGramEliminant.polynomial (finSystem q D coordinate) (finDegree D)
    (CoerciveCoordinateEliminant.width n D)

theorem ne_zero (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (coordinate : Fin n) : polynomial q D coordinate ≠ 0 := by
  obtain ⟨t, ht⟩ := finSystem_exists_real_no_complex_projective_root q D hD coordinate
  apply ProjectiveGramEliminant.ne_zero_of_real_specialization (finSystem q D coordinate)
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
  ProjectiveGramEliminant.eval_eq_zero_of_common_root (finSystem q D coordinate) (finDegree D)
    (CoerciveCoordinateEliminant.width n D) (CoerciveCoordinateEliminant.level_lt n D)
    (finSystem_homogeneous q D coordinate) (parameterMap s (x coordinate)) (finPoint x)
    (finSystem_critical_root q D hD coordinate s x hx) (finPoint_nonzero x)

noncomputable def massBound (q : MvPolynomial (Fin n) ℤ) (D : ℕ) : ℕ :=
  let d := finDegree (n := n) D
  let W := CoerciveCoordinateEliminant.width n D
  let C := Fintype.card (Macaulay.activeIndices d W)
  let R := Fintype.card (Macaulay.MultiplierIndex d W)
  C.factorial * (R * CoerciveCriticalBounds.coefficientBudget q D ^ 2) ^ C

theorem mass_le (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (coordinate : Fin n) : NestedMass.mass (polynomial q D coordinate) ≤ massBound q D :=
  ProjectiveGramEliminant.mass_le (finSystem q D coordinate) (finDegree D)
    (CoerciveCoordinateEliminant.width n D) (CoerciveCriticalBounds.coefficientBudget q D)
    (fun j e => (CoerciveCriticalBounds.finSystem_entryBounds q D hD coordinate j e).mass)

end LeanCanny.Algebra.CoerciveGramEliminant
