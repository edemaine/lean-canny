/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialSystemReindex
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # A positive-dimensional completion of a square polynomial system

Append one coordinate and the equation that sets it to zero. Every root has
one extension, and the Jacobian determinant is unchanged after renaming.
This also applies to the empty system: its completion is the equation X = 0.
The indexed layout keeps every original coordinate at its old index.
-/

@[expose] public section
namespace LeanCanny.Algebra.PositivePolynomialSystem
open MvPolynomial TriangularPolynomialSystem
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def native (p : Fin n → MvPolynomial (Fin n) R) :
    (Fin n ⊕ Fin 1) → MvPolynomial (Fin n ⊕ Fin 1) R :=
  append p (fun j => X (Sum.inr j))

noncomputable def system (p : Fin n → MvPolynomial (Fin n) R) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) R :=
  PolynomialSystemReindex.system finSumFinEquiv (native p)

theorem old_row (p : Fin n → MvPolynomial (Fin n) R) (i : Fin n) :
    system p i.castSucc = rename Fin.castSucc (p i) := by
  simp only [system, PolynomialSystemReindex.system, finSumFinEquiv_symm_apply_castSucc,
    native, append, Sum.elim_inl, rename_rename, Function.comp_def,
    finSumFinEquiv_apply_left]
  rfl

theorem new_row (p : Fin n → MvPolynomial (Fin n) R) :
    system p (Fin.last n) = X (Fin.last n) := by
  simp only [system, PolynomialSystemReindex.system, finSumFinEquiv_symm_last,
    native, append, Sum.elim_inr, rename_X, finSumFinEquiv_apply_right]
  rfl

theorem roots_iff {K : Type*} [CommRing K] (φ : R →+* K)
    (p : Fin n → MvPolynomial (Fin n) R) (z : Fin (n + 1) → K) :
    (∀ j, (system p j).eval₂ φ z = 0) ↔
      (∀ i, (p i).eval₂ φ (z ∘ Fin.castSucc) = 0) ∧ z (Fin.last n) = 0 := by
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · simpa only [old_row, eval₂_rename] using h i.castSucc
    · simpa only [new_row, eval₂_X] using h (Fin.last n)
  · rintro ⟨h, hz⟩ j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [new_row, eval₂_X] using hz
    · simpa only [old_row, eval₂_rename] using h i

def extend {K : Type*} [Zero K] (x : Fin n → K) : Fin (n + 1) → K :=
  Fin.lastCases 0 x

theorem extend_old {K : Type*} [Zero K] (x : Fin n → K) (i : Fin n) :
    extend x i.castSucc = x i := by simp [extend]

theorem extend_last {K : Type*} [Zero K] (x : Fin n → K) :
    extend x (Fin.last n) = 0 := by simp [extend]

theorem eq_extend {K : Type*} [Zero K] (z : Fin (n + 1) → K) (hz : z (Fin.last n) = 0) :
    extend (z ∘ Fin.castSucc) = z := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [extend_last] using hz.symm
  · exact extend_old _ j

theorem roots_extend_iff {K : Type*} [CommRing K] (φ : R →+* K)
    (p : Fin n → MvPolynomial (Fin n) R) (x : Fin n → K) :
    (∀ j, (system p j).eval₂ φ (extend x) = 0) ↔ ∀ i, (p i).eval₂ φ x = 0 := by
  rw [roots_iff]
  have hx : extend x ∘ Fin.castSucc = x := funext (extend_old x)
  rw [hx, extend_last]
  simp

theorem jacobian_native (p : Fin n → MvPolynomial (Fin n) R) :
    jacobian (native p) = rename Sum.inl (jacobian p) := by
  rw [native, jacobian_append]
  simp [spatialJacobian, Matrix.det_unique, pderiv_X]

theorem jacobian_system (p : Fin n → MvPolynomial (Fin n) R) :
    jacobian (system p) = rename Fin.castSucc (jacobian p) := by
  rw [system, PolynomialSystemReindex.jacobian, jacobian_native, rename_rename]
  rfl

theorem regular_iff {K : Type*} [CommRing K] (φ : R →+* K)
    (p : Fin n → MvPolynomial (Fin n) R) (z : Fin (n + 1) → K) :
    (jacobian (system p)).eval₂ φ z ≠ 0 ↔
      (jacobian p).eval₂ φ (z ∘ Fin.castSucc) ≠ 0 := by
  rw [jacobian_system, eval₂_rename]

theorem degree_le [Nontrivial R] (p : Fin n → MvPolynomial (Fin n) R) (D : ℕ)
    (hD : 0 < D) (hp : ∀ i, (p i).totalDegree ≤ D) (j : Fin (n + 1)) :
    (system p j).totalDegree ≤ D := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [new_row]
    rw [totalDegree_X]
    exact hD
  · rw [old_row]
    exact (totalDegree_rename_le _ _).trans (hp i)

omit [CommRing R] in
theorem mass_le (p : Fin n → MvPolynomial (Fin n) ℤ) (B : ℕ)
    (hB : 0 < B) (hp : ∀ i, MvMass.mass (p i) ≤ B) (j : Fin (n + 1)) :
    MvMass.mass (system p j) ≤ B := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [new_row, MvMass.X]
    exact hB
  · rw [old_row]
    exact (MvMass.rename_le _ _).trans (hp i)

end LeanCanny.Algebra.PositivePolynomialSystem
