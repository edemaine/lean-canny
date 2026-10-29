/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectionCriticalFamily
public import LeanCanny.Algebra.PartialDerivativeDegree
public import LeanCanny.Algebra.MvCoefficientMass

/-! # Critical sampling stages retaining the complete ambient tuple

Inside the free block the equations are original-source critical equations.
Outside it, linear equations copy the corresponding ancestral coordinates.
The original polynomial is renamed, never composed with an earlier primitive
parameter. Row bounds therefore depend only on the original source and the
direction, independently of the number of ancestral stages.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatCriticalStage
open MvPolynomial
open scoped Classical

variable {ι R : Type*} {n : ℕ} [CommRing R]

noncomputable def oldCoordinate : Option ι → MvPolynomial (ι ⊕ Fin n) R
  | none => 0
  | some i => X (Sum.inl i)

def oldValue {K : Type*} [Zero K] (z : (ι ⊕ Fin n) → K) : Option ι → K
  | none => 0
  | some i => z (Sum.inl i)

noncomputable def row (p : MvPolynomial (Fin n) R) (s : Finset (Fin n)) (base : Fin n)
    (v : Fin n → R) (old : Fin n → Option ι) (i : Fin n) : MvPolynomial (ι ⊕ Fin n) R :=
  if i ∈ s then rename Sum.inr (ProjectionCriticalFamily.spatialEquation p base v i)
  else X (Sum.inr i) - oldCoordinate (old i)

theorem eval_oldCoordinate {K : Type*} [CommRing K] (φ : R →+* K)
    (z : (ι ⊕ Fin n) → K) (o : Option ι) :
    (oldCoordinate (R := R) o).eval₂ φ z = oldValue z o := by
  cases o <;> simp only [oldCoordinate, oldValue, eval₂_zero, eval₂_X]

theorem roots_iff {K : Type*} [CommRing K] (φ : R →+* K)
    (p : MvPolynomial (Fin n) R) (s : Finset (Fin n)) (base : Fin n)
    (v : Fin n → R) (old : Fin n → Option ι) (z : (ι ⊕ Fin n) → K) :
    (∀ i, (row p s base v old i).eval₂ φ z = 0) ↔
      (∀ i ∈ s, (ProjectionCriticalFamily.spatialEquation p base v i).eval₂ φ (z ∘ Sum.inr) = 0) ∧
        ∀ i, i ∉ s → z (Sum.inr i) = oldValue z (old i) := by
  constructor
  · intro h
    constructor
    · intro i hi
      simpa only [row, ite_eq_left hi, eval₂_rename] using h i
    · intro i hi
      simpa only [row, ite_eq_right hi, eval₂_sub, eval₂_X, eval_oldCoordinate, sub_eq_zero] using h i
  · rintro ⟨hc, ho⟩ i
    by_cases hi : i ∈ s
    · simpa only [row, ite_eq_left hi, eval₂_rename] using hc i hi
    · simpa only [row, ite_eq_right hi, eval₂_sub, eval₂_X, eval_oldCoordinate, sub_eq_zero] using ho i hi

theorem spatial_degree (p : MvPolynomial (Fin n) R) (base : Fin n) (v : Fin n → R) (i : Fin n) :
    (ProjectionCriticalFamily.spatialEquation p base v i).totalDegree ≤ p.totalDegree := by
  unfold ProjectionCriticalFamily.spatialEquation
  split_ifs
  · exact le_rfl
  · apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (PartialDerivativeDegree.degree_le _ _).trans (Nat.sub_le _ _)
    · exact (totalDegree_mul _ _).trans (by
        simpa only [totalDegree_C, Nat.zero_add] using
          (PartialDerivativeDegree.degree_le p base).trans (Nat.sub_le _ _))

theorem oldCoordinate_degree [Nontrivial R] (o : Option ι) :
    (oldCoordinate (R := R) (n := n) o).totalDegree ≤ 1 := by
  cases o <;> simp [oldCoordinate]

theorem degree_le [Nontrivial R] (p : MvPolynomial (Fin n) R) (s : Finset (Fin n)) (base : Fin n)
    (v : Fin n → R) (old : Fin n → Option ι) (i : Fin n) :
    (row p s base v old i).totalDegree ≤ max p.totalDegree 1 := by
  unfold row
  split_ifs
  · exact (totalDegree_rename_le _ _).trans ((spatial_degree p base v i).trans (Nat.le_max_left _ _))
  · apply (totalDegree_sub _ _).trans
    exact max_le (by simp) ((oldCoordinate_degree _).trans (Nat.le_max_right _ _))

theorem spatial_mass (p : MvPolynomial (Fin n) ℤ) (base : Fin n) (v : Fin n → ℤ)
    (U : ℕ) (hv : ∀ i, (v i).natAbs ≤ U) (i : Fin n) :
    MvMass.mass (ProjectionCriticalFamily.spatialEquation p base v i) ≤
      (p.totalDegree + 1) * (U + 1) * MvMass.mass p := by
  have hp (j : Fin n) := MvMass.pderiv_le p j
  unfold ProjectionCriticalFamily.spatialEquation
  split_ifs
  · have hf : 1 ≤ (p.totalDegree + 1) * (U + 1) :=
      Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_le_succ (Nat.zero_le _))
    simpa only [one_mul] using Nat.mul_le_mul_right (MvMass.mass p) hf
  · apply (MvMass.sub_le _ _).trans
    calc
      _ ≤ p.totalDegree * MvMass.mass p + U * (p.totalDegree * MvMass.mass p) :=
        Nat.add_le_add (hp i) ((MvMass.mul_le _ _).trans (by
          rw [MvMass.C]
          exact Nat.mul_le_mul (hv i) (hp base)))
      _ = p.totalDegree * (U + 1) * MvMass.mass p := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ _))

theorem oldCoordinate_mass (o : Option ι) : MvMass.mass (oldCoordinate (R := ℤ) (n := n) o) ≤ 1 := by
  cases o <;> simp [oldCoordinate]

theorem mass_le (p : MvPolynomial (Fin n) ℤ) (s : Finset (Fin n)) (base : Fin n)
    (v : Fin n → ℤ) (old : Fin n → Option ι) (U : ℕ) (hv : ∀ i, (v i).natAbs ≤ U) (i : Fin n) :
    MvMass.mass (row p s base v old i) ≤
      max 2 ((p.totalDegree + 1) * (U + 1) * MvMass.mass p) := by
  unfold row
  split_ifs
  · exact (MvMass.rename_le _ _).trans ((spatial_mass p base v U hv i).trans (Nat.le_max_right _ _))
  · apply (MvMass.sub_le _ _).trans
    have H := oldCoordinate_mass (n := n) (old i)
    rw [MvMass.X]
    exact (by omega : 1 + MvMass.mass (oldCoordinate (R := ℤ) (n := n) (old i)) ≤ 2).trans (Nat.le_max_left _ _)

end LeanCanny.Algebra.FlatCriticalStage
