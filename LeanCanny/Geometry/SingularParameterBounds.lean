/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.SystemCoordinateBounds
public import LeanCanny.Algebra.PartialDerivativeDegree
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Bounded exceptional parameters for generically simple integer systems

The first variable is the parameter; the other variables are spatial. A
qualitative finite exceptional set is enough to construct a new integer factor
with degree and mass bounds from the equations alone. The original generic
regularity certificate needs no arithmetic bound.
-/

@[expose] public section
namespace LeanCanny.Geometry.SingularParameterBounds
open scoped Classical BigOperators
open MvPolynomial Set LeanCanny.Algebra
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

noncomputable def jacobian (q : Fin n → MvPolynomial (Fin (n + 1)) ℤ) :
    MvPolynomial (Fin (n + 1)) ℤ := Matrix.det (fun i j => pderiv j.succ (q i))

theorem jacobian_degree (q : Fin n → MvPolynomial (Fin (n + 1)) ℤ) (D : ℕ)
    (hD : ∀ i, (q i).totalDegree ≤ D) : (jacobian q).totalDegree ≤ n * D := by
  rw [jacobian, Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro σ _
  rw [Units.smul_def]
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _j : Fin n, D := Finset.sum_le_sum fun j _ =>
      (PartialDerivativeDegree.degree_le (q (σ j)) j.succ).trans ((Nat.sub_le _ _).trans (hD _))
    _ = _ := by simp

def jacobianMassExponent (n D b : ℕ) : ℕ := n * (n.size + D.size + b)

private theorem unit_smul (u : ℤˣ) (p : MvPolynomial (Fin (n + 1)) ℤ) :
    MvMass.mass (u • p) = MvMass.mass p := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h, Units.smul_def]

theorem jacobian_mass (q : Fin n → MvPolynomial (Fin (n + 1)) ℤ) (D b : ℕ)
    (hD : ∀ i, (q i).totalDegree ≤ D) (hb : ∀ i, MvMass.mass (q i) ≤ 2 ^ b) :
    MvMass.mass (jacobian q) ≤ 2 ^ jacobianMassExponent n D b := by
  have hpartial (i j : Fin n) : MvMass.mass (pderiv j.succ (q i)) ≤ 2 ^ (D.size + b) := by
    apply (MvMass.pderiv_le _ _).trans
    calc
      _ ≤ D * 2 ^ b := Nat.mul_le_mul (hD i) (hb i)
      _ ≤ 2 ^ D.size * 2 ^ b := Nat.mul_le_mul_right _ (Nat.lt_size_self D).le
      _ = _ := (pow_add _ _ _).symm
  have hmass : MvMass.mass (jacobian q) ≤ n.factorial * (2 ^ (D.size + b)) ^ n := by
    rw [jacobian, Matrix.det_apply]
    calc
      _ ≤ ∑ σ : Equiv.Perm (Fin n), MvMass.mass
          (Equiv.Perm.sign σ • ∏ j, pderiv j.succ (q (σ j))) := MvMass.sum_le _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ _j : Fin n, 2 ^ (D.size + b) := by
        apply Finset.sum_le_sum
        intro σ _
        rw [unit_smul]
        exact (MvMass.prod_le _ _).trans (Finset.prod_le_prod fun j _ => hpartial _ j)
      _ = _ := by simp [Fintype.card_perm]
  calc
    _ ≤ n.factorial * (2 ^ (D.size + b)) ^ n := hmass
    _ ≤ (2 ^ n.size) ^ n * (2 ^ (D.size + b)) ^ n := Nat.mul_le_mul_right _
      ((Nat.factorial_le_pow n).trans (Nat.pow_le_pow_left (Nat.lt_size_self n).le n))
    _ = _ := by
      rw [← mul_pow, ← pow_add, ← pow_mul]
      congr 1
      unfold jacobianMassExponent
      ring

abbrev SingularValues (q : Fin n → MvPolynomial (Fin (n + 1)) ℤ) : Set ℝ :=
  {t | ∃ z : Fin (n + 1) → ℝ,
    (∀ j, (q j).eval₂ (Int.castRingHom ℝ) z = 0) ∧
      (jacobian q).eval₂ (Int.castRingHom ℝ) z = 0 ∧ z 0 = t}

def systemDegree (n D : ℕ) : ℕ := D + n * D
def systemMassExponent (n D b : ℕ) : ℕ := b + jacobianMassExponent n D b
def factorMassExponent (n D b : ℕ) : ℕ :=
  CoerciveRadiusBits.massExponent (n + 1) (2 * systemDegree n D)
    ((n + 1).size + 2 * systemMassExponent n D b)

/-- Finitely many singular parameters have a bounded integer exceptional
factor, even if some singular fibers have positive dimension. -/
theorem exists_bounded_of_finite (q : Fin n → MvPolynomial (Fin (n + 1)) ℤ) (D b : ℕ)
    (hD : ∀ i, (q i).totalDegree ≤ D) (hb : ∀ i, MvMass.mass (q i) ≤ 2 ^ b)
    (hfinite : (SingularValues q).Finite) :
    ∃ r : Polynomial ℤ, r ≠ 0 ∧
      r.natDegree ≤ CoerciveCoordinateEliminant.columnBound (n + 1) (2 * systemDegree n D) ∧
      coefficientMass r < 2 ^ factorMassExponent n D b ∧
      ∀ z : Fin (n + 1) → ℝ, (∀ j, (q j).eval₂ (Int.castRingHom ℝ) z = 0) →
        r.eval₂ (Int.castRingHom ℝ) (z 0) ≠ 0 →
          (jacobian q).eval₂ (Int.castRingHom ℝ) z ≠ 0 := by
  let F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℤ := Fin.cons (jacobian q) q
  have hFD (i : Fin (n + 1)) : (F i).totalDegree ≤ systemDegree n D := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (jacobian_degree q D hD).trans (Nat.le_add_left _ _)
    · exact (hD j).trans (Nat.le_add_right _ _)
  have hFb (i : Fin (n + 1)) : MvMass.mass (F i) ≤ 2 ^ systemMassExponent n D b := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (jacobian_mass q D b hD hb).trans
        (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
    · exact (hb j).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  have heval (z : Fin (n + 1) → ℝ) :
      (∀ j, (F j).eval₂ (Int.castRingHom ℝ) z = 0) ↔
        (jacobian q).eval₂ (Int.castRingHom ℝ) z = 0 ∧
          ∀ j, (q j).eval₂ (Int.castRingHom ℝ) z = 0 := by
    simp only [F, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
  have hf : {t : ℝ | ∃ z : Fin (n + 1) → ℝ,
      (∀ j, (F j).eval₂ (Int.castRingHom ℝ) z = 0) ∧ z 0 = t}.Finite := by
    apply hfinite.subset
    rintro t ⟨z, hz, ht⟩
    exact ⟨z, (heval z).mp hz |>.2, (heval z).mp hz |>.1, ht⟩
  obtain ⟨r, hr, hd, hm, hann⟩ := SystemCoordinateBounds.exists_bounded F
    (systemDegree n D) (systemMassExponent n D b) hFD hFb 0 hf
  refine ⟨r, hr, hd, hm, ?_⟩
  intro z hz hrz hj
  exact hrz (hann z ((heval z).mpr ⟨hj, hz⟩))

/-- A qualitative generic regularity factor can be replaced with a bounded
integer factor; its coefficients and degree are never used. -/
theorem exists_bounded (q : Fin n → MvPolynomial (Fin (n + 1)) ℤ) (D b : ℕ)
    (hD : ∀ i, (q i).totalDegree ≤ D) (hb : ∀ i, MvMass.mass (q i) ≤ 2 ^ b)
    (d : Polynomial ℝ) (hd : d ≠ 0)
    (hgeneric : ∀ z : Fin (n + 1) → ℝ, (∀ j, (q j).eval₂ (Int.castRingHom ℝ) z = 0) →
      d.eval (z 0) ≠ 0 → (jacobian q).eval₂ (Int.castRingHom ℝ) z ≠ 0) :
    ∃ r : Polynomial ℤ, r ≠ 0 ∧
      r.natDegree ≤ CoerciveCoordinateEliminant.columnBound (n + 1) (2 * systemDegree n D) ∧
      coefficientMass r < 2 ^ factorMassExponent n D b ∧
      ∀ z : Fin (n + 1) → ℝ, (∀ j, (q j).eval₂ (Int.castRingHom ℝ) z = 0) →
        r.eval₂ (Int.castRingHom ℝ) (z 0) ≠ 0 →
          (jacobian q).eval₂ (Int.castRingHom ℝ) z ≠ 0 := by
  apply exists_bounded_of_finite q D b hD hb
  apply (Polynomial.finite_setOfPred_isRoot hd).subset
  rintro t ⟨z, hz, hj, rfl⟩
  change d.eval (z 0) = 0
  by_contra ht
  exact hgeneric z hz ht hj

end LeanCanny.Geometry.SingularParameterBounds
