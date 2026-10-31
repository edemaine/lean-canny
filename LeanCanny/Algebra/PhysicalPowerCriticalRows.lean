/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCriticalStage
public import LeanCanny.Algebra.CoordinatePowerReal

/-! # Critical equations with fixed parameter powers and new physical powers

Derivatives are taken before power substitution. Physical coordinates use
power W; multipliers use (D-1)W. Old scalar parameters retain their own
powers. Odd powers give an exact equivalence on all real critical roots,
including singular roots and every multiplier coordinate.
-/

@[expose] public section
namespace LeanCanny.Algebra.PhysicalPowerCriticalRows
open MvPolynomial FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {ι R : Type*} {n : ℕ} [CommRing R]

def powers (w : ι → ℕ) (D W : ℕ) : (ι ⊕ Variables n) → ℕ
  | .inl i => w i
  | .inr (.inl _) => W
  | .inr (.inr _) => (D - 1) * W

noncomputable def rows (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (H : Fin n → MvPolynomial ι R) (w : ι → ℕ) (D W : ℕ)
    (j : Variables n) : MvPolynomial (ι ⊕ Variables n) R :=
  CoordinatePowerSubstitution.substitute (powers w D W) (FlatAffineCriticalStage.row p s a H j)

def degrees (s : Finset (Fin n)) (D W : ℕ) : Variables n → ℕ
  | .inl _ => (D - 1) * W
  | .inr j => Fin.cases (D * W) (fun i => if i ∈ s then W else (D - 1) * W) j

def point {K : Type*} [Monoid K] (w : ι → ℕ) (D W : ℕ) (z : (ι ⊕ Variables n) → K) :
    (ι ⊕ Variables n) → K := fun i => z i ^ powers w D W i

theorem point_parameter {K : Type*} [Monoid K] (w : ι → ℕ) (D W : ℕ)
    (z : (ι ⊕ Variables n) → K) (i : ι) : point w D W z (Sum.inl i) = z (Sum.inl i) ^ w i := rfl

theorem point_ambient {K : Type*} [Monoid K] (w : ι → ℕ) (D W : ℕ)
    (z : (ι ⊕ Variables n) → K) (i : Fin n) : point w D W z (ambient i) = z (ambient i) ^ W := rfl

theorem point_multiplier {K : Type*} [Monoid K] (w : ι → ℕ) (D W : ℕ)
    (z : (ι ⊕ Variables n) → K) (j : Fin (n + 1)) :
    point w D W z (multiplier j) = z (multiplier j) ^ ((D - 1) * W) := rfl

theorem roots_iff_original {K : Type*} [CommRing K] (φ : R →+* K)
    (p : MvPolynomial (Fin n) R) (s : Finset (Fin n)) (a : Fin (n + 1) → Fin n → R)
    (H : Fin n → MvPolynomial ι R) (w : ι → ℕ) (D W : ℕ) (z : (ι ⊕ Variables n) → K) :
    (∀ j, (rows p s a H w D W j).eval₂ φ z = 0) ↔
      ∀ j, (FlatAffineCriticalStage.row p s a H j).eval₂ φ (point w D W z) = 0 := by
  simp only [rows, CoordinatePowerSubstitution.eval_substitute]
  rfl

theorem powers_odd (w : ι → ℕ) (hw : ∀ i, Odd (w i)) (D W : ℕ)
    (hD : Odd (D - 1)) (hW : Odd W) : ∀ i : ι ⊕ Variables n, Odd (powers w D W i) := by
  intro i
  cases i with
  | inl i => exact hw i
  | inr j =>
    cases j with
    | inl _ => exact hW
    | inr _ => exact hD.mul hW

noncomputable def realRootEquiv (p : MvPolynomial (Fin n) ℤ) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → ℤ) (H : Fin n → MvPolynomial ι ℤ)
    (w : ι → ℕ) (hw : ∀ i, Odd (w i)) (D W : ℕ) (hD : Odd (D - 1)) (hW : Odd W) :
    {z : (ι ⊕ Variables n) → ℝ // ∀ j, (rows p s a H w D W j).eval₂ (Int.castRingHom ℝ) z = 0} ≃
    {z : (ι ⊕ Variables n) → ℝ // ∀ j, (FlatAffineCriticalStage.row p s a H j).eval₂ (Int.castRingHom ℝ) z = 0} :=
  (CoordinatePowerSubstitution.realPowerHomeomorph (powers w D W) (powers_odd w hw D W hD hW)).toEquiv.subtypeEquiv
    (roots_iff_original (Int.castRingHom ℝ) p s a H w D W)

end LeanCanny.Algebra.PhysicalPowerCriticalRows
