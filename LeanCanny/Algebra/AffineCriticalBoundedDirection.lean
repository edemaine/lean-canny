/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineCriticalPowerBadSystem

/-! # Bounded integer critical directions on regular affine slices

A nonzero Macaulay minor for the projective bad-root system bounds the
objective parameters. The bound has polynomial binary length in unary
ambient dimension and binary source degree. The hypotheses require affine
slice regularity and leading-cone transversality over field extensions.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineCriticalBoundedDirection
open MvPolynomial AffineCriticalPowerBadSystem
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} {n : ℕ} [Field K] [CharZero K]

def width (n D : ℕ) : ℕ := 4 * n + D.size + 5
def allowance (n D : ℕ) : ℕ := FixedWidthPolynomial.count (2 * n + 2) (width n D) * (2 * n + 1)
def binaryWidth (n D : ℕ) : ℕ := (2 * n + 2) * width n D + (2 * n + 1).size

theorem level_lt_width (D : ℕ) (hD : 1 < D) (s : Finset (Fin n)) :
    Macaulay.level (nativeDegrees D s) < 2 ^ width n D := by
  let C := (2 * n + 2) * ((2 * n + 2) * D)
  let T := (2 * n + 2) + (2 * n + 2) + D.size
  have hlevel : Macaulay.level (nativeDegrees D s) ≤ C + 1 := by
    have hs : (∑ j : Fin (2 * n + 2), (nativeDegrees D s j - 1)) ≤ C := by
      calc
        _ ≤ ∑ _j : Fin (2 * n + 2), badDegree n D := Finset.sum_le_sum fun j _ =>
          (Nat.sub_le _ _).trans (degrees_le D hD s ((layout n).symm j))
        _ = C := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, badDegree, C]
    unfold Macaulay.level
    omega
  have hC : C < 2 ^ T := by
    calc
      C = ((2 * n + 2) * (2 * n + 2)) * D := by dsimp [C]; ring
      _ ≤ (2 ^ (2 * n + 2) * 2 ^ (2 * n + 2)) * D := Nat.mul_le_mul_right D
        (Nat.mul_le_mul Nat.lt_two_pow_self.le Nat.lt_two_pow_self.le)
      _ < (2 ^ (2 * n + 2) * 2 ^ (2 * n + 2)) * 2 ^ D.size :=
        Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self D) (by positivity)
      _ = 2 ^ T := by rw [← pow_add, ← pow_add]
  have hw : width n D = T + 1 := by dsimp [width, T]; omega
  rw [hw, pow_succ]
  have hpos : 0 < 2 ^ T := by positivity
  omega

theorem allowance_size_le (n D : ℕ) : (allowance n D).size ≤ binaryWidth n D :=
  ProjectiveDirectionGrid.allowance_size_le (2 * n + 1) (width n D) (2 * n + 1)

theorem allowance_lt_two_pow (n D : ℕ) : allowance n D < 2 ^ binaryWidth n D :=
  (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (allowance_size_le n D))

/-- No exceptional factor, factor degree, or algebraic coefficient-height
budget is supplied to this direction-existence theorem. -/
theorem exists_bounded_root_free (low H : MvPolynomial (Fin n) K) (D : ℕ)
    (hlow : low.totalDegree < D) (hH : H.IsHomogeneous D) (hD : 1 < D)
    (s : Finset (Fin n)) (hs : s.card < n) (A : Fin n → Fin n → K) (β : Fin n → K)
    (hcone : ∀ (L : Type u) [Field L] [Algebra K L], AffineConeFlag.Transverse (L := L) H s A)
    (hslice : ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin n → L), aeval x (low + H) = 0 →
      (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = algebraMap K L (β r)) →
      GenericAffineCriticalJacobian.ConstraintIndependent (low + H) s A x) :
    ∃ v : Fin n → ℕ, (∀ i, v i ≤ allowance n D) ∧
      ∀ (L : Type u) [Field L] [Algebra K L] (z : Fin (2 * n + 2) → L),
        (∀ j, (nativeRows (low + H) D s A β j).eval₂ (eval₂Hom (algebraMap K L) (fun i => (v i : L))) z = 0) → z = 0 := by
  let R := MvPolynomial (Fin n) K
  let F := FractionRing R
  let L := AlgebraicClosure F
  let φ : R →+* L := (algebraMap F L).comp (algebraMap R F)
  let : Algebra K L := (φ.comp C).toAlgebra
  have hinj : Function.Injective φ :=
    (algebraMap F L).injective.comp (IsFractionRing.injective R F)
  have hφ : φ.comp C = algebraMap K L := rfl
  have hr (z : Fin (2 * n + 2) → L)
      (hz : ∀ j, (nativeRows (low + H) D s A β j).eval₂ φ z = 0) : z = 0 :=
    native_no_root φ hφ hinj low H D hlow hH hD s hs A β (hcone L) (hslice L) z hz
  exact ProjectiveDirectionGrid.exists_bounded (nativeRows (low + H) D s A β) (nativeDegrees D s)
    (width n D) (2 * n + 1) (level_lt_width D hD s) (native_homogeneous (low + H) D s A β)
    (fun j => degrees_pos D hD s ((layout n).symm j)) (native_parameter_degree (low + H) D s A β) φ hr

end LeanCanny.Algebra.AffineCriticalBoundedDirection
