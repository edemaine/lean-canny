/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineCriticalConeSystem
public import LeanCanny.Algebra.ProjectiveDirectionFamily

/-! # Bounded integer directions transverse to an affine-height cone flag

The multiplier-power system has 2*n+1 homogeneous rows of degrees at most D
and parameter coefficient degree at most one. A maximal Macaulay minor
therefore gives an integer direction with polynomial binary length in n
and D.size. Old normals and cone transversality are hypotheses over field
extensions; affine regularity at finite levels is a separate condition.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineConeBoundedDirection
open MvPolynomial AffineCriticalConeSystem GenericAffineCriticalJacobian GenericAffineConeFlag
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} {n : ℕ} [Field K] [CharZero K]

def width (n D : ℕ) : ℕ := 2 * n + D.size + 2
def allowance (n D : ℕ) : ℕ := FixedWidthPolynomial.count (2 * n + 1) (width n D)
def binaryWidth (n D : ℕ) : ℕ := (2 * n + 1) * width n D + 1

theorem level_lt_width (D : ℕ) (hD : 1 < D) (s : Finset (Fin n)) :
    Macaulay.level (nativeDegrees D s) < 2 ^ width n D := by
  let C := (2 * n + 1) * D
  let T := (2 * n + 1) + D.size
  have hlevel : Macaulay.level (nativeDegrees D s) ≤ C + 1 := by
    have hs : (∑ j : Fin (2 * n + 1), (nativeDegrees D s j - 1)) ≤ C := by
      calc
        _ ≤ ∑ j : Fin (2 * n + 1), D := Finset.sum_le_sum fun j _ =>
          (Nat.sub_le _ _).trans (degrees_le D s (by omega) ((layout n).symm j))
        _ = C := by simp [C]
    unfold Macaulay.level
    omega
  have hC : C < 2 ^ T := by
    calc
      C ≤ 2 ^ (2 * n + 1) * D := Nat.mul_le_mul_right D (Nat.lt_two_pow_self.le)
      _ < 2 ^ (2 * n + 1) * 2 ^ D.size :=
        Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self D) (by positivity)
      _ = 2 ^ T := by rw [← pow_add]
  have hw : width n D = T + 1 := by dsimp [width, T]; omega
  rw [hw, pow_succ]
  have hpos : 0 < 2 ^ T := by positivity
  omega

theorem allowance_size_le (n D : ℕ) : (allowance n D).size ≤ binaryWidth n D := by
  have H := ProjectiveDirectionGrid.allowance_size_le (2 * n) (width n D) 1
  simpa only [Nat.mul_one, Nat.size_one, allowance, binaryWidth] using H

theorem allowance_lt_two_pow (n D : ℕ) : allowance n D < 2 ^ binaryWidth n D :=
  (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (allowance_size_le n D))

/-- The bound depends on source dimension and degree, without a supplied
exceptional polynomial or a bound on its coefficients. -/
theorem exists_bounded_root_free (p : MvPolynomial (Fin n) K) (D : ℕ)
    (hD : p.IsHomogeneous D) (hD2 : 1 < D) (s : Finset (Fin n)) (hs : s.card < n)
    (A : Fin n → Fin n → K)
    (hA : ∀ (L : Type u) [Field L] [Algebra K L], NormalIndependent (L := L) s A)
    (hcone : ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin n → L), aeval x p = 0 →
      (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = 0) → x ≠ 0 →
      ConstraintIndependent p s A x) :
    ∃ v : Fin n → ℕ, (∀ i, v i ≤ allowance n D) ∧
      ∀ (L : Type u) [Field L] [Algebra K L] (z : Fin (2 * n + 1) → L),
        (∀ j, (nativeRows p D s A j).eval₂ (eval₂Hom (algebraMap K L) (fun i => (v i : L))) z = 0) → z = 0 := by
  let R := MvPolynomial (Fin n) K
  let F := FractionRing R
  let L := AlgebraicClosure F
  let φ : R →+* L := (algebraMap F L).comp (algebraMap R F)
  let : Algebra K L := (φ.comp C).toAlgebra
  have hinj : Function.Injective φ :=
    (algebraMap F L).injective.comp (IsFractionRing.injective R F)
  have hφ : φ.comp C = algebraMap K L := rfl
  have hr (z : Fin (2 * n + 1) → L)
      (hz : ∀ j, (nativeRows p D s A j).eval₂ φ z = 0) : z = 0 :=
    native_no_root φ hφ hinj p D hD hD2 s hs A (hA L) (hcone L) z hz
  have H := ProjectiveDirectionGrid.exists_bounded (nativeRows p D s A) (nativeDegrees D s)
    (width n D) 1 (level_lt_width D hD2 s) (native_homogeneous p D hD s A)
    (fun j => degrees_pos D hD2 s ((layout n).symm j)) (native_parameter_degree p D s A) φ hr
  simpa only [Nat.mul_one, allowance] using H

end LeanCanny.Algebra.AffineConeBoundedDirection
