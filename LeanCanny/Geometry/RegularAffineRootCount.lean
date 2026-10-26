/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.UniformAffineCoordinates
public import LeanCanny.Geometry.RootBranchCount

/-! # Counting regular integer affine roots

The concrete coordinate eliminants bound the whole root set of a square
integer system whenever all its roots are analytically simple. No finite-root
assumption, parameter specialization, or coefficient-height budget is needed
for this count. Uniform degree bounds give a polynomial binary label width.
-/

@[expose] public section
namespace LeanCanny.Geometry.RegularAffineRootCount
open MvPolynomial LeanCanny.Algebra
open scoped Classical BigOperators

variable {n : ℕ}

abbrev Roots (q : Fin n → MvPolynomial (Fin n) ℤ) :=
  {x : Fin n → ℝ // ∀ j, (q j).eval₂ (Int.castRingHom ℝ) x = 0}

def labelWidth (n D : ℕ) : ℕ := n * (n + 1) * (n * (D - 1) + 1).size

theorem finite_card_le (q : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ d j) (hd : ∀ j, 0 < d j)
    (hregular : ∀ x : Roots q,
      (fderiv ℝ (fun y => fun j => (q j).eval₂ (Int.castRingHom ℝ) y) x.val).IsInvertible) :
    Finite (Roots q) ∧ Nat.card (Roots q) ≤ UniformAffineCoordinates.count d ^ n := by
  let W := UniformAffineCoordinates.width d
  let P := fun i => AffineCoordinateEliminant.polynomial q d i W
  have hP (i : Fin n) : (P i).map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.cast_injective)).mpr
      (AffineCoordinateEliminant.ne_zero q d i W)
  have hbound := RootBranchCount.finite_card_le (fun x : Roots q => x.val) Subtype.val_injective
    (fun i => (P i).map (Int.castRingHom ℝ)) hP (fun x i => by
      rw [Polynomial.eval_map]
      exact AffineCoordinateEliminant.eval_eq_zero (Int.castRingHom ℝ) q d hD hd i W
        (Nat.lt_size_self _) x.val x.property (hregular x))
  refine ⟨hbound.1, hbound.2.trans ?_⟩
  calc
    ∏ i, ((P i).map (Int.castRingHom ℝ)).natDegree ≤
        ∏ _i : Fin n, UniformAffineCoordinates.count d :=
      Finset.prod_le_prod (fun i _ => Polynomial.natDegree_map_le.trans
        (AffineCoordinateEliminant.degree_le q d i W))
    _ = UniformAffineCoordinates.count d ^ n := by simp

theorem count_uniform (D : ℕ) :
    UniformAffineCoordinates.count (fun _ : Fin n => D) ^ n = 2 ^ labelWidth n D := by
  have hl : Macaulay.level (AffineCoordinateSystem.degrees (fun _ : Fin n => D)) = n * (D - 1) + 1 := by
    simp [Macaulay.level, AffineCoordinateSystem.degrees, Fin.sum_univ_succ]
  simp only [UniformAffineCoordinates.count, UniformAffineCoordinates.width, hl,
    FixedWidthPolynomial.count, ← pow_mul, labelWidth]
  congr 1
  ring

theorem finite_card_le_uniform (q : Fin n → MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ D) (hpos : 0 < D)
    (hregular : ∀ x : Roots q,
      (fderiv ℝ (fun y => fun j => (q j).eval₂ (Int.castRingHom ℝ) y) x.val).IsInvertible) :
    Finite (Roots q) ∧ Nat.card (Roots q) ≤ 2 ^ labelWidth n D := by
  simpa only [count_uniform] using finite_card_le q (fun _ => D) hD (fun _ => hpos) hregular

end LeanCanny.Geometry.RegularAffineRootCount
