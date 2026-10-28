/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RegularAffineRootCount

/-! # Finite regular roots without regularity of every root

The coordinate eliminants annihilate each regular affine root individually.
Consequently the regular subset is finite and has the same uniform degree
bound, even when the original system also has singular or positive-dimensional
root families. No global regularity or finite-root premise is required.
-/

@[expose] public section
namespace LeanCanny.Geometry.RegularAffineRootCount
open MvPolynomial LeanCanny.Algebra
open scoped Classical BigOperators
variable {n : ℕ}

abbrev RegularRoots (q : Fin n → MvPolynomial (Fin n) ℤ) :=
  {x : Roots q // (fderiv ℝ (fun y => fun j => (q j).eval₂ (Int.castRingHom ℝ) y) x.val).IsInvertible}

theorem finite_regular_card_le (q : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ d j) (hd : ∀ j, 0 < d j) :
    Finite (RegularRoots q) ∧ Nat.card (RegularRoots q) ≤ UniformAffineCoordinates.count d ^ n := by
  let W := UniformAffineCoordinates.width d
  let P := fun i => AffineCoordinateEliminant.polynomial q d i W
  have hP (i : Fin n) : (P i).map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff Int.cast_injective).mpr (AffineCoordinateEliminant.ne_zero q d i W)
  have hbound := RootBranchCount.finite_card_le (fun x : RegularRoots q => x.val.val)
    (Subtype.val_injective.comp Subtype.val_injective) (fun i => (P i).map (Int.castRingHom ℝ)) hP (fun x i => by
      rw [Polynomial.eval_map]
      exact AffineCoordinateEliminant.eval_eq_zero (Int.castRingHom ℝ) q d hD hd i W
        (Nat.lt_size_self _) x.val.val x.val.property x.property)
  refine ⟨hbound.1, hbound.2.trans ?_⟩
  calc
    ∏ i, ((P i).map (Int.castRingHom ℝ)).natDegree ≤ ∏ _i : Fin n, UniformAffineCoordinates.count d :=
      Finset.prod_le_prod (fun i _ => Polynomial.natDegree_map_le.trans (AffineCoordinateEliminant.degree_le q d i W))
    _ = UniformAffineCoordinates.count d ^ n := by simp

theorem finite_regular_card_le_uniform (q : Fin n → MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ D) (hpos : 0 < D) :
    Finite (RegularRoots q) ∧ Nat.card (RegularRoots q) ≤ 2 ^ labelWidth n D := by
  simpa only [count_uniform] using finite_regular_card_le q (fun _ => D) hD (fun _ => hpos)

end LeanCanny.Geometry.RegularAffineRootCount
