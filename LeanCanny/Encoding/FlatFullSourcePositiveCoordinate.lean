/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourcePositive
public import LeanCanny.Geometry.AffineCoordinateEliminant

/-! # Coordinate eliminants for the positive-dimensional flat tower

One elimination applies to all ancestral coordinates and the zero dummy
coordinate. Derived width is positive and contains every original row degree
at every input, including depth zero. Degree and coefficient-bit budgets have
native controls. Regular original roots extend to the same coordinate roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourcePositiveCoordinate
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatFullSourceTower (Inputs degree mass)
open FlatFullSourcePositive (system count)
open scoped Classical
attribute [local irreducible] FlatFullSourceTower.system FlatFullSourceTower.degree FlatFullSourceTower.mass

noncomputable def level (F : Inputs) (u : List Bool) : ℕ := count F u * (degree F u - 1) + 1
noncomputable def width (F : Inputs) (u : List Bool) : ℕ := (level F u).size
noncomputable def matrixCount (F : Inputs) (u : List Bool) : ℕ :=
  FixedWidthPolynomial.count (count F u + 1) (width F u)
noncomputable def coefficientBits (F : Inputs) (u : List Bool) : ℕ :=
  (matrixCount F u).size * matrixCount F u + matrixCount F u * (mass F u + 3) + 1

theorem level_binary {F : Inputs} (h : F.Access) : BinaryFn (level F) :=
  (((BinaryFn.ofUnary (FlatFullSourcePositive.count_unary h)).mul
    ((FlatFullSourceTower.degree_binary h).sub (BinaryFn.const 1)))).add (BinaryFn.const 1)

theorem width_unary {F : Inputs} (h : F.Access) : UnaryFn (width F) :=
  (UnaryFn.length (level_binary h).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

theorem matrixCount_binary {F : Inputs} (h : F.Access) : BinaryFn (matrixCount F) := by
  apply BinaryFn.of_bits
  exact mem_FP_of_eq (FixedWidthPolynomial.countCode_mem_FP
    ((FlatFullSourcePositive.count_unary h).add (UnaryFn.const 1)) (width_unary h))
    (fun u => FixedWidthPolynomial.countCode_code (fun u => count F u + 1) (width F) u)

theorem coefficientBits_binary {F : Inputs} (h : F.Access) : BinaryFn (coefficientBits F) := by
  have hc := matrixCount_binary h
  exact ((hc.size.mul hc).add (hc.mul ((FlatFullSourceTower.mass_binary h).add (BinaryFn.const 3)))).add
    (BinaryFn.const 1)

theorem level_eq (F : Inputs) (u : List Bool) :
    Macaulay.level (AffineCoordinateSystem.degrees (fun _ : Fin (count F u) => degree F u)) = level F u := by
  simp [Macaulay.level, AffineCoordinateSystem.degrees, Fin.sum_univ_succ, level]

theorem degree_lt_width (F : Inputs) (u : List Bool) : degree F u < 2 ^ width F u := by
  have hd := FlatFullSourceTower.degree_pos F u
  have hn := FlatFullSourcePositive.count_pos F u
  have hm : degree F u - 1 ≤ count F u * (degree F u - 1) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (degree F u - 1) (show 1 ≤ count F u by omega)
  exact (show degree F u ≤ level F u by unfold level; omega).trans_lt (Nat.lt_size_self _)

theorem width_pos (F : Inputs) (u : List Bool) : 0 < width F u := by
  have hd := FlatFullSourceTower.degree_pos F u
  have hw := degree_lt_width F u
  by_contra h
  have hz : width F u = 0 := by omega
  rw [hz, pow_zero] at hw
  omega

noncomputable def polynomial (F : Inputs) (u : List Bool) (i : Fin (count F u)) : Polynomial ℤ :=
  AffineCoordinateEliminant.polynomial (system F u) (fun _ => degree F u) i (width F u)

theorem ne_zero (F : Inputs) (u : List Bool) (i : Fin (count F u)) : polynomial F u i ≠ 0 :=
  AffineCoordinateEliminant.ne_zero _ _ _ _

theorem polynomial_degree (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    (polynomial F u i).natDegree ≤ matrixCount F u := AffineCoordinateEliminant.degree_le _ _ _ _

theorem polynomial_coefficient_bits (F : Inputs) (u : List Bool) (i : Fin (count F u)) (j : ℕ) :
    ((polynomial F u i).coeff j).natAbs.size ≤ coefficientBits F u :=
  AffineCoordinateEliminant.coefficient_size_le _ _ _ _ _
    (fun row _ => (MvMass.coeff_le _ _).trans (FlatFullSourcePositive.polynomial_mass F u row)) j

theorem eval_regular_root (F : Inputs) (u : List Bool) (z : Fin (count F u) → ℝ)
    (hz : ∀ i, (system F u i).eval₂ (Int.castRingHom ℝ) z = 0)
    (hr : (fderiv ℝ (fun y => fun i => (system F u i).eval₂ (Int.castRingHom ℝ) y) z).IsInvertible)
    (i : Fin (count F u)) : (polynomial F u i).eval₂ (Int.castRingHom ℝ) (z i) = 0 :=
  AffineCoordinateEliminant.eval_eq_zero _ _ _ (FlatFullSourcePositive.polynomial_degree F u)
    (fun _ => FlatFullSourceTower.degree_pos F u) i (width F u)
    (by rw [level_eq]; exact Nat.lt_size_self _) z hz hr

theorem eval_original_regular_root (F : Inputs) (u : List Bool)
    (z : Fin (FlatFullSourceTower.count F u) → ℝ)
    (hz : ∀ i, (FlatFullSourceTower.system F u i).eval₂ (Int.castRingHom ℝ) z = 0)
    (hr : (fderiv ℝ (fun y => fun i => (FlatFullSourceTower.system F u i).eval₂ (Int.castRingHom ℝ) y) z).IsInvertible)
    (i : Fin (FlatFullSourceTower.count F u)) :
    (polynomial F u i.castSucc).eval₂ (Int.castRingHom ℝ) (z i) = 0 := by
  have he : PositivePolynomialSystem.extend z ∘ Fin.castSucc = z :=
    funext (PositivePolynomialSystem.extend_old z)
  have hr' : (fderiv ℝ (fun y => fun j => (system F u j).eval₂ (Int.castRingHom ℝ) y)
      (PositivePolynomialSystem.extend z)).IsInvertible := by
    apply (FlatFullSourcePositive.analytic_regular_iff F u (PositivePolynomialSystem.extend z)).mpr
    have hr0 := hr
    rw [← he] at hr0
    exact hr0
  simpa only [PositivePolynomialSystem.extend_old] using
    eval_regular_root F u (PositivePolynomialSystem.extend z)
      ((FlatFullSourcePositive.roots_extend_iff (Int.castRingHom ℝ) F u z).mpr hz) hr' i.castSucc

end LeanCanny.Encoding.FlatFullSourcePositiveCoordinate
