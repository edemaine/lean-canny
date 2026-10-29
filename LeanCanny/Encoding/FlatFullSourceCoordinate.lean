/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceTower
public import LeanCanny.Geometry.AffineCoordinateEliminant

/-! # Uniform coordinate eliminants for the entire flat sampling tower

A single elimination applies to all ancestral coordinates at once. Matrix
width, degree allowance, and coefficient-bit allowance have native controls
for input-dependent depth. Every regular root of the complete system
annihilates these nonzero integer coordinate polynomials. This does not yet
provide their native coefficient evaluator.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceCoordinate
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatFullSourceTower (Inputs system degree mass count)
open scoped Classical
attribute [local irreducible] FlatFullSourceTower.system FlatFullSourceTower.degree FlatFullSourceTower.mass

noncomputable def level (F : Inputs) (u : List Bool) : ℕ := count F u * (degree F u - 1) + 1
noncomputable def width (F : Inputs) (u : List Bool) : ℕ := (level F u).size
noncomputable def matrixCount (F : Inputs) (u : List Bool) : ℕ :=
  FixedWidthPolynomial.count (count F u + 1) (width F u)
noncomputable def coefficientBits (F : Inputs) (u : List Bool) : ℕ :=
  (matrixCount F u).size * matrixCount F u + matrixCount F u * (mass F u + 3) + 1

theorem level_binary {F : Inputs} (h : F.Access) : BinaryFn (level F) :=
  (((BinaryFn.ofUnary (FlatFullSourceTower.count_unary h)).mul
    ((FlatFullSourceTower.degree_binary h).sub (BinaryFn.const 1)))).add (BinaryFn.const 1)

theorem width_unary {F : Inputs} (h : F.Access) : UnaryFn (width F) :=
  (UnaryFn.length (level_binary h).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

theorem matrixCount_binary {F : Inputs} (h : F.Access) : BinaryFn (matrixCount F) := by
  apply BinaryFn.of_bits
  exact mem_FP_of_eq (FixedWidthPolynomial.countCode_mem_FP
    ((FlatFullSourceTower.count_unary h).add (UnaryFn.const 1)) (width_unary h))
    (fun u => FixedWidthPolynomial.countCode_code (fun u => count F u + 1) (width F) u)

theorem coefficientBits_binary {F : Inputs} (h : F.Access) : BinaryFn (coefficientBits F) := by
  have hc := matrixCount_binary h
  exact ((hc.size.mul hc).add (hc.mul ((FlatFullSourceTower.mass_binary h).add (BinaryFn.const 3)))).add
    (BinaryFn.const 1)

theorem level_eq (F : Inputs) (u : List Bool) :
    Macaulay.level (AffineCoordinateSystem.degrees (fun _ : Fin (count F u) => degree F u)) = level F u := by
  simp [Macaulay.level, AffineCoordinateSystem.degrees, Fin.sum_univ_succ, level]

noncomputable def polynomial (F : Inputs) (u : List Bool) (i : Fin (count F u)) : Polynomial ℤ :=
  AffineCoordinateEliminant.polynomial (system F u) (fun _ => degree F u) i (width F u)

theorem ne_zero (F : Inputs) (u : List Bool) (i : Fin (count F u)) : polynomial F u i ≠ 0 :=
  AffineCoordinateEliminant.ne_zero _ _ _ _

theorem polynomial_degree (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    (polynomial F u i).natDegree ≤ matrixCount F u := AffineCoordinateEliminant.degree_le _ _ _ _

theorem polynomial_coefficient_bits (F : Inputs) (u : List Bool) (i : Fin (count F u)) (j : ℕ) :
    ((polynomial F u i).coeff j).natAbs.size ≤ coefficientBits F u :=
  AffineCoordinateEliminant.coefficient_size_le _ _ _ _ _
    (fun row _ => (MvMass.coeff_le _ _).trans (FlatFullSourceTower.polynomial_mass F u row)) j

theorem eval_regular_root (F : Inputs) (u : List Bool) (z : Fin (count F u) → ℝ)
    (hz : ∀ i, (system F u i).eval₂ (Int.castRingHom ℝ) z = 0)
    (hr : (fderiv ℝ (fun y => fun i => (system F u i).eval₂ (Int.castRingHom ℝ) y) z).IsInvertible)
    (i : Fin (count F u)) : (polynomial F u i).eval₂ (Int.castRingHom ℝ) (z i) = 0 :=
  AffineCoordinateEliminant.eval_eq_zero _ _ _ (FlatFullSourceTower.polynomial_degree F u)
    (fun _ => FlatFullSourceTower.degree_pos F u) i (width F u)
    (by rw [level_eq]; exact Nat.lt_size_self _) z hz hr

end LeanCanny.Encoding.FlatFullSourceCoordinate
