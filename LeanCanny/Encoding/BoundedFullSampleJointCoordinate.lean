/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleJointGeometry

/-! # Bounded coordinate equations for regular child candidates

Each coordinate has a concrete nonzero integer annihilator. Its width,
degree allowance, and coefficient-bit allowance are computed natively from
the joint source bounds. No regularity of other parent fibers is assumed.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleJointCoordinate
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedFullSampleBlock BoundedFullSampleJointSource
open scoped Classical
attribute [local irreducible] BoundedFullSampleJointSource.degree
  BoundedFullSampleJointSource.massExponent BoundedFullSampleJointSource.system

noncomputable def level (F : Inputs) (u : List Bool) : ℕ :=
  (F.dim u + 1) * (degree F u - 1) + 1

noncomputable def width (F : Inputs) (u : List Bool) : ℕ :=
  (level F u).size

noncomputable def count (F : Inputs) (u : List Bool) : ℕ :=
  FixedWidthPolynomial.count (F.dim u + 2) (width F u)

noncomputable def coefficientBits (F : Inputs) (w : List Bool → ℕ)
    (u : List Bool) : ℕ :=
  (count F u).size * count F u +
    count F u * (massExponent F w u + 3) + 1

theorem level_binary {F : Inputs} (h : F.PolyTime) : BinaryFn (level F) :=
  (((BinaryFn.ofUnary h.dim).add (BinaryFn.const 1)).mul
    ((degree_binary h).sub (BinaryFn.const 1))).add (BinaryFn.const 1)

theorem width_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (width F) :=
  (UnaryFn.length (level_binary h).bits_mem_FP).of_eq
    (fun u => BinaryNatCode.length_encode (level F u))

theorem count_binary {F : Inputs} (h : F.PolyTime) : BinaryFn (count F) := by
  apply BinaryFn.of_bits
  exact mem_FP_of_eq (FixedWidthPolynomial.countCode_mem_FP (h.dim.add (UnaryFn.const 2)) (width_unary h))
    (fun u => FixedWidthPolynomial.countCode_code (fun u => F.dim u + 2) (width F) u)

theorem coefficientBits_binary {F : Inputs} (h : F.PolyTime)
    {w : List Bool → ℕ} (hw : UnaryFn w) : BinaryFn (coefficientBits F w) := by
  have hc := count_binary h
  exact ((hc.size.mul hc).add (hc.mul ((massExponent_binary h hw).add (BinaryFn.const 3)))).add
    (BinaryFn.const 1)

theorem level_eq (F : Inputs) (u : List Bool) :
    Macaulay.level (AffineCoordinateSystem.degrees (fun _ : Fin (F.dim u + 1) => degree F u)) =
      level F u := by
  simp [Macaulay.level, AffineCoordinateSystem.degrees, Fin.sum_univ_succ, level]

theorem degree_lt_width (F : Inputs) (u : List Bool) :
    degree F u < 2 ^ width F u := by
  have hd := degree_pos F u
  have hm : degree F u - 1 ≤ (F.dim u + 1) * (degree F u - 1) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (degree F u - 1) (show 1 ≤ F.dim u + 1 by omega)
  exact (show degree F u ≤ level F u by unfold level; omega).trans_lt (Nat.lt_size_self _)

theorem width_pos (F : Inputs) (u : List Bool) :
    0 < width F u := by
  have hd := degree_pos F u
  have hf := degree_lt_width F u
  by_contra hn
  have hz : width F u = 0 := by omega
  rw [hz, pow_zero] at hf
  omega

noncomputable def polynomial (F : Inputs) (w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (F.dim u)) (i : Fin (F.dim u + 1)) : Polynomial ℤ :=
  AffineCoordinateEliminant.polynomial (system F w bits u b) (fun _ => degree F u) i (width F u)

theorem ne_zero (F : Inputs) (w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (F.dim u)) (i : Fin (F.dim u + 1)) :
    polynomial F w bits u b i ≠ 0 := AffineCoordinateEliminant.ne_zero _ _ _ _

theorem polynomial_degree (F : Inputs) (w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (F.dim u)) (i : Fin (F.dim u + 1)) :
    (polynomial F w bits u b i).natDegree ≤ count F u :=
  AffineCoordinateEliminant.degree_le _ _ _ _

theorem polynomial_coefficient_bits (F : Inputs) (w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (F.dim u)) (i : Fin (F.dim u + 1)) (j : ℕ) :
    ((polynomial F w bits u b i).coeff j).natAbs.size ≤ coefficientBits F w u :=
  AffineCoordinateEliminant.coefficient_size_le _ _ _ _ _
    (fun row _ => (MvMass.coeff_le _ _).trans (polynomial_mass F w bits u b row)) j

theorem eval_regular_candidate (F : Inputs) (w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (F.dim u))
    (z : BoundedFullSampleJointGeometry.RegularCandidates F w bits u b) (i : Fin (F.dim u + 1)) :
    (polynomial F w bits u b i).eval₂ (Int.castRingHom ℝ) (z.val.val i) = 0 :=
  AffineCoordinateEliminant.eval_eq_zero (Int.castRingHom ℝ) _ _
    (BoundedFullSampleJointSource.polynomial_degree F w bits u b) (fun _ => degree_pos F u)
    i (width F u) (by rw [level_eq]; exact Nat.lt_size_self _) z.val.val z.val.property z.property

end LeanCanny.Encoding.BoundedFullSampleJointCoordinate
