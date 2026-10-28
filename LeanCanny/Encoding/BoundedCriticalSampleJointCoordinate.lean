/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleJointGeometry

/-! # Bounded coordinate equations for regular child candidates

Each coordinate has a concrete nonzero integer annihilator. Its width,
degree allowance, and coefficient-bit allowance are computed natively from
the joint source bounds. No regularity of other parent fibers is assumed.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleJointCoordinate
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedCriticalSampleJointSource
open scoped Classical
attribute [local irreducible] BoundedCriticalSampleJointSource.degree
  BoundedCriticalSampleJointSource.massExponent BoundedCriticalSampleJointSource.system

noncomputable def level (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (u : List Bool) : ℕ :=
  (k u + 1) * (degree P read u - 1) + 1

noncomputable def width (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (u : List Bool) : ℕ :=
  (level P read k u).size

noncomputable def count (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (u : List Bool) : ℕ :=
  FixedWidthPolynomial.count (k u + 2) (width P read k u)

noncomputable def coefficientBits (P : Readers) (read : List Bool → List Bool) (k w : List Bool → ℕ)
    (u : List Bool) : ℕ :=
  (count P read k u).size * count P read k u +
    count P read k u * (massExponent P read k w u + 3) + 1

theorem level_binary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {k : List Bool → ℕ} (hk : UnaryFn k) : BinaryFn (level P read k) :=
  (((BinaryFn.ofUnary hk).add (BinaryFn.const 1)).mul
    ((degree_binary h read hr).sub (BinaryFn.const 1))).add (BinaryFn.const 1)

theorem width_unary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {k : List Bool → ℕ} (hk : UnaryFn k) : UnaryFn (width P read k) :=
  (UnaryFn.length (level_binary h read hr hk).bits_mem_FP).of_eq
    (fun u => BinaryNatCode.length_encode (level P read k u))

theorem count_binary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {k : List Bool → ℕ} (hk : UnaryFn k) : BinaryFn (count P read k) := by
  apply BinaryFn.of_bits
  exact mem_FP_of_eq (FixedWidthPolynomial.countCode_mem_FP (hk.add (UnaryFn.const 2)) (width_unary h read hr hk))
    (fun u => FixedWidthPolynomial.countCode_code (fun u => k u + 2) (width P read k) u)

theorem coefficientBits_binary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {k w : List Bool → ℕ} (hk : UnaryFn k) (hw : UnaryFn w) : BinaryFn (coefficientBits P read k w) := by
  have hc := count_binary h read hr hk
  exact ((hc.size.mul hc).add (hc.mul ((massExponent_binary h read hr hk hw).add (BinaryFn.const 3)))).add
    (BinaryFn.const 1)

theorem level_eq (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (u : List Bool) :
    Macaulay.level (AffineCoordinateSystem.degrees (fun _ : Fin (k u + 1) => degree P read u)) =
      level P read k u := by
  simp [Macaulay.level, AffineCoordinateSystem.degrees, Fin.sum_univ_succ, level]

theorem degree_lt_width (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (u : List Bool) :
    degree P read u < 2 ^ width P read k u := by
  have hd := degree_pos P read u
  have hm : degree P read u - 1 ≤ (k u + 1) * (degree P read u - 1) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (degree P read u - 1) (show 1 ≤ k u + 1 by omega)
  exact (show degree P read u ≤ level P read k u by unfold level; omega).trans_lt (Nat.lt_size_self _)

theorem width_pos (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (u : List Bool) :
    0 < width P read k u := by
  have hd := degree_pos P read u
  have hf := degree_lt_width P read k u
  by_contra hn
  have hz : width P read k u = 0 := by omega
  rw [hz, pow_zero] at hf
  omega

noncomputable def polynomial (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (k u)) (i : Fin (k u + 1)) : Polynomial ℤ :=
  AffineCoordinateEliminant.polynomial (system P read o k w bits u b) (fun _ => degree P read u) i (width P read k u)

theorem ne_zero (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (k u)) (i : Fin (k u + 1)) :
    polynomial P read o k w bits u b i ≠ 0 := AffineCoordinateEliminant.ne_zero _ _ _ _

theorem polynomial_degree (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (k u)) (i : Fin (k u + 1)) :
    (polynomial P read o k w bits u b i).natDegree ≤ count P read k u :=
  AffineCoordinateEliminant.degree_le _ _ _ _

theorem polynomial_coefficient_bits (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (k u)) (i : Fin (k u + 1)) (j : ℕ) :
    ((polynomial P read o k w bits u b i).coeff j).natAbs.size ≤ coefficientBits P read k w u :=
  AffineCoordinateEliminant.coefficient_size_le _ _ _ _ _
    (fun row _ => (MvMass.coeff_le _ _).trans (polynomial_mass P read o k w bits u b row)) j

theorem eval_regular_candidate (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b : Fin (k u))
    (z : BoundedCriticalSampleJointGeometry.RegularCandidates P read o k w bits u b) (i : Fin (k u + 1)) :
    (polynomial P read o k w bits u b i).eval₂ (Int.castRingHom ℝ) (z.val.val i) = 0 :=
  AffineCoordinateEliminant.eval_eq_zero (Int.castRingHom ℝ) _ _
    (BoundedCriticalSampleJointSource.polynomial_degree P read o k w bits u b) (fun _ => degree_pos P read u)
    i (width P read k u) (by rw [level_eq]; exact Nat.lt_size_self _) z.val.val z.val.property z.property

end LeanCanny.Encoding.BoundedCriticalSampleJointCoordinate
