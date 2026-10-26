/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSeparator
public import LeanCanny.Geometry.LinearProjectionEliminant

/-! # Concrete bounded polynomials for selected critical-sample projections

Every actual sample projects to a root of one nonzero integer polynomial.
Its degree has polynomial binary length computed from the original readers.
The coefficient allowance includes the actual source and both selected records.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalProjection
open LeanCanny.ETR LeanCanny.Geometry LeanCanny.Algebra MvPolynomial BoundedFullWriter
open scoped Classical BigOperators

noncomputable def sourceBits (P : Readers) (c : List Bool) : ℕ :=
  regularizationExponent P c +
    BoundedRegularSource.sourceMassExponent (P.dim c) (size P c) (size P c) (P.radius c) + 1

noncomputable def equationBits (P : Readers) (c : List Bool) : ℕ :=
  (degree P c).size + sourceBits P c + BoundedFullDirectionQueries.width P c + 1

noncomputable def systemWidth (P : Readers) (c : List Bool) : ℕ :=
  ((P.dim c + 4) * (degree P c - 1) + 1).size

noncomputable def labelWidth (P : Readers) (c : List Bool) : ℕ :=
  (P.dim c + 5) * systemWidth P c

noncomputable def weights (P : Readers) (c : List Bool) (i : Fin (P.dim c + 4)) : ℤ :=
  BoundedCriticalSeparator.weight P (BoundedCriticalSeparator.record P) c i.val

noncomputable def polynomial (P : Readers) (c : List Bool) : Polynomial ℤ :=
  LinearProjectionEliminant.polynomial (BoundedFullCriticalSamples.equations P c)
    (fun _ => degree P c) (weights P c) (systemWidth P c)

theorem source_mass (P : Readers) (c : List Bool) :
    MvMass.mass (BoundedFullCriticalSamples.polynomial P c) ≤ 2 ^ sourceBits P c := by
  apply (MvMass.rename_le _ _).trans
  exact IntegerRegularSource.mass_le _ 1 (degree P c)
    (BoundedRegularSource.sourceMassExponent (P.dim c) (size P c) (size P c) (P.radius c))
    (BoundedRegularSource.source_mass _ _ _ _ (original_mass P c))

theorem record_coordinate_lt (W : ℕ) (r : List Bool) (i : ℕ) :
    Nat.fromBitsLE ((r.drop (i * W)).take W) < 2 ^ W :=
  (Nat.fromBitsLE_lt_pow_length _).trans_le
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))

theorem direction_bound (P : Readers) (c : List Bool) (i : ℕ) :
    (BoundedFullCriticalSamples.direction P c i).natAbs ≤ 2 ^ BoundedFullDirectionQueries.width P c := by
  exact (record_coordinate_lt _ (BoundedFullDirectionChoice.record P c) i).le

theorem weight_bound (P : Readers) (c : List Bool) (i : Fin (P.dim c + 4)) :
    (weights P c i).natAbs ≤ 2 ^ BoundedCriticalSeparator.width P c := by
  exact (record_coordinate_lt _ (BoundedCriticalSeparator.record P c) i.val).le

theorem equations_mass (P : Readers) (c : List Bool) (j : Fin (P.dim c + 4)) :
    MvMass.mass (BoundedFullCriticalSamples.equations P c j) ≤ 2 ^ equationBits P c := by
  have hp (i : Fin (P.dim c + 4)) :
      MvMass.mass (pderiv i (BoundedFullCriticalSamples.polynomial P c)) ≤ 2 ^ ((degree P c).size + sourceBits P c) := by
    calc
      _ ≤ (BoundedFullCriticalSamples.polynomial P c).totalDegree *
          MvMass.mass (BoundedFullCriticalSamples.polynomial P c) := MvMass.pderiv_le _ _
      _ ≤ degree P c * 2 ^ sourceBits P c :=
        Nat.mul_le_mul (BoundedFullCriticalSamples.source_degree P c) (source_mass P c)
      _ ≤ 2 ^ (degree P c).size * 2 ^ sourceBits P c :=
        Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
      _ = _ := (pow_add _ _ _).symm
  have hle : sourceBits P c ≤ equationBits P c := by unfold equationBits; omega
  refine Fin.cases ((source_mass P c).trans (Nat.pow_le_pow_right (by decide) hle)) (fun j => ?_) j
  change MvMass.mass (pderiv j.succ (BoundedFullCriticalSamples.polynomial P c) -
    C (BoundedFullCriticalSamples.direction P c j.val) * pderiv 0 (BoundedFullCriticalSamples.polynomial P c)) ≤ _
  have hm := (MvMass.mul_le (C (BoundedFullCriticalSamples.direction P c j.val))
    (pderiv 0 (BoundedFullCriticalSamples.polynomial P c))).trans
      (Nat.mul_le_mul (by simpa only [MvMass.C] using direction_bound P c j.val) (hp 0))
  rw [← pow_add] at hm
  have hsmall := (hp j.succ).trans (Nat.pow_le_pow_right (by decide)
    (Nat.le_add_left ((degree P c).size + sourceBits P c) (BoundedFullDirectionQueries.width P c)))
  rw [Nat.add_comm (BoundedFullDirectionQueries.width P c)] at hm hsmall
  apply (MvMass.sub_le _ _).trans
  apply (Nat.add_le_add hsmall hm).trans
  simp only [equationBits, pow_succ]
  omega

theorem systemWidth_unary {P : Readers} (h : P.PolyTime) : UnaryFn (systemWidth P) := by
  have hB := ((BinaryFn.ofUnary (h.dim.add (UnaryFn.const 4))).mul
    ((degree_binary h).sub (BinaryFn.const 1))).add (BinaryFn.const 1)
  exact (UnaryFn.length hB.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

theorem labelWidth_unary {P : Readers} (h : P.PolyTime) : UnaryFn (labelWidth P) :=
  (h.dim.add (UnaryFn.const 5)).mul (systemWidth_unary h)

theorem sourceBits_binary {P : Readers} (h : P.PolyTime) : BinaryFn (sourceBits P) :=
  ((regularizationExponent_binary h).add
    (BoundedRegularControls.sourceMassExponent_binary h.dim (BinaryFn.ofUnary (size_unary h))
      (BinaryFn.ofUnary (size_unary h)) h.radius)).add (BinaryFn.const 1)

theorem equationBits_binary {P : Readers} (h : P.PolyTime) : BinaryFn (equationBits P) :=
  ((((degree_binary h).size).add (sourceBits_binary h)).add
    (BinaryFn.ofUnary (BoundedFullDirectionQueries.width_unary h))).add (BinaryFn.const 1)

noncomputable def projectionBits (P : Readers) (c : List Bool) : ℕ :=
  equationBits P c + BoundedCriticalSeparator.width P c + (P.dim c + 4) + 2

noncomputable def coefficientBits (P : Readers) (c : List Bool) : ℕ :=
  (2 ^ labelWidth P c).size * 2 ^ labelWidth P c +
    2 ^ labelWidth P c * (projectionBits P c + 1) + 1

theorem coefficientBits_binary {P : Readers} (h : P.PolyTime) : BinaryFn (coefficientBits P) := by
  have hN : BinaryFn (fun c => 2 ^ labelWidth P c) :=
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp (labelWidth_unary h)
  have hB := (((equationBits_binary h).add (BinaryFn.ofUnary (BoundedCriticalSeparator.width_unary h))).add
    (BinaryFn.ofUnary (h.dim.add (UnaryFn.const 4)))).add (BinaryFn.const 2)
  exact (((hN.size).mul hN).add (hN.mul (hB.add (BinaryFn.const 1)))).add (BinaryFn.const 1)

theorem polynomial_ne_zero (P : Readers) (c : List Bool) : polynomial P c ≠ 0 :=
  LinearProjectionEliminant.ne_zero _ _ _ _

theorem polynomial_degree (P : Readers) (c : List Bool) :
    (polynomial P c).natDegree ≤ 2 ^ labelWidth P c := by
  simpa only [FixedWidthPolynomial.count, ← pow_mul, polynomial, labelWidth, Nat.mul_comm,
    Nat.add_assoc, Nat.reduceAdd] using
    LinearProjectionEliminant.degree_le (BoundedFullCriticalSamples.equations P c)
      (fun _ => degree P c) (weights P c) (systemWidth P c)

theorem projection_mass_bound (P : Readers) (c : List Bool) :
    2 ^ equationBits P c + 1 + (P.dim c + 4) * 2 ^ BoundedCriticalSeparator.width P c ≤
      2 ^ projectionBits P c := by
  let a := equationBits P c + BoundedCriticalSeparator.width P c + (P.dim c + 4)
  have h₁ : 2 ^ equationBits P c ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by dsimp [a]; omega)
  have h₂ : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h₃ : (P.dim c + 4) * 2 ^ BoundedCriticalSeparator.width P c ≤ 2 ^ a := by
    calc
      _ ≤ 2 ^ (P.dim c + 4) * 2 ^ BoundedCriticalSeparator.width P c :=
        Nat.mul_le_mul_right _ (show P.dim c + 4 < 2 ^ (P.dim c + 4) from Nat.lt_two_pow_self).le
      _ = 2 ^ (P.dim c + 4 + BoundedCriticalSeparator.width P c) := (pow_add _ _ _).symm
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by dsimp [a]; omega)
  change _ ≤ 2 ^ (a + 2)
  rw [pow_add]
  norm_num
  omega

theorem polynomial_coefficient_bits (P : Readers) (c : List Bool) (k : ℕ) :
    ((polynomial P c).coeff k).natAbs.size ≤ coefficientBits P c := by
  have hB := projection_mass_bound P c
  have he := LinearProjectionEliminant.coefficient_size_le (BoundedFullCriticalSamples.equations P c)
    (fun _ => degree P c) (weights P c) (systemWidth P c) (projectionBits P c) (equationBits P c)
    (BoundedCriticalSeparator.width P c)
    (fun j e => (MvMass.coeff_le _ _).trans (equations_mass P c j)) (weight_bound P c) hB k
  simpa only [FixedWidthPolynomial.count, ← pow_mul, polynomial, coefficientBits, labelWidth,
    Nat.mul_comm, Nat.add_assoc, Nat.reduceAdd] using he

theorem polynomial_eval_sample (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    (polynomial P c).eval₂ (Int.castRingHom ℝ)
      (BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) c x.val) = 0 := by
  have hpos : 0 < degree P c := by
    have := BoundedRegularSource.powerDegree_gt_one (size P c)
    change 0 < BoundedZeroSource.powerDegree (size P c)
    omega
  have hlevel : Macaulay.level (AffineCoordinateSystem.degrees (fun _ : Fin (P.dim c + 4) => degree P c)) =
      (P.dim c + 4) * (degree P c - 1) + 1 := by
    simp [Macaulay.level, AffineCoordinateSystem.degrees, Fin.sum_univ_succ]
  have he := LinearProjectionEliminant.eval_eq_zero (Int.castRingHom ℝ)
    (BoundedFullCriticalSamples.equations P c) (fun _ => degree P c)
    (BoundedFullCriticalSamples.equations_degree P c) (fun _ => hpos) (weights P c) (systemWidth P c)
    (by rw [hlevel]; exact Nat.lt_size_self _) x.val x.property (BoundedFullCriticalSamples.regular P c x)
  simpa only [polynomial, BoundedCriticalSeparator.value, weights, Int.coe_castRingHom,
    Int.cast_natCast, mul_comm] using he

end LeanCanny.Encoding.BoundedCriticalProjection
