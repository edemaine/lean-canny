/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentFullBlockScaling
public import LeanCanny.Algebra.ParameterSpatialSpecialization

/-! # Spatial critical equations in full-source sample blocks

The original parameter is variable zero; the critical equations differentiate
only the free block. A fixed-width direction word supplies the candidate
direction. Degree and mass allowances are derived from the constructed
source, native parent controls, and direction width. Specialization gives exactly the
spatial critical system of the same block polynomial at the actual sample.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentFullBlockCriticalSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter MvPolynomial
open RationalParentFullBlock
open scoped Classical
attribute [local irreducible] RationalParentFullBlockPolynomial.polynomial
  RationalParentFullBlockPolynomial.mass width degreeBound
set_option backward.isDefEq.respectTransparency false

def direction (k w : List Bool → ℕ) (bits : List Bool → List Bool) (u : List Bool) (i : Fin (k u)) : ℕ :=
  FixedWidthQuery.entry k w bits u i.val

theorem direction_lt (k w : List Bool → ℕ) (bits : List Bool → List Bool) (u : List Bool) (i : Fin (k u)) :
    direction k w bits u i < 2 ^ w u := by
  simp only [direction, FixedWidthQuery.entry, i.isLt, ite_true, FixedWidthQuery.coordinate]
  exact (Nat.fromBitsLE_lt_pow_length _).trans_le
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))

noncomputable def polynomial (F : Inputs) (w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b i : Fin (F.dim u)) : MvPolynomial (Fin (F.dim u + 1)) ℤ :=
  ParameterSpatialSpecialization.equation (RationalParentFullBlockPolynomial.polynomial F u) b
    (fun j => (direction F.dim w bits u j : ℤ)) i

theorem source_degree (F : Inputs) (u : List Bool) :
    (RationalParentFullBlockPolynomial.polynomial F u).totalDegree ≤ degreeBound F u :=
  RationalParentFullBlockPolynomial.polynomial_degree F u

theorem polynomial_degree (F : Inputs) (w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b i : Fin (F.dim u)) :
    (polynomial F w bits u b i).totalDegree ≤ degreeBound F u := by
  have hp := source_degree F u
  have hd (j : Fin (F.dim u + 1)) :=
    ((PartialDerivativeDegree.degree_le (RationalParentFullBlockPolynomial.polynomial F u) j).trans
      (Nat.sub_le _ _)).trans hp
  unfold polynomial ParameterSpatialSpecialization.equation
  split_ifs
  · exact hp
  · apply (totalDegree_sub _ _).trans
    apply max_le (hd i.succ)
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, Nat.zero_add] using hd b.succ)

noncomputable def massExponent (F : Inputs) (w : List Bool → ℕ) (u : List Bool) : ℕ :=
  RationalParentFullBlockPolynomial.mass F u + (degreeBound F u + 1).size + w u + 1

theorem polynomial_mass (F : Inputs) (w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b i : Fin (F.dim u)) :
    MvMass.mass (polynomial F w bits u b i) ≤ 2 ^ massExponent F w u := by
  let B := RationalParentFullBlockPolynomial.mass F u
  let D := degreeBound F u
  let p := RationalParentFullBlockPolynomial.polynomial F u
  have hp : MvMass.mass p ≤ 2 ^ B := RationalParentFullBlockPolynomial.polynomial_mass F u
  have hd : p.totalDegree ≤ D := source_degree F u
  have hm (j : Fin (F.dim u + 1)) : MvMass.mass (pderiv j p) ≤ D * 2 ^ B :=
    (MvMass.pderiv_le p j).trans (Nat.mul_le_mul hd hp)
  have hD : D + 1 ≤ 2 ^ (D + 1).size := (Nat.lt_size_self (D + 1)).le
  have hv : direction F.dim w bits u i + 1 ≤ 2 ^ (w u + 1) := by
    have := direction_lt F.dim w bits u i
    have H : 2 ^ w u ≤ 2 ^ (w u + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hbound : MvMass.mass (polynomial F w bits u b i) ≤
      (direction F.dim w bits u i + 1) * (D + 1) * 2 ^ B := by
    unfold polynomial ParameterSpatialSpecialization.equation
    split_ifs
    · exact hp.trans (Nat.le_mul_of_pos_left _ (by positivity))
    · have H := (MvMass.sub_le (pderiv i.succ p) (C (direction F.dim w bits u i : ℤ) * pderiv b.succ p)).trans
        (Nat.add_le_add (hm i.succ) ((MvMass.mul_le _ _).trans
          (Nat.mul_le_mul_left _ (hm b.succ))))
      simp only [MvMass.C, Int.natAbs_natCast] at H
      nlinarith
  apply hbound.trans
  calc
    _ ≤ 2 ^ (w u + 1) * 2 ^ (D + 1).size * 2 ^ B :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hv hD)
    _ = _ := by
      change 2 ^ (w u + 1) * 2 ^ (D + 1).size * 2 ^ B = 2 ^ (B + (D + 1).size + w u + 1)
      rw [← pow_add, ← pow_add]
      congr 1
      omega

theorem massExponent_binary {F : Inputs} (h : F.Access)
    {w : List Bool → ℕ} (hw : UnaryFn w) : BinaryFn (massExponent F w) :=
  ((((RationalParentFullBlockPolynomial.mass_binary h).add
    (((degreeBound_binary h).add (BinaryFn.const 1)).size)).add (BinaryFn.ofUnary hw)).add (BinaryFn.const 1))

theorem specialize_polynomial (F : Inputs) (w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b i : Fin (F.dim u)) (t : ℝ) :
    ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ) t (polynomial F w bits u b i) =
      ProjectionCriticalFamily.spatialEquation
        (ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ) t
          (RationalParentFullBlockPolynomial.polynomial F u)) b
        (fun j => (direction F.dim w bits u j : ℝ)) i :=
  ParameterSpatialSpecialization.specialize_equation _ _ _ _ _ _

end LeanCanny.Encoding.RationalParentFullBlockCriticalSource
