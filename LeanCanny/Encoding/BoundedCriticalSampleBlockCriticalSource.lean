/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleBlockTerm
public import LeanCanny.Algebra.ParameterSpatialSpecialization

/-! # Spatial critical equations in actual-sample coordinate blocks

The original parameter is variable zero; the critical equations differentiate
only the free block. A fixed-width direction word supplies the candidate
direction. Degree and mass allowances are derived from the term, original
sample controls, and direction width. Specialization gives exactly the
spatial critical system of the same block polynomial at the actual sample.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleBlockCriticalSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter MvPolynomial
open BoundedCriticalSampleBlockEncoding
open scoped Classical
attribute [local irreducible] BoundedCriticalSampleBlockTerm.polynomial BoundedCriticalSampleBlockTerm.mass width budget span

def direction (k w : List Bool → ℕ) (bits : List Bool → List Bool) (u : List Bool) (i : Fin (k u)) : ℕ :=
  FixedWidthQuery.entry k w bits u i.val

theorem direction_lt (k w : List Bool → ℕ) (bits : List Bool → List Bool) (u : List Bool) (i : Fin (k u)) :
    direction k w bits u i < 2 ^ w u := by
  simp only [direction, FixedWidthQuery.entry, i.isLt, ite_true, FixedWidthQuery.coordinate]
  exact (Nat.fromBitsLE_lt_pow_length _).trans_le
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))

noncomputable def polynomial (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b i : Fin (k u)) : MvPolynomial (Fin (k u + 1)) ℤ :=
  ParameterSpatialSpecialization.equation (BoundedCriticalSampleBlockTerm.polynomial P read o k u) b
    (fun j => (direction k w bits u j : ℤ)) i

theorem source_degree (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (u : List Bool) :
    (BoundedCriticalSampleBlockTerm.polynomial P read o k u).totalDegree ≤ budget P read u := by
  apply (BoundedCriticalSampleBlockTerm.polynomial_degree P read o k u).trans
  unfold budget
  nlinarith

theorem polynomial_degree (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b i : Fin (k u)) :
    (polynomial P read o k w bits u b i).totalDegree ≤ budget P read u := by
  have hp := source_degree P read o k u
  have hd (j : Fin (k u + 1)) :=
    ((PartialDerivativeDegree.degree_le (BoundedCriticalSampleBlockTerm.polynomial P read o k u) j).trans
      (Nat.sub_le _ _)).trans hp
  unfold polynomial ParameterSpatialSpecialization.equation
  split_ifs
  · exact hp
  · apply (totalDegree_sub _ _).trans
    apply max_le (hd i.succ)
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, Nat.zero_add] using hd b.succ)

noncomputable def massExponent (P : Readers) (read : List Bool → List Bool) (k w : List Bool → ℕ) (u : List Bool) : ℕ :=
  span P read k u + BoundedCriticalSampleBlockTerm.mass P read u + (budget P read u + 1).size + w u + 1

theorem polynomial_mass (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b i : Fin (k u)) :
    MvMass.mass (polynomial P read o k w bits u b i) ≤ 2 ^ massExponent P read k w u := by
  let B := span P read k u + BoundedCriticalSampleBlockTerm.mass P read u
  let D := budget P read u
  let p := BoundedCriticalSampleBlockTerm.polynomial P read o k u
  have hp : MvMass.mass p ≤ 2 ^ B := BoundedCriticalSampleBlockTerm.polynomial_mass P read o k u
  have hd : p.totalDegree ≤ D := source_degree P read o k u
  have hm (j : Fin (k u + 1)) : MvMass.mass (pderiv j p) ≤ D * 2 ^ B :=
    (MvMass.pderiv_le p j).trans (Nat.mul_le_mul hd hp)
  have hD : D + 1 ≤ 2 ^ (D + 1).size := (Nat.lt_size_self (D + 1)).le
  have hv : direction k w bits u i + 1 ≤ 2 ^ (w u + 1) := by
    have := direction_lt k w bits u i
    have H : 2 ^ w u ≤ 2 ^ (w u + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hbound : MvMass.mass (polynomial P read o k w bits u b i) ≤
      (direction k w bits u i + 1) * (D + 1) * 2 ^ B := by
    unfold polynomial ParameterSpatialSpecialization.equation
    split_ifs
    · exact hp.trans (Nat.le_mul_of_pos_left _ (by positivity))
    · have H := (MvMass.sub_le (pderiv i.succ p) (C (direction k w bits u i : ℤ) * pderiv b.succ p)).trans
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

theorem massExponent_binary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {k w : List Bool → ℕ} (hk : UnaryFn k) (hw : UnaryFn w) : BinaryFn (massExponent P read k w) :=
  ((((BoundedCriticalSampleBlockTerm.polynomial_mass_binary h read hr hk).add
    (((budget_binary h read hr).add (BinaryFn.const 1)).size)).add (BinaryFn.ofUnary hw)).add (BinaryFn.const 1))

theorem specialize_polynomial (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (b i : Fin (k u)) (t : ℝ) :
    ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ) t (polynomial P read o k w bits u b i) =
      ProjectionCriticalFamily.spatialEquation
        (ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ) t
          (BoundedCriticalSampleBlockTerm.polynomial P read o k u)) b
        (fun j => (direction k w bits u j : ℝ)) i :=
  ParameterSpatialSpecialization.specialize_equation _ _ _ _ _ _

end LeanCanny.Encoding.BoundedCriticalSampleBlockCriticalSource
