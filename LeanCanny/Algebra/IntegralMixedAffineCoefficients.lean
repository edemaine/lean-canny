/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHistory
/-! # Affine height expressions are finite linear combinations of cleared references -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedAffineCoefficients
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralMixedHistory
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def constantCoefficient : AffineExpr → ℤ
  | .constant c => c
  | .reference _ => 0
  | .add a b => constantCoefficient a + constantCoefficient b
  | .scale c e => c * constantCoefficient e

def referenceCoefficient : AffineExpr → ℕ → ℤ
  | .constant _, _ => 0
  | .reference i, j => if i = j then 1 else 0
  | .add a b, j => referenceCoefficient a j + referenceCoefficient b j
  | .scale c e, j => c * referenceCoefficient e j

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem reference_sum (x : State P S B m ι) (j : ℕ) :
    (∑ i : Fin m, (if j = i.val then (1 : ℤ) else 0) • cleared x i) =
      if hj : j < m then cleared x ⟨j, hj⟩ else 0 := by
  let _ := x.sampler.scalarPrefix.ring
  by_cases hj : j < m
  · rw [dite_eq_left hj, Finset.sum_eq_single (⟨j, hj⟩ : Fin m)]
    · rw [ite_eq_left rfl, one_smul]
    · intro b _ hb
      have hn : j ≠ b.val := by
        intro he
        exact hb (Fin.ext he.symm)
      rw [ite_eq_right hn, zero_smul]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  · rw [dite_eq_right hj]
    apply Finset.sum_eq_zero
    intro i _
    have hn : j ≠ i.val := by intro he; exact hj (he ▸ i.isLt)
    rw [ite_eq_right hn, zero_smul]

theorem expression_linear (x : State P S B m ι) (e : AffineExpr) :
    expression x e = ((commonDenominator x * constantCoefficient e : ℤ) : x.sampler.scalarPrefix.carrier) +
      ∑ i : Fin m, referenceCoefficient e i.val • cleared x i := by
  let _ := x.sampler.scalarPrefix.ring
  induction e with
  | constant c =>
    simp only [expression, constantCoefficient, referenceCoefficient, zero_smul, Finset.sum_const_zero, add_zero, Int.cast_mul]
  | reference j =>
    simp only [expression, constantCoefficient, referenceCoefficient, mul_zero, Int.cast_zero, zero_add]
    exact (reference_sum x j).symm
  | add a b ha hb =>
    simp only [expression, constantCoefficient, referenceCoefficient, ha, hb, add_smul,
      Finset.sum_add_distrib, mul_add, Int.cast_add]
    abel
  | scale c e he =>
    simp only [expression, constantCoefficient, referenceCoefficient, he]
    rw [← zsmul_eq_mul, smul_add, Finset.smul_sum]
    congr 1
    · simp only [zsmul_eq_mul, Int.cast_mul]
      ring
    · simp only [mul_smul]

end LeanCanny.Algebra.IntegralMixedAffineCoefficients
