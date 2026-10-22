/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRegularSource
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # The native tube regular Jacobian and its arithmetic budgets

The square Jacobian differentiates only the reciprocal and point coordinates.
Directions and the three perturbation parameters stay as integer polynomial
variables. Its determinant is an actual polynomial singularity equation;
its degree and entire coefficient mass have uniform source-size bounds.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRegularJacobianBudget
open LeanCanny.Encoding LeanCanny.Algebra Geometry
open MvPolynomial
open scoped BigOperators Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

private theorem det_mass_le {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ ℤ)) (H : ℕ)
    (hH : ∀ i j, MvMass.mass (A i j) ≤ H) :
    MvMass.mass A.det ≤ (Fintype.card ι).factorial * H ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ π : Equiv.Perm ι, MvMass.mass (Equiv.Perm.sign π • ∏ j, A (π j) j) := MvMass.sum_le _ _
    _ ≤ ∑ _π : Equiv.Perm ι, ∏ _j : ι, H := by
      apply Finset.sum_le_sum
      intro π _
      rw [Units.smul_def, MvPolynomial.smul_eq_C_mul]
      calc
        _ ≤ MvMass.mass (C (Equiv.Perm.sign π : ℤ)) * MvMass.mass (∏ j, A (π j) j) := MvMass.mul_le _ _
        _ = MvMass.mass (∏ j, A (π j) j) := by rw [MvMass.C, Int.units_natAbs, one_mul]
        _ ≤ ∏ j, MvMass.mass (A (π j) j) := MvMass.prod_le _ _
        _ ≤ ∏ _j : ι, H := Finset.prod_le_prod fun j _ => hH (π j) j
    _ = _ := by simp [Fintype.card_perm]

private theorem det_degree_le {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ ℤ)) (D : ℕ)
    (hD : ∀ i j, (A i j).totalDegree ≤ D) :
    A.det.totalDegree ≤ Fintype.card ι * D := by
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro π _
  apply (MvPolynomial.totalDegree_smul_le _ _).trans
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _j : ι, D := Finset.sum_le_sum fun j _ => hD (π j) j
    _ = _ := by simp

/-- Column coordinate corresponding to a regular-system row. -/
noncomputable def coordinate (bits : List Bool) : TubeRegularSource.Index bits → TubeRegularSource.Variable bits
  | none => none
  | some j => some (.inl (.inl ((Equiv.optionSubtypeNe
      (TubePolynomial.base (Fin (CompactSource.term bits).arity))) j)))

/-- The reciprocal/point Jacobian; parameters and directions are held fixed. -/
noncomputable def matrix (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) :
    Matrix (TubeRegularSource.Index bits) (TubeRegularSource.Index bits)
      (MvPolynomial (TubeRegularSource.Variable bits) ℤ) :=
  fun i j => pderiv (coordinate bits j) (TubeRegularSource.polynomial bits s i)

noncomputable def polynomial (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) :
    MvPolynomial (TubeRegularSource.Variable bits) ℤ := (matrix bits s).det

/-- A polynomial bound on the order of the spatial regular Jacobian. -/
def orderBudget (bits : List Bool) : ℕ := 3 * CompactSource.size bits + 3

def degreeBudget (bits : List Bool) : ℕ := orderBudget bits * (TubeIndexed.degreeBound bits - 1)

def massBudget (bits : List Bool) : ℕ :=
  orderBudget bits * orderBudget bits +
    orderBudget bits * (TubeRegularSource.coefficientBudget bits + TubeIndexed.degreeBound bits)

theorem orderBudget_unary : UnaryFn orderBudget :=
  ((UnaryFn.const 3).mul CompactSource.size_unary).add (UnaryFn.const 3)

theorem degreeBudget_unary : UnaryFn degreeBudget :=
  orderBudget_unary.mul (TubeIndexed.degreeBound_unary.sub (UnaryFn.const 1))

theorem massBudget_unary : UnaryFn massBudget :=
  (orderBudget_unary.mul orderBudget_unary).add
    (orderBudget_unary.mul (TubeRegularSource.coefficientBudget_unary.add TubeIndexed.degreeBound_unary))

theorem order_le (bits : List Bool) : Fintype.card (TubeRegularSource.Index bits) ≤ orderBudget bits := by
  have h := TubeSource.count_le_code bits
  simp only [TubeSource.countCode, BinaryNatCode.encode, Nat.fromBitsLE_bits] at h
  rw [Fintype.card_option]
  unfold orderBudget
  omega

/-- Whole coefficient mass, stronger than the existing per-coefficient budget. -/
theorem regular_mass_le (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (i : TubeRegularSource.Index bits) :
    MvMass.mass (TubeRegularSource.polynomial bits s i) ≤
      2 ^ TubeRegularSource.coefficientBudget bits := by
  let B := TubeSource.massBudget (CompactSource.size bits)
  let D := TubeIndexed.degreeBound bits
  have hp (j : TubeSource.ProjectionIndex bits) :
      MvMass.mass (TubeSource.integerProjection bits s j) ≤ 2 ^ B :=
    TubeSource.integer_projection_mass_le bits s j
  have hpow : 2 ^ B ≤ 2 ^ TubeRegularSource.coefficientBudget bits :=
    Nat.pow_le_pow_right (by decide) (by unfold TubeRegularSource.coefficientBudget; dsimp [B]; omega)
  cases i with
  | some j => exact (MvMass.rename_le _ _).trans ((hp j).trans hpow)
  | none =>
    have hd := TubeHomogenization.source_degree bits s none
    have hder := (MvMass.pderiv_le (TubeSource.integerProjection bits s none)
      (TubeRegularSource.base (CompactSource.term bits).arity)).trans
        (Nat.mul_le_mul hd (hp none))
    change MvMass.mass _ ≤ D * 2 ^ B at hder
    have hr := MvMass.rename_le (some : TubeSource.IntegerProjectionVariable bits → TubeRegularSource.Variable bits)
      (pderiv (TubeRegularSource.base (CompactSource.term bits).arity) (TubeSource.integerProjection bits s none))
    have hm := MvMass.mul_le (X none : MvPolynomial (TubeRegularSource.Variable bits) ℤ)
      (rename some (pderiv (TubeRegularSource.base (CompactSource.term bits).arity)
        (TubeSource.integerProjection bits s none)))
    have hs := MvMass.sub_le (X none * rename some
      (pderiv (TubeRegularSource.base (CompactSource.term bits).arity) (TubeSource.integerProjection bits s none)))
      (1 : MvPolynomial (TubeRegularSource.Variable bits) ℤ)
    simp only [MvMass.X, one_mul, MvMass.one] at hm hs
    have hprod : D * 2 ^ B ≤ 2 ^ (B + D) := by
      calc
        _ ≤ 2 ^ D * 2 ^ B := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
        _ = _ := by rw [← pow_add, Nat.add_comm]
    have hpos : 1 ≤ 2 ^ (B + D) := Nat.one_le_two_pow
    change MvMass.mass (X none * rename some (pderiv _ _) - 1) ≤ _
    change MvMass.mass _ ≤ 2 ^ (B + D + 1)
    calc
      _ ≤ D * 2 ^ B + 1 := hs.trans (Nat.add_le_add_right (hm.trans (hr.trans hder)) 1)
      _ ≤ 2 ^ (B + D) + 1 := Nat.add_le_add_right hprod 1
      _ ≤ _ := by rw [pow_succ]; omega

theorem entry_degree_le (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (i j : TubeRegularSource.Index bits) :
    (matrix bits s i j).totalDegree ≤ TubeIndexed.degreeBound bits - 1 :=
  (PartialDerivativeDegree.degree_le _ _).trans
    (Nat.sub_le_sub_right (TubeRegularSource.degree_le bits s i) 1)

theorem entry_mass_le (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (i j : TubeRegularSource.Index bits) :
    MvMass.mass (matrix bits s i j) ≤
      2 ^ (TubeRegularSource.coefficientBudget bits + TubeIndexed.degreeBound bits) := by
  apply (MvMass.pderiv_le _ _).trans
  apply (Nat.mul_le_mul (TubeRegularSource.degree_le bits s i) (regular_mass_le bits s i)).trans
  calc
    _ ≤ 2 ^ TubeIndexed.degreeBound bits * 2 ^ TubeRegularSource.coefficientBudget bits :=
      Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    _ = _ := by rw [← pow_add, Nat.add_comm]

theorem degree_le (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) :
    (polynomial bits s).totalDegree ≤ degreeBudget bits :=
  (det_degree_le _ _ (entry_degree_le bits s)).trans (Nat.mul_le_mul_right _ (order_le bits))

theorem mass_le (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) :
    MvMass.mass (polynomial bits s) ≤ 2 ^ massBudget bits := by
  let N := Fintype.card (TubeRegularSource.Index bits)
  let b := TubeRegularSource.coefficientBudget bits + TubeIndexed.degreeBound bits
  have hf : N.factorial ≤ 2 ^ (N * N) :=
    (Nat.factorial_le_pow N).trans ((Nat.pow_le_pow_left Nat.lt_two_pow_self.le N).trans_eq (pow_mul 2 N N).symm)
  have h := det_mass_le (matrix bits s) (2 ^ b) (entry_mass_le bits s)
  have hN : N ≤ orderBudget bits := order_le bits
  have he : N * N + N * b ≤ massBudget bits :=
    Nat.add_le_add (Nat.mul_le_mul hN hN) (Nat.mul_le_mul_right b hN)
  calc
    _ ≤ N.factorial * (2 ^ b) ^ N := h
    _ ≤ 2 ^ (N * N) * (2 ^ b) ^ N := Nat.mul_le_mul_right _ hf
    _ = 2 ^ (N * N + N * b) := by rw [← pow_mul, ← pow_add, Nat.mul_comm b]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

theorem coefficient_le (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (e : TubeRegularSource.Variable bits →₀ ℕ) :
    ((polynomial bits s).coeff e).natAbs ≤ 2 ^ massBudget bits :=
  (MvMass.coeff_le _ _).trans (mass_le bits s)

/-- Evaluating the singularity equation evaluates the actual square Jacobian determinant. -/
theorem eval_polynomial {K : Type*} [CommRing K] (bits : List Bool)
    (s : Finset (PerturbedSource.Index bits)) (φ : ℤ →+* K)
    (x : TubeRegularSource.Variable bits → K) :
    (polynomial bits s).eval₂ φ x =
      Matrix.det (fun i j => (pderiv (coordinate bits j) (TubeRegularSource.polynomial bits s i)).eval₂ φ x) := by
  exact RingHom.map_det (MvPolynomial.eval₂Hom φ x) (matrix bits s)

end LeanCanny.ETR.TubeRegularJacobianBudget
