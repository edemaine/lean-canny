/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFramedSlackRootProperties
public import LeanCanny.Geometry.BoundedRegularRadiusBounds

/-! # Actual slack integer leaves over one formal radius

The old prefix matrices are fixed integer matrices. Only radius and the
proved affine dyadic exponents vary. Characteristic polynomials, scalar
substitution and power expansion therefore give literal native leaf families.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedSlackRadiusModel
open Polynomial LeanCanny.Geometry IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedClearedMatrixBits (rank)
open IntegralMixedFramedSlackMatrixBits (commonAt)
open scoped Classical

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)

noncomputable def power (offset slope : ℕ) : ℤ[X] := Polynomial.C ((2 : ℤ) ^ offset) * Polynomial.X ^ slope

theorem power_eval (offset slope R : ℕ) :
    (power offset slope).eval ((2 : ℤ) ^ R) = (2 : ℤ) ^ (offset + slope * R) := by
  simp only [power, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← pow_mul, ← pow_add, Nat.mul_comm R slope]

private theorem constant_matrix_eval {ι : Type*} (M : Matrix ι ι ℤ) (t : ℤ) :
    (M.map (Polynomial.C : ℤ →+* ℤ[X])).map (Polynomial.evalRingHom t) = M := by
  ext i j
  exact Polynomial.eval_C

private theorem scalar_matrix_eval {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ℤ[X]) (t : ℤ) :
    (Matrix.scalar ι a).map (Polynomial.evalRingHom t) = Matrix.scalar ι (a.eval t) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

noncomputable def sphere (N : List Bool → ℕ) (key : List Bool) :
    Matrix (Fin (rank P D H key)) (Fin (rank P D H key)) ℤ[X] :=
  Matrix.scalar _ (Polynomial.C (commonAt P D H key ^ 2) * Polynomial.X ^ 2) -
    (IntegralMixedFramedClearedPowerSumBits.matrixSum P D H N (fun _ => 2) key).map Polynomial.C

noncomputable def regular (N charge : List Bool → ℕ) (key : List Bool) :
    Matrix (Fin (rank P D H key)) (Fin (rank P D H key)) ℤ[X] :=
  let n := N key
  let d := charge key
  let a := power (BoundedRegularSource.regularizationExponent n d d 0) (BoundedRegularRadius.regularizationSlope n d)
  let k := power (BoundedZeroSource.penaltyExponent n d 0) (BoundedZeroSource.powerDegree d)
  let q := Polynomial.C (commonAt P D H key ^ BoundedZeroSource.powerDegree d)
  Matrix.scalar _ (a * q * k + q) -
    a • (IntegralMixedFramedClearedPowerSumBits.matrixSum P D H N
      (fun key => BoundedZeroSource.powerDegree (charge key)) key).map Polynomial.C -
    a • sphere P D H N key ^ (BoundedZeroSource.powerDegree d / 2)

theorem sphere_map_eval (N R : List Bool → ℕ) (key : List Bool) :
    (sphere P D H N key).map (Polynomial.evalRingHom ((2 : ℤ) ^ R key)) =
      IntegralMixedFramedSlackMatrixBits.sphere P D H N R key := by
  change (Polynomial.evalRingHom ((2 : ℤ) ^ R key)).mapMatrix _ = _
  rw [sphere, map_sub]
  simp only [RingHom.mapMatrix_apply]
  rw [scalar_matrix_eval, constant_matrix_eval]
  ext i j
  simp only [IntegralMixedFramedSlackMatrixBits.sphere, Matrix.sub_apply,
    IntegralMixedFramedSlackMatrixBits.sphereCoefficient, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Matrix.scalar_apply,
    Matrix.diagonal_apply, Matrix.intCast_apply]
  split_ifs <;> rfl

theorem regular_map_eval (N charge R : List Bool → ℕ) (key : List Bool) :
    (regular P D H N charge key).map (Polynomial.evalRingHom ((2 : ℤ) ^ R key)) =
      IntegralMixedFramedSlackMatrixBits.regular P D H N
        (fun key => BoundedZeroSource.powerDegree (charge key)) R
        (fun key => BoundedRegularSource.regularizationExponent (N key) (charge key) (charge key) (R key))
        (fun key => BoundedZeroSource.penaltyExponent (N key) (charge key) (R key)) key := by
  let φ := Polynomial.evalRingHom ((2 : ℤ) ^ R key)
  change φ.mapMatrix _ = _
  rw [regular, map_sub, map_sub]
  simp only [RingHom.mapMatrix_apply]
  rw [scalar_matrix_eval]
  simp only [Matrix.map_smul' φ _ _ (map_mul φ), Matrix.map_pow]
  dsimp only [φ]
  rw [constant_matrix_eval, sphere_map_eval P D H N R key]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    power_eval, ← BoundedRegularRadius.regularization_affine, ← BoundedRegularRadius.penalty_affine]
  ext i j
  simp only [IntegralMixedFramedSlackMatrixBits.regular, Matrix.sub_apply,
    IntegralMixedFramedSlackMatrixBits.regularCoefficient, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.intCast_apply,
    zsmul_eq_mul, Int.cast_id]

private theorem scaled_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ[X]) (c : ℤ[X]) (t : ℤ) :
    (ScaledGradedReductionAnnihilator.polynomial M c 1).map (Polynomial.evalRingHom t) =
      ScaledGradedReductionAnnihilator.polynomial (M.map (Polynomial.evalRingHom t)) (c.eval t) 1 := by
  simp only [ScaledGradedReductionAnnihilator.polynomial, pow_one, Polynomial.map_comp, Matrix.charpoly_map,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
  rfl

noncomputable def spherePolynomial (N : List Bool → ℕ) (key : List Bool) : (ℤ[X])[X] :=
  Polynomial.expand ℤ[X] 2 (ScaledGradedReductionAnnihilator.polynomial (sphere P D H N key)
    (Polynomial.C (commonAt P D H key ^ 2)) 1)

noncomputable def regularPolynomial (N charge : List Bool → ℕ) (key : List Bool) : (ℤ[X])[X] :=
  Polynomial.expand ℤ[X] (BoundedZeroSource.powerDegree (charge key))
    (ScaledGradedReductionAnnihilator.polynomial (regular P D H N charge key)
      (power (BoundedRegularSource.regularizationExponent (N key) (charge key) (charge key) 0)
        (BoundedRegularRadius.regularizationSlope (N key) (charge key)) *
        Polynomial.C (commonAt P D H key ^ BoundedZeroSource.powerDegree (charge key))) 1)

theorem spherePolynomial_map_eval
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (N R : List Bool → ℕ) (key : List Bool) :
    (spherePolynomial P D H N key).map (Polynomial.evalRingHom ((2 : ℤ) ^ R key)) =
      (IntegralMixedFramedSlackRootBits.sphereSource P D H s hs N R).polynomial key := by
  rw [spherePolynomial, Polynomial.map_expand, scaled_map, sphere_map_eval,
    IntegralMixedFramedSlackRootBits.sphere_polynomial]
  simp only [Polynomial.eval_C]

theorem regularPolynomial_map_eval
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (N charge R : List Bool → ℕ) (key : List Bool) :
    (regularPolynomial P D H N charge key).map (Polynomial.evalRingHom ((2 : ℤ) ^ R key)) =
      (IntegralMixedFramedSlackRootBits.regularSource P D H s hs N
        (fun key => BoundedZeroSource.powerDegree (charge key)) R
        (fun key => BoundedRegularSource.regularizationExponent (N key) (charge key) (charge key) (R key))
        (fun key => BoundedZeroSource.penaltyExponent (N key) (charge key) (R key))).polynomial key := by
  rw [regularPolynomial, Polynomial.map_expand, scaled_map, regular_map_eval,
    IntegralMixedFramedSlackRootBits.regular_polynomial]
  simp only [Polynomial.eval_mul, power_eval, ← BoundedRegularRadius.regularization_affine,
    Polynomial.eval_C]

end LeanCanny.Algebra.IntegralMixedFramedSlackRadiusModel
