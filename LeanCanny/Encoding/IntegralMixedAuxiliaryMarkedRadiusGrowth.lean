/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRadiusModel
public import LeanCanny.Algebra.IntegerPolynomialDyadicInterpolation

/-! # Actual marked prelude growth and formal parameter coefficient bounds -/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRadiusModel
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation Polynomial
open IntegralMixedAuxiliaryMarkedIntegerSource (number tag oldKey tail)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem sphere_mass_affine (R : List Bool → ℕ) (key : List Bool) :
    (IntegralMixedAuxiliaryParametricSlackSource.sphereSource hn ht ha R).mass key +
        R key * (IntegralMixedAuxiliaryParametricSlackSource.sphereSource hn ht ha (fun _ => 0)).mass key =
      (IntegralMixedAuxiliaryParametricSlackSource.sphereSource hn ht ha (fun _ => 0)).mass key +
        R key * (IntegralMixedAuxiliaryParametricSlackSource.sphereSource hn ht ha (fun _ => 1)).mass key := by
  dsimp only [IntegralMixedAuxiliaryParametricSlackSource.sphereSource,
    IntegralMixedFramedSlackRootBits.sphereSource, IntegerPolynomialExpandSource.source,
    IntegralMixedFramedSlackRootBits.rawSphereSource, IntegralMixedFramedSlackRootBits.sphereEntryHeight,
    ScaledCharacteristicIntegerBounds.massHeight, ScaledCharacteristicIntegerBounds.coefficientHeight,
    CharacteristicIntegerBounds.budget, IntegralMixedFramedSlackMatrixBounds.sphereHeight]
  ring

private theorem regular_mass_affine (R : List Bool → ℕ) (key : List Bool) :
    (IntegralMixedAuxiliaryParametricSlackSource.regularSource hn ht ha R).mass key +
        R key * (IntegralMixedAuxiliaryParametricSlackSource.regularSource hn ht ha (fun _ => 0)).mass key =
      (IntegralMixedAuxiliaryParametricSlackSource.regularSource hn ht ha (fun _ => 0)).mass key +
        R key * (IntegralMixedAuxiliaryParametricSlackSource.regularSource hn ht ha (fun _ => 1)).mass key := by
  dsimp only [IntegralMixedAuxiliaryParametricSlackSource.regularSource,
    IntegralMixedFramedSlackRootBits.regularSource, IntegerPolynomialExpandSource.source,
    IntegralMixedFramedSlackRootBits.rawRegularSource, IntegralMixedFramedSlackRootBits.regularEntryHeight,
    IntegralMixedFramedSlackRootBits.regularScalarHeight,
    IntegralMixedAuxiliaryParametricSlackSource.regularizationAt,
    IntegralMixedAuxiliaryParametricSlackSource.penaltyAt]
  rw [BoundedRegularRadius.regularization_affine _ _ _ (R key),
    BoundedRegularRadius.regularization_affine _ _ _ 1,
    BoundedRegularRadius.penalty_affine _ _ (R key), BoundedRegularRadius.penalty_affine _ _ 1]
  dsimp only [ScaledCharacteristicIntegerBounds.massHeight, ScaledCharacteristicIntegerBounds.coefficientHeight,
    CharacteristicIntegerBounds.budget, IntegralMixedFramedSlackMatrixBounds.regularHeight,
    IntegralMixedFramedSlackMatrixBounds.regularDiagonalHeight,
    IntegralMixedFramedSlackMatrixBounds.sphereHeight]
  ring

noncomputable def nativeMass (R : List Bool → ℕ) (q : List Bool) : ℕ :=
  (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).mass q

noncomputable def massZero (q : List Bool) : ℕ := nativeMass hn ht ha (fun _ => 0) q
noncomputable def massOne (q : List Bool) : ℕ := nativeMass hn ht ha (fun _ => 1) q

theorem nativeMass_affine (R : List Bool → ℕ) (q : List Bool) :
    nativeMass hn ht ha R q + R (pairFst q) * massZero hn ht ha q =
      massZero hn ht ha q + R (pairFst q) * massOne hn ht ha q := by
  have HS := sphere_mass_affine hn ht ha (R ∘ tail) (oldKey n t (pairFst q))
  have HR := regular_mass_affine hn ht ha (R ∘ tail) (oldKey n t (pairFst q))
  simp only [Function.comp_apply, IntegralMixedAuxiliaryMarkedIntegerSource.oldKey_tail] at HS HR
  simp only [nativeMass, massZero, massOne, IntegralMixedAuxiliaryMarkedIntegerSource.source,
    IntegerPolynomialSourceChoice.choose, IntegerPolynomialSourceChoice.reindex,
    PowerIntegerPolynomial.source, IntegerPolynomialZeroRootSource.source, Function.comp_apply]
  split_ifs
  · ring
  · exact HS
  · exact HR
  · ring
  · dsimp only [IntegralMixedAuxiliaryParametricSlackSource.regularizationAt, Function.comp_apply]
    rw [IntegralMixedAuxiliaryMarkedIntegerSource.oldKey_tail]
    rw [BoundedRegularRadius.regularization_affine _ _ _ (R (pairFst q)),
      BoundedRegularRadius.regularization_affine _ _ _ 1]
    ring
  · dsimp only [IntegralMixedAuxiliaryMarkedIntegerSource.beta, Function.comp_apply]
    rw [IntegralMixedAuxiliaryMarkedIntegerSource.oldKey_tail]
    rw [BoundedRegularRadius.perturbation_affine _ _ _ (R (pairFst q)),
      BoundedRegularRadius.perturbation_affine _ _ _ 1]
    ring
  · dsimp only [IntegralMixedAuxiliaryParametricSlackSource.penaltyAt, Function.comp_apply]
    rw [IntegralMixedAuxiliaryMarkedIntegerSource.oldKey_tail]
    rw [BoundedRegularRadius.penalty_affine _ _ (R (pairFst q)),
      BoundedRegularRadius.penalty_affine _ _ 1]
    ring
  · ring

theorem nativeMass_le (R : List Bool → ℕ) (q : List Bool) :
    nativeMass hn ht ha R q ≤ massOne hn ht ha q * R (pairFst q) + massZero hn ht ha q := by
  have H := nativeMass_affine hn ht ha R q
  nlinarith

theorem massZero_binary : BinaryFn (massZero hn ht ha) :=
  (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha (BinaryFn.const 0)).mass

theorem massOne_binary : BinaryFn (massOne hn ht ha) :=
  (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha (BinaryFn.const 1)).mass

noncomputable def parameterMassBudget (q : List Bool) : ℕ :=
  IntegerPolynomialDyadic.massBudget 0 (massOne hn ht ha q) (massZero hn ht ha q)

theorem parameterMassBudget_binary : BinaryFn (parameterMassBudget hn ht ha) :=
  IntegerPolynomialDyadic.massBudget_binary (BinaryFn.const 0)
    (massOne_binary hn ht ha) (massZero_binary hn ht ha)

theorem coefficient_growth (q : List Bool) (k R : ℕ) :
    (((polynomial hn ht ha q).coeff k).eval ((2 : ℤ) ^ R)).natAbs ≤
      2 ^ (massOne hn ht ha q * R + massZero hn ht ha q) := by
  have HC := coeff_natAbs_le_coefficientMass
    ((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha (fun _ => R)).polynomial q) k
  have HM := (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha (fun _ => R)).mass_bound q
  have HP := polynomial_map_eval hn ht ha (fun _ => R) q
  have HB := HC.trans HM
  rw [← HP, Polynomial.coeff_map] at HB
  exact HB.trans (Nat.pow_le_pow_right (by decide) (nativeMass_le hn ht ha (fun _ => R) q))

theorem coefficient_parameter_mass (q : List Bool) (k : ℕ) :
    coefficientMass ((polynomial hn ht ha q).coeff k) ≤ 2 ^ parameterMassBudget hn ht ha q :=
  IntegerPolynomialDyadic.coefficientMass_le _ 0 _ _
    (fun R _ => coefficient_growth hn ht ha q k R)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRadiusModel
