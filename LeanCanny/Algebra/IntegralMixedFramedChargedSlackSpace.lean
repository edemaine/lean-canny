/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedChargedSlackSource
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQSlackSpace
/-! # Native access for the actual charged slack integer sources

All coefficients are derived from the verified current-Q backend. Mass
controls use the actual family-height recurrence and original numeric readers.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedChargedSlackSource
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedSlackMatrixBounds
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem height_binary (P : Parameters) (a : Access P) {L F C : List Bool → ℕ}
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : BinaryFn (height P L F C) :=
  IntegralMixedFramedStepHeight.familyHeight_binary P a hL hF hC

private theorem birth_binary (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    BinaryFn (fun key => (IntegralMixedFramedClearedMatrixBits.family P D H).birth key) :=
  BinaryFn.ofUnary (IntegralMixedFramedClearedMatrixBits.birth_unary P a D H)

variable (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool → ℕ) (hInputs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
  (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D)
    (IntegralMixedFramedCurrentQSlackBits.liftedData P D H))
  (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D)
    (IntegralMixedFramedCurrentQSlackBits.liftedData P D H) c)

include a hL hF hC c hb

theorem rawSphereAccess {N R : List Bool → ℕ} (hN : UnaryFn N) (hR : BinaryFn R) :
    IntegerPolynomialRootQueriesBits.Access (rawSphereSource P D H L F C hInputs N R) where
  coefficient := IntegralMixedFramedCurrentQSlackBits.sphere_coefficient_space P a D H c hb hN hR
  degree := IntegralMixedFramedClearedMatrixBits.rank_binary P a D H
  mass := ScaledCharacteristicIntegerBounds.massHeight_binary (IntegralMixedFramedClearedMatrixBits.rank_binary P a D H)
    (sphereHeight_binary (birth_binary P a D H) (BinaryFn.ofUnary hN) (IntegralMixedFramedClearedMatrixBits.rank_binary P a D H)
      (height_binary P a hL hF hC) hR)
    ((BinaryFn.const 2).mul ((birth_binary P a D H).mul (height_binary P a hL hF hC)))

theorem rawRegularAccess {N d R Lam K : List Bool → ℕ} (hN : UnaryFn N) (hd : BinaryFn d)
    (hR : BinaryFn R) (hLam : BinaryFn Lam) (hK : BinaryFn K) :
    IntegerPolynomialRootQueriesBits.Access (rawRegularSource P D H L F C hInputs N d R Lam K) where
  coefficient := IntegralMixedFramedCurrentQSlackBits.regular_coefficient_space P a D H c hb hN hd hR hLam hK
  degree := IntegralMixedFramedClearedMatrixBits.rank_binary P a D H
  mass := ScaledCharacteristicIntegerBounds.massHeight_binary (IntegralMixedFramedClearedMatrixBits.rank_binary P a D H)
    (regularHeight_binary (birth_binary P a D H) (BinaryFn.ofUnary hN) (IntegralMixedFramedClearedMatrixBits.rank_binary P a D H)
      (height_binary P a hL hF hC) hd hR hLam hK)
    (hLam.add (hd.mul ((birth_binary P a D H).mul (height_binary P a hL hF hC))))

theorem sphereAccess {N R : List Bool → ℕ} (hN : UnaryFn N) (hR : BinaryFn R) :
    IntegerPolynomialRootQueriesBits.Access (sphereSource P D H L F C hInputs N R) :=
  IntegerPolynomialExpandSource.access (rawSphereSource P D H L F C hInputs N R)
    (rawSphereAccess P a D H L F C hInputs hL hF hC c hb hN hR)
    (BinaryFn.const 2) (fun _ => by decide)

theorem regularAccess {N d R Lam K : List Bool → ℕ} (hN : UnaryFn N) (hd : BinaryFn d)
    (hR : BinaryFn R) (hLam : BinaryFn Lam) (hK : BinaryFn K) (hpos : ∀ key, 0 < d key) :
    IntegerPolynomialRootQueriesBits.Access (regularSource P D H L F C hInputs N d R Lam K) :=
  IntegerPolynomialExpandSource.access (rawRegularSource P D H L F C hInputs N d R Lam K)
    (rawRegularAccess P a D H L F C hInputs hL hF hC c hb hN hd hR hLam hK) hd hpos

end LeanCanny.Algebra.IntegralMixedFramedChargedSlackSource
