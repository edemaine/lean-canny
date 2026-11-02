/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedSpace
public import LeanCanny.Algebra.SelectedMultivariatePolynomialDegree
/-! # Original-size degree boxes for actual packed coordinate coefficients

The degree is a test-circuit bound on weighted raw joint variables. It does
not change the immutable spatial source degree or scalar cap.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

private theorem weighted_representative_degree {A : Type*} [CommRing A] (m N S : ℕ)
    (basis : IntegralCoordinateBasis A m N) (z : A) :
    (SelectedPoweredPolynomialLift.representative basis (UniformIntegralPowerSchedule.weights S N m) z).totalDegree≤
      UniformIntegralPowerSchedule.birth S N (m-1)*(m*(N-1)) :=
  (CoordinatePowerSubstitution.degree_le _ _ _ (UniformIntegralPowerSchedule.weights_le S N m)).trans
    (Nat.mul_le_mul_left _ (basis.representative_degree z))

noncomputable def degreeBound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (e : List Bool→ℕ) (q : List Bool) :=
  e q+IntegralMixedFramedAllCoordinateSourceBits.degree P D H (parent q)

theorem degreeBound_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (hp : parent∈FP) (e : List Bool→ℕ) (he : BinaryFn e) :
    BinaryFn (degreeBound P D H parent e) :=
  he.add ((IntegralMixedFramedAllCoordinateSourceBits.degree_binary P a D H).comp hp)

theorem head_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (d e : List Bool→ℕ) (q : List Bool) (y : ℕ) :
    ((head P D H parent d e q).coeff y).totalDegree≤degreeBound P D H parent e q := by
  let key:=IntegralMixedVirtualTaskBits.saved P (parent q)
  let x:=(family P D H).state key
  let :=x.sampler.scalarPrefix.ring
  unfold head degreeBound
  apply SelectedMultivariatePolynomialLift.coefficient_degree
  intro z
  exact weighted_representative_degree _ _ _ _ z

noncomputable def guardedHead (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (d e : List Bool→ℕ) (q : List Bool) :=
  if IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q then head P D H parent d e q else 0

theorem guardedHead_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (d e : List Bool→ℕ) (q : List Bool) (y : ℕ) :
    ((guardedHead P D H parent d e q).coeff y).totalDegree≤degreeBound P D H parent e q := by
  unfold guardedHead
  split_ifs
  · exact head_degree P D H parent d e q y
  · simp

theorem arity_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (hp : parent∈FP) :
    UnaryFn (fun q=>IntegralMixedFramedCoordinateCoefficientSpaceBits.arity P D H parent q+1) :=
  ((IntegralMixedFramedAllCoordinateSourceBits.arity_unary P a D H).comp hp).add (UnaryFn.const 1)

end LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedBits
