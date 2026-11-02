/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedAllCoordinatePolynomialBounds
public import LeanCanny.Algebra.SelectedMultivariatePolynomialLift
/-! # One old coefficient context for the symbolic coordinate polynomial

The integer representative is indexed by the saved old key and independent
Y/E selectors. Changing numeric query fields retains this context literally.
No independently sampled old roots or spatial source change is introduced.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateRepresentativeBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

noncomputable def atContext (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (S : ℕ) (key : List Bool) (j y k : ℕ) : MvPolynomial (Fin ((family P D H).birth key)) ℤ := by
  let := ((family P D H).state key).sampler.scalarPrefix.ring
  exact SelectedPoweredPolynomialLift.representative ((family P D H).state key).sampler.scalarPrefix.basis
    (UniformIntegralPowerSchedule.weights S (2^(family P D H).width key) ((family P D H).birth key))
    (((IntegralMixedCriticalSweep.coordinate ((family P D H).state key) ((family P D H).birth_bound key)
      ((family P D H).rule key) (IntegralMixedCoordinateCoefficientSnapshot.coordinate (family P D H) key j)).coeff y).coeff k)

theorem source (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (ha : IntegralMixedFramedAllCoordinateSourceBits.Active P D H q) :
    HEq (IntegralMixedFramedAllCoordinateSourceBits.polynomial P D H q)
      (atContext P D H (IntegralMixedFramedAllCoordinateSourceBits.horizon P q) (IntegralMixedVirtualTaskBits.saved P q)
        (get P .slot13 q) (get P .slot8 q) (get P .coefficient q)) := by
  have HC : get P .slot8 q<IntegralMixedCoordinateTrailing.ChoiceBound
      ((family P D H).spatial (IntegralMixedVirtualTaskBits.saved P q))
      ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P q)) := ha.2.2.1
  unfold IntegralMixedFramedAllCoordinateSourceBits.polynomial IntegralCoordinateCoefficientBits.Family.poweredPolynomial
    IntegralCoordinateCoefficientBits.Family.polynomial atContext SelectedPoweredPolynomialLift.representative
  simp only [IntegralMixedFramedAllCoordinateSourceBits.source,ite_eq_left ha]
  unfold IntegralMixedCoordinateCoefficientSnapshot.kind IntegralMixedRelativeCuts.factor IntegralMixedCoordinateTrailing.factor
  simp only [IntegralMixedCoordinateCoefficientSnapshot.choice,Nat.mod_eq_of_lt HC]
  rfl

theorem atContext_congr (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (S T : ℕ) (key key' : List Bool) (j j' y y' k k' : ℕ)
    (hS : S=T) (hkey : key=key') (hj : j=j') (hy : y=y') (hk : k=k') :
    HEq (atContext P D H S key j y k) (atContext P D H T key' j' y' k') := by
  cases hS
  cases hkey
  cases hj
  cases hy
  cases hk
  rfl

end LeanCanny.Algebra.IntegralMixedFramedCoordinateRepresentativeBits
