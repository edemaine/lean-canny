/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRawHeight
public import LeanCanny.Algebra.IntegralCoordinatePoweredSpace
public import LeanCanny.Algebra.IntegralCoordinateEvaluation
public import LeanCanny.Algebra.PaddedIntegralEquationMass
/-! # Actual untruncated cut coefficients on the same joint-prefix tuple

All four cut tags use the literal relative factor before the recorded scalar
degree truncation. Each coefficient is the canonical old-basis polynomial,
with the actual fixed powers restored. Its integer coefficients are exactly
the factor's regular-representation column zero, not an annihilator.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCutCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical

def key (c : List Bool) := pairFst c
def coefficientIndex (c : List Bool) := Nat.fromBitsLE (pairSnd c)

noncomputable def source (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    IntegralCoordinateCoefficientBits.Family where
  arity c := (family P D H).birth (key c)
  width c := (family P D H).width (key c)
  carrier c := ((family P D H).state (key c)).sampler.scalarPrefix.carrier
  ring c := ((family P D H).state (key c)).sampler.scalarPrefix.ring
  basis c := ((family P D H).state (key c)).sampler.scalarPrefix.basis
  element c := (IntegralMixedRelativeCuts.factor ((family P D H).state (key c))
    ((family P D H).birth_bound (key c)) ((family P D H).rule (key c)) ((family P D H).kind (key c))).coeff (coefficientIndex c)

def horizon (P : Parameters) (c : List Bool) := P.cap (pairFst (key c))+1
noncomputable def polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :=
  (source P D H).poweredPolynomial (horizon P) c

theorem matrix (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :
    (source P D H).matrix c=IntegralMixedCutMatrix.coefficientMatrix ((family P D H).state (key c))
      ((family P D H).birth_bound (key c)) ((family P D H).rule (key c)) ((family P D H).kind (key c)) (coefficientIndex c) := rfl

theorem evaluation (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool)
    (z : Fin ((family P D H).birth (key c))→ℝ)
    (φ : ((family P D H).state (key c)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (((family P D H).state (key c)).sampler.scalarPrefix.basis.generator i)=
      z i^UniformIntegralPowerSchedule.weights (horizon P c) (2^(family P D H).width (key c)) ((family P D H).birth (key c)) i) :
    (polynomial P D H c).eval₂ (Int.castRingHom ℝ) z=
      φ ((IntegralMixedRelativeCuts.factor ((family P D H).state (key c))
        ((family P D H).birth_bound (key c)) ((family P D H).rule (key c)) ((family P D H).kind (key c))).coeff (coefficientIndex c)) := by
  have HS:=CoordinatePowerSubstitution.eval_substitute (Int.castRingHom ℝ)
    (UniformIntegralPowerSchedule.weights (horizon P c) (2^(source P D H).width c) ((source P D H).arity c))
    ((source P D H).polynomial c) z
  have HE:=(((family P D H).state (key c)).sampler.scalarPrefix.basis).representative_eval_algHom
    ((source P D H).element c) φ
  change ((source P D H).polynomial c).eval₂ (Int.castRingHom ℝ)
    (fun i=>φ (((family P D H).state (key c)).sampler.scalarPrefix.basis.generator i))=_ at HE
  exact HS.trans (by simpa only [hφ,source] using HE)

theorem mass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hF : ∀ root,1≤F root)
    (hf : ∀ c,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C c) (c : List Bool) :
    MvMass.mass (polynomial P D H c)≤count ((source P D H).arity c) ((source P D H).width c)*
      2^IntegralMixedFramedRawHeight.rootCeiling P L F C (pairFst (key c)) := by
  let := (source P D H).ring c
  apply (CoordinatePowerSubstitution.mass_le _ _).trans
  apply PaddedIntegralParameterExtension.representative_mass
  intro r
  exact IntegralMixedFramedRawHeight.coefficient_root_height P D H L F C hs hF hf (key c) (coefficientIndex c) r _

end LeanCanny.Algebra.IntegralMixedFramedCutCoefficientBits
