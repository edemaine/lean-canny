/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedChoiceProbeSpace
public import LeanCanny.Algebra.IntegralMixedFramedCutCoefficientBounds
/-! # Native finite-choice coefficient polynomials use the same selected parent

The polynomial is evaluated on the same complete joint-prefix tuple. Its
bounds are inherited from the fixed original spatial source and actual
bank-height recurrence, with no absolute norm or new scalar-degree cap.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedChoiceProbeSourceBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

def horizon (P : Parameters) (c : List Bool) := P.cap (RankedHistoryTask.root c)+1
noncomputable def polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :=
  (source P D H).poweredPolynomial (horizon P) c

theorem horizon_unary (P : Parameters) (a : Access P) : UnaryFn (horizon P) :=
  (a.cap.comp RankedHistoryTask.root_FP).add (UnaryFn.const 1)

theorem evaluation (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
    (z : Fin ((family P D H).birth (IntegralMixedVirtualTaskBits.saved P c))→ℝ)
    (φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.basis.generator i)=
      z i^UniformIntegralPowerSchedule.weights (horizon P c) (2^(family P D H).width (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)) i) :
    (polynomial P D H c).eval₂ (Int.castRingHom ℝ) z=
      φ ((IntegralMixedRelativeCuts.factor ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).birth_bound _) ((family P D H).rule _) (IntegralMixedRelativeCuts.atChoice ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c))
          ((family P D H).kind _) (IntegralMixedRawKindChoiceBits.requested P c))).coeff (get P .coefficient c)) := by
  have HS:=CoordinatePowerSubstitution.eval_substitute (Int.castRingHom ℝ)
    (UniformIntegralPowerSchedule.weights (horizon P c) (2^(source P D H).width c) ((source P D H).arity c))
    ((source P D H).polynomial c) z
  have HE:=(((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.basis).representative_eval_algHom
    ((source P D H).element c) φ
  change ((source P D H).polynomial c).eval₂ (Int.castRingHom ℝ)
    (fun i=>φ (((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.basis.generator i))=_ at HE
  exact HS.trans (by simpa only [hφ,source,ite_eq_left ha] using HE)


noncomputable def degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :=
  UniformIntegralPowerSchedule.birth (horizon P c) (2^(source P D H).width c) ((source P D H).arity c-1)*
    ((source P D H).arity c*(2^(source P D H).width c-1))
theorem degree_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    BinaryFn (degree P D H) :=
  (UniformIntegralPowerSchedule.birth_binary (horizon_unary P a)
    ((BinaryFn.const 2).powUnary (width_unary P a D H)) ((arity_unary P a D H).sub (UnaryFn.const 1))).mul
      ((BinaryFn.ofUnary (arity_unary P a D H)).mul
        (((BinaryFn.const 2).powUnary (width_unary P a D H)).sub (BinaryFn.const 1)))

theorem polynomial_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :
    (polynomial P D H c).totalDegree≤degree P D H c := by
  let := (source P D H).ring c
  apply (CoordinatePowerSubstitution.degree_le _ _ _ (UniformIntegralPowerSchedule.weights_le _ _ _)).trans
  exact Nat.mul_le_mul_left _ (((source P D H).basis c).representative_degree ((source P D H).element c))

end LeanCanny.Algebra.IntegralMixedFramedChoiceProbeSourceBits
