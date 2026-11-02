/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCutCoefficientPolynomial
public import LeanCanny.Algebra.IntegralMixedFramedBankSnapshot
public import LeanCanny.Algebra.IntegralMixedFramedRawHeightControls
/-! # One original-source degree, mass and width for full cut coefficient tests -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCutCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan family)

theorem arity_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    UnaryFn (source P D H).arity :=
  (IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp pairFst_mem_FP
theorem width_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    UnaryFn (source P D H).width := a.width.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
theorem horizon_unary (P : Parameters) (a : Access P) : UnaryFn (horizon P) :=
  ((a.cap.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).add (UnaryFn.const 1))

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

noncomputable def massBound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (c : List Bool) :=
  (source P D H).arity c*(source P D H).width c+
    IntegralMixedFramedRawHeight.rootCeiling P L F C (pairFst (key c))
theorem massBound_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : BinaryFn (massBound P D H L F C) :=
  ((BinaryFn.ofUnary (arity_unary P a D H)).mul (BinaryFn.ofUnary (width_unary P a D H))).add
    ((IntegralMixedFramedRawHeight.rootCeiling_binary P a hL hF hC).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))

theorem polynomial_mass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hF : ∀ root,1≤F root)
    (hf : ∀ c,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C c) (c : List Bool) :
    MvMass.mass (polynomial P D H c)≤2^massBound P D H L F C c := by
  apply (mass P D H L F C hs hF hf c).trans_eq
  unfold massBound count
  rw [←pow_mul,←pow_add]
  congr 1
  ring

noncomputable def denseWidth (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :=
  (degree P D H c).size
theorem denseWidth_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    UnaryFn (denseWidth P D H) :=
  (UnaryFn.length (degree_binary P a D H).bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)

end LeanCanny.Algebra.IntegralMixedFramedCutCoefficientBits
