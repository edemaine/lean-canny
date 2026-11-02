/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCutProbePolynomial
/-! # Original-source mass and dense width for native full coefficient tests -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCutProbeSourceBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

noncomputable def massBound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (c : List Bool) :=
  (source P D H).arity c*(source P D H).width c+
    IntegralMixedFramedRawHeight.rootCeiling P L F C (RankedHistoryTask.root c)
theorem massBound_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) :
    BinaryFn (massBound P D H L F C) :=
  ((BinaryFn.ofUnary (arity_unary P a D H)).mul (BinaryFn.ofUnary (width_unary P a D H))).add
    ((IntegralMixedFramedRawHeight.rootCeiling_binary P a hL hF hC).comp RankedHistoryTask.root_FP)

theorem polynomial_mass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hF : ∀ root,1≤F root)
    (hf : ∀ c,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C c) (c : List Bool) :
    MvMass.mass (polynomial P D H c)≤2^massBound P D H L F C c := by
  let := (source P D H).ring c
  have HR : MvMass.mass ((source P D H).polynomial c)≤count ((source P D H).arity c) ((source P D H).width c)*
      2^IntegralMixedFramedRawHeight.rootCeiling P L F C (RankedHistoryTask.root c) := by
    apply PaddedIntegralParameterExtension.representative_mass
    intro r
    change (((source P D H).matrix c) r (IntegralCoordinateBasis.zeroFin _ _)).natAbs≤_
    by_cases ha : IntegralMixedFramedFullCutProbeBits.Active P c
    · rw [matrix_active P D H c ha]
      have HX:=IntegralMixedFramedRawHeight.coefficient_root_height P D H L F C hs hF hf
        (IntegralMixedVirtualTaskBits.saved P c) (get P .coefficient c) r (IntegralCoordinateBasis.zeroFin _ _)
      rw [IntegralMixedFullHistoryFamilyBits.saved_root] at HX
      exact HX
    · rw [matrix_inactive P D H c ha]
      simp only [Matrix.zero_apply,Int.natAbs_zero]
      exact Nat.zero_le _
  apply (CoordinatePowerSubstitution.mass_le _ _).trans (HR.trans_eq ?_)
  unfold massBound count
  rw [←pow_mul,←pow_add]
  congr 1
  ring

noncomputable def denseWidth (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :=
  (degree P D H c).size
theorem denseWidth_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    UnaryFn (denseWidth P D H) :=
  (UnaryFn.length (degree_binary P a D H).bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)

end LeanCanny.Algebra.IntegralMixedFramedCutProbeSourceBits
