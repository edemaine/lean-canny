/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullCutTerminalSelected
/-! # Original-only terminal full-factor readers and mass bounds -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullCutTerminalHead
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open FixedWidthBivariateReader (origin origin_FP)
open FixedWidthBivariateReboxBits (outer target)
open IntegralMixedFramedFullCutHead (headDegree headMass)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)

theorem coefficient_mass (parent terminal : List Bool→List Bool) (d L F C : List Bool→ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hF : ∀root,1≤F root)
    (hf : ∀old,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C old) (c : List Bool) (k : ℕ) :
    MvMass.mass ((polynomial P D H parent terminal d c).coeff k)≤2^headMass P D H parent L F C c :=by
  unfold polynomial
  split_ifs
  · rw [castHead,Polynomial.coeff_map]
    apply (MvMass.rename_le _ _).trans
    rw [FixedWidthBivariateSuffixBits.coefficient]
    exact (MvMass.rename_le _ _).trans (IntegralMixedFramedFullCutHead.head_coefficient_mass P D H parent d L F C hs hF hf c k)
  · simp

theorem word_evaluator (a : Access P) (L F C : List Bool→ℕ)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (parent terminal : List Bool→List Bool) (hp : parent∈FP) (ht : terminal∈FP) (d W : List Bool→ℕ) (hd : BinaryFn d) (hW : UnaryFn W) :
    SpaceFunction (FixedWidthBivariateReboxBits.coefficient (fun c=>count P D H terminal c+1) W (polynomial P D H parent terminal d)) :=by
  have E:=coefficient_evaluator P D H (parent∘origin) (terminal∘origin) (d∘origin) a L F C hL hF hC h hb
    (mem_FP_comp origin_FP hp) (mem_FP_comp origin_FP ht) (W∘origin) outer (hd.comp origin_FP) (hW.comp origin_FP)
    (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))
    target FixedWidthBivariateReboxBits.modulus (by polytime [target]) (by polytime [FixedWidthBivariateReboxBits.modulus])
  exact E.congr (funext fun _=>rfl)

noncomputable def reader (a : Access P) (L F C : List Bool→ℕ)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (parent terminal : List Bool→List Bool) (hp : parent∈FP) (ht : terminal∈FP) (d W : List Bool→ℕ) (hd : BinaryFn d) (hW : UnaryFn W)
    (hfit : ∀c,headDegree P D H parent c<2^W c) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>count P D H terminal c+1) W (polynomial P D H parent terminal d)) :=
  FixedWidthBivariateReader.reader (fun c=>count P D H terminal c+1) W (polynomial P D H parent terminal d)
    (FixedWidthBivariateReboxBits.coefficient (fun c=>count P D H terminal c+1) W (polynomial P D H parent terminal d))
    (word_evaluator P D H a L F C hL hF hC h hb parent terminal hp ht d W hd hW)
    ((count_unary P D H terminal a ht).add (UnaryFn.const 1)) hW (headDegree P D H parent) (coefficient_degree P D H parent terminal d) hfit
    (FixedWidthBivariateReboxBits.coefficient_packet (fun c=>count P D H terminal c+1) W (polynomial P D H parent terminal d))

end LeanCanny.Algebra.IntegralMixedFramedFullCutTerminalHead
