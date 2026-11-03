/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullCutHeadBounds
public import LeanCanny.Algebra.FixedWidthBivariateReboxSpace
/-! # Original-only certified bivariate readers for full relative cut heads -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullCutHead
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open FixedWidthBivariateReader (origin origin_FP)
open FixedWidthBivariateReboxBits (outer target modulus)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)

theorem word_evaluator (a : Access P) (L F C : List Bool→ℕ)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (parent : List Bool→List Bool) (hp : parent∈FP) (d W : List Bool→ℕ) (hd : BinaryFn d) (hW : UnaryFn W) :
    SpaceFunction (FixedWidthBivariateReboxBits.coefficient (arity P D H parent) W (head P D H parent d)) :=by
  have E:=coefficient_evaluator P D H a L F C hL hF hC h hb (parent∘origin) (mem_FP_comp origin_FP hp)
    (d∘origin) outer (W∘origin) (hd.comp origin_FP)
    (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)) (hW.comp origin_FP)
    target FixedWidthBivariateReboxBits.modulus (by polytime [target]) (by polytime [FixedWidthBivariateReboxBits.modulus])
  exact E.congr (funext fun _=>rfl)

noncomputable def reader (a : Access P) (L F C : List Bool→ℕ)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (parent : List Bool→List Bool) (hp : parent∈FP) (d W : List Bool→ℕ) (hd : BinaryFn d) (hW : UnaryFn W)
    (hfit : ∀c,headDegree P D H parent c<2^W c) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (arity P D H parent) W (head P D H parent d)) :=
  FixedWidthBivariateReader.reader (arity P D H parent) W (head P D H parent d)
    (FixedWidthBivariateReboxBits.coefficient (arity P D H parent) W (head P D H parent d))
    (word_evaluator P D H a L F C hL hF hC h hb parent hp d W hd hW)
    (arity_unary P D H parent a hp) hW (headDegree P D H parent) (head_coefficient_degree P D H parent d) hfit
    (FixedWidthBivariateReboxBits.coefficient_packet (arity P D H parent) W (head P D H parent d))

end LeanCanny.Algebra.IntegralMixedFramedFullCutHead
