/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedChoiceProbeBounds
public import LeanCanny.Algebra.IntegralCoordinatePullSpace
/-! # Indexed cut tests reuse the original full-factor coefficient reader

The query writer can change binary choice/coefficient selectors while the
sampling source remains fixed. All matrix cost is derived from the actual
original current-Q controls at the honest caller-modulus pullback.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedChoiceProbeSourceBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCutProbeTaskBits (parameters)
open IntegralMixedFramedCutProbeTransportBits (plan data)

theorem pulled_powered_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D H L F C) h)
    (query : List Bool→List Bool) (hq : query∈FP) (S V : List Bool→ℕ) (hS : UnaryFn S) (hV : UnaryFn V)
    (target modulus : List Bool→List Bool) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value ((source P D H).pull query).arity V
      (((source P D H).pull query).poweredPolynomial S) target modulus) :=
  IntegralCoordinateCoefficientBits.pulled_powered_evaluator (source P D H) query hq S V target modulus
    (IntegralMixedFramedChoiceProbePacketBits.value P D H) hS (arity_unary P a D H) (width_unary P a D H) hV ht hm
    (IntegralMixedFramedChoiceProbePacketBits.evaluator P a D H L F C hL hF hC h hb)
    (IntegralMixedFramedChoiceProbePacketBits.packet P D H)

end LeanCanny.Algebra.IntegralMixedFramedChoiceProbeSourceBits
