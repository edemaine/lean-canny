/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedChoiceProbePackets
/-! # Charged native lower-choice coefficients at arbitrary caller moduli

The supplied controls are for the honest copied original root with its
caller-modulus budget. Their verified seven-routine current-Q machine
provides every critical, PSC, Gram and earlier leading reply. No factor,
coefficient, leading, denominator or matrix evaluator is a premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedChoiceProbePacketBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCutProbeTaskBits (parameters)
open IntegralMixedFramedCutProbeTransportBits (plan data)
open scoped Classical

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D H L F C) h) :
    SpaceFunction (value P D H) := by
  have E := (IntegralMixedFramedFullChoiceProbeBits.evaluator (parameters P L F C)
    (IntegralMixedFramedCutProbeTaskBits.access P a L F C hL hF hC) (plan P D L F C) (data P D H L F C) h hb).precompose
    (IntegralMixedFramedChoiceProbeTaskBits.query P L F C) (IntegralMixedFramedChoiceProbeTaskBits.query_FP P a L F C hL hF hC)
  have EB := SpaceFunction.branch (fun q=>decide (Labels P q)) (labels_FP P a).flag_mem_FP
    E (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact EB.congr (funext fun q=>by
    simp only [Function.comp_apply,decide_eq_true_eq]
    by_cases hl : Labels P q
    · rw [ite_eq_left hl]
      exact query_value P D H L F C q hl
    · rw [ite_eq_right hl]
      exact (value_outside P D H q hl).symm)

attribute [local irreducible] IntegralCoordinateCoefficientBits.Family.matrix IntegralMixedFramedChoiceProbeSourceBits.source

theorem packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c mw : List Bool)
    (i j : Fin (FixedWidthPolynomial.count ((IntegralMixedFramedChoiceProbeSourceBits.source P D H).arity c)
      ((IntegralMixedFramedChoiceProbeSourceBits.source P D H).width c))) :
    value P D H (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))=
      residueBits (((IntegralMixedFramedChoiceProbeSourceBits.source P D H).matrix c i j : ℤ) : ZMod (Nat.fromBitsLE mw+1)) := by
  have HB : IntegralMixedFramedCutProbeTaskBits.original
      (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))=c := by
    simp only [IntegralMixedFramedCutProbeTaskBits.original,PaddedIntegralGeneratorSource.base,pairFst_pair]
  have HR : IntegralMixedFramedCutProbeTaskBits.row
      (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))=i.val := by
    simp only [IntegralMixedFramedCutProbeTaskBits.row,PaddedIntegralGeneratorSource.row,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HC : IntegralMixedFramedCutProbeTaskBits.col
      (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))=j.val := by
    simp only [IntegralMixedFramedCutProbeTaskBits.col,PaddedIntegralGeneratorSource.col,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HM : IntegralMixedFramedCutProbeTaskBits.callerModulus
      (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))=Nat.fromBitsLE mw+1 := by
    simp only [IntegralMixedFramedCutProbeTaskBits.callerModulus,PaddedIntegralGeneratorSource.modulus,pairFst_pair,pairSnd_pair]
  unfold value
  rw [HB,HR,HC,HM,IntegralCriticalTotalSnapshotBits.integerEntry,dite_eq_left i.isLt,dite_eq_left j.isLt]

end LeanCanny.Algebra.IntegralMixedFramedChoiceProbePacketBits

namespace LeanCanny.Algebra.IntegralMixedFramedChoiceProbeSourceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCutProbeTaskBits (parameters)
open IntegralMixedFramedCutProbeTransportBits (plan data)

/-- The actual canonical coefficient polynomial can now be read at any
requested fixed-power monomial and any caller modulus. -/
theorem powered_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D H L F C) h)
    (S V : List Bool→ℕ) (hS : UnaryFn S) (hV : UnaryFn V)
    (target modulus : List Bool→List Bool) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (source P D H).arity V ((source P D H).poweredPolynomial S) target modulus) :=
  IntegralCoordinateCoefficientBits.powered_evaluator (source P D H) S V target modulus
    (IntegralMixedFramedChoiceProbePacketBits.value P D H) hS (arity_unary P a D H) (width_unary P a D H) hV ht hm
    (IntegralMixedFramedChoiceProbePacketBits.evaluator P a D H L F C hL hF hC h hb)
    (IntegralMixedFramedChoiceProbePacketBits.packet P D H)

end LeanCanny.Algebra.IntegralMixedFramedChoiceProbeSourceBits
