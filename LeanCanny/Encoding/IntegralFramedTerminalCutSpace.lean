/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalCutSource
public import LeanCanny.Algebra.IntegralMixedFramedChoiceProbePullSpace
/-! # Original-only native full-factor probes at one terminal vertex

Every coefficient uses the actual current-Q factor backend with the
original caller modulus. The only additional operations are an original
arity comparison and suffix layout transport. No factor, matrix or
coefficient evaluator is supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCutProbeTaskBits (parameters)
open IntegralMixedFramedCutProbeTransportBits (plan data)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralFramedCutCoefficientTest.query

private theorem coefficient_cast {a b : ℕ} (h : a=b) (p : MvPolynomial (Fin a) ℤ) (W k : ℕ) :
    (MvPolynomial.rename (Fin.cast h) p).coeff (nativeExponent (Equiv.refl (Fin b)) W k)=
      p.coeff (nativeExponent (Equiv.refl (Fin a)) W k) := by
  cases h
  rw [show (Fin.cast rfl : Fin a→Fin a)=id from by funext i; rfl,MvPolynomial.rename_id]
  rfl

variable (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q)
  (key : List Bool→List Bool) (hk : key∈FP) (hpos : ∀ q,0<(family P D H).birth (key q))
  (h : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C))
  (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D H L F C) h)

include a hL hF hC hk h hb in
theorem coefficient_evaluator : SpaceFunction (SquareSampleCompleteSuffixPolynomialTest.coefficient
    (source P D H L F C hs key hpos hFpos hf)) := by
  let ctx:=RationalSubstitution.IntegerBits.context
  let target:=RationalSubstitution.IntegerBits.selectedDegree
  let f:=fun q=>IntegralFramedCutCoefficientTest.query P (pair (pairFst (ctx q)) (pairSnd (ctx q)))
  have hq : f∈FP:=mem_FP_comp
    (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP)
      (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP))
    (IntegralFramedCutCoefficientTest.query_FP P a)
  let S:=IntegralMixedFramedChoiceProbeSourceBits.horizon P∘f
  let V:=fun q=>(IntegralMixedFramedChoiceProbeSourceBits.degree P D H (f q)+1).size
  have hS : UnaryFn S:=(IntegralMixedFramedChoiceProbeSourceBits.horizon_unary P a).comp hq
  have HD0 : BinaryFn (fun q=>IntegralMixedFramedChoiceProbeSourceBits.degree P D H (f q)):=
    (IntegralMixedFramedChoiceProbeSourceBits.degree_binary P a D H).comp hq
  have HD : BinaryFn (fun q=>IntegralMixedFramedChoiceProbeSourceBits.degree P D H (f q)+1):=HD0.add (BinaryFn.const 1)
  have hV : UnaryFn V:=(UnaryFn.length HD.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)
  have EP:=IntegralMixedFramedChoiceProbeSourceBits.pulled_powered_evaluator P a D H L F C hL hF hC h hb
    f hq S V hS hV target pairSnd RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
  have HO : UnaryFn (fun q=>oldArity P D H (pairFst (ctx q)) (pairSnd (ctx q))) :=
    (oldArity_unary P a D H).comp RationalSubstitution.IntegerBits.context_mem_FP
  have HC : UnaryFn (fun q=>count P D H key (pairFst (ctx q))) :=
    (count_unary P a D H key hk).comp (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP)
  have HG:=(BinaryFn.ofUnary HO).le (BinaryFn.ofUnary HC)
  have E:=SpaceFunction.branch (fun q=>decide (oldArity P D H (pairFst (ctx q)) (pairSnd (ctx q))≤count P D H key (pairFst (ctx q))))
    HG.flag_mem_FP EP (SpaceFunction.ofFP _ (constFn_mem_FP []))
  apply E.congr
  funext q
  unfold SquareSampleCompleteSuffixPolynomialTest.coefficient SquareSampleCompleteSuffixPolynomialTest.oldCoefficient
  simp only [source]
  by_cases hfit:oldArity P D H (pairFst (ctx q)) (pairSnd (ctx q))≤count P D H key (pairFst (ctx q))
  · rw [ite_eq_left (by simpa only [decide_eq_true_eq] using hfit),polynomial,dite_eq_left hfit]
    unfold arity
    rw [coefficient_cast]
    rfl
  · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hfit),polynomial,dite_eq_right hfit]
    change []=residueBits ((0 :ℤ) : ZMod (Nat.fromBitsLE (pairSnd q)+1))
    rw [Int.cast_zero]
    rfl

include a hL hF hC hk h hb in
theorem access : (source P D H L F C hs key hpos hFpos hf).Access where
  newer := by
    have HC:=(count_unary P a D H key hk).comp pairFst_mem_FP
    exact HC.sub ((oldArity_unary P a D H).min HC)
  degree := by
    have HD : BinaryFn (fun z=>IntegralMixedFramedChoiceProbeSourceBits.degree P D H
        (IntegralFramedCutCoefficientTest.query P (pair (pairFst z) (pairSnd z)))) :=
      (IntegralMixedFramedChoiceProbeSourceBits.degree_binary P a D H).comp
        (mem_FP_comp (mem_FP_pair pairFst_mem_FP pairSnd_mem_FP) (IntegralFramedCutCoefficientTest.query_FP P a))
    exact HD.add (BinaryFn.const 1)
  mass := by
    have HM : BinaryFn (fun z=>IntegralMixedFramedChoiceProbeSourceBits.massBound P D H L F C
        (IntegralFramedCutCoefficientTest.query P (pair (pairFst z) (pairSnd z)))) :=
      (IntegralMixedFramedChoiceProbeSourceBits.massBound_binary P a D H L F C hL hF hC).comp
        (mem_FP_comp (mem_FP_pair pairFst_mem_FP pairSnd_mem_FP) (IntegralFramedCutCoefficientTest.query_FP P a))
    exact HM.add (BinaryFn.const 1)
  coefficient := coefficient_evaluator P a D H L F C hs hL hF hC hFpos hf key hk hpos h hb

end LeanCanny.Encoding.IntegralFramedTerminalCutTest
