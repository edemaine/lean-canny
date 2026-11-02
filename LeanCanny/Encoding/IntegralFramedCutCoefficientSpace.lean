/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutCoefficientTest
public import LeanCanny.Algebra.IntegralMixedFramedChoiceProbePullSpace
public import LeanCanny.Algebra.FixedWidthHeadLiftSpace
/-! # Native indexed full-coefficient signs on the actual successor root

The source coefficients are derived from current-Q controls, while an
unused head variable embeds them into the same successor tuple. Invalid
parent tasks have zero test polynomial. No coefficient or factor evaluator
is a caller premise.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutCoefficientTest
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open RationalSubstitution.Indexed
open IntegralMixedFramedCutProbeTaskBits (parameters)
open IntegralMixedFramedCutProbeTransportBits (plan data)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

private theorem coefficient_cast {a b : ℕ} (h : a=b) (p : MvPolynomial (Fin a) ℤ) (W k : ℕ) :
    (MvPolynomial.rename (Fin.cast h) p).coeff (nativeExponent (Equiv.refl (Fin b)) W k)=
      p.coeff (nativeExponent (Equiv.refl (Fin a)) W k) := by
  cases h
  rw [show (Fin.cast rfl : Fin a→Fin a)=id from by funext i; rfl,MvPolynomial.rename_id]
  rfl

private theorem pulled_polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (f : List Bool→List Bool) (q : List Bool) :
    ((IntegralMixedFramedChoiceProbeSourceBits.source P D H).pull f).poweredPolynomial
      (IntegralMixedFramedChoiceProbeSourceBits.horizon P∘f) q=
      IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H (f q) := by rfl

theorem coefficient_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) (hFpos : ∀ root,1≤F root)
    (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D H L F C) h) :
    SpaceFunction (SquareSampleCompleteIndexedPolynomialTest.coefficient (test P D H L F C hs hFpos hf)) := by
  let ctx:=RationalSubstitution.IntegerBits.context
  let target:=RationalSubstitution.IntegerBits.selectedDegree
  let f:=query P∘ctx
  have hq : f∈FP := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP (query_FP P a)
  let S:=IntegralMixedFramedChoiceProbeSourceBits.horizon P∘f
  let V:=fun q=>(degree P D H (ctx q)).size
  let A:=((IntegralMixedFramedChoiceProbeSourceBits.source P D H).pull f).arity
  let p:=((IntegralMixedFramedChoiceProbeSourceBits.source P D H).pull f).poweredPolynomial S
  have hS : UnaryFn S := (IntegralMixedFramedChoiceProbeSourceBits.horizon_unary P a).comp hq
  have HD : BinaryFn (fun q=>degree P D H (ctx q)) := (degree_binary P a D H).comp RationalSubstitution.IntegerBits.context_mem_FP
  have hV : UnaryFn V := (UnaryFn.length HD.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)
  have ht : target∈FP := RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  have ET:=IntegerParameterCoefficientBits.spatial_mem_FP V target hV ht
  have EP := IntegralMixedFramedChoiceProbeSourceBits.pulled_powered_evaluator P a D H L F C hL hF hC h hb
    f hq S V hS hV (IntegerParameterCoefficientBits.spatial V target) pairSnd ET pairSnd_mem_FP
  have EH:=FixedWidthHeadLiftBits.evaluator A V p target pairSnd hV ht EP
  have HG : FPPred (fun q=>IntegralMixedFramedFullCutProbeBits.Active P (pairFst (ctx q))) :=
    (IntegralMixedFramedFullCutProbeBits.active_FP P a).comp (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP)
  have EB:=SpaceFunction.branch (fun q=>decide (IntegralMixedFramedFullCutProbeBits.Active P (pairFst (ctx q)))) HG.flag_mem_FP EH
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  apply EB.congr
  funext q
  simp only [decide_eq_true_eq]
  unfold SquareSampleCompleteIndexedPolynomialTest.coefficient FixedWidthRationalSubstitutionBits.Family.coefficient
  change (if IntegralMixedFramedFullCutProbeBits.Active P (pairFst (ctx q)) then
      FixedWidthRowBits.value (fun q=>A q+1) V (fun q=>MvPolynomial.rename Fin.succ (p q)) target pairSnd q else [])=
    residueBits (((polynomial P D H L F C hs (pairFst (ctx q)) (pairSnd (ctx q))).coeff
      (exponentVector ((IntegralFramedCutSuccessor.input P D H L F C hs).count (pairFst (ctx q)))
        (entry (V q) (Nat.fromBitsLE (target q)))) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q)+1))
  rw [←nativeExponent_refl]
  by_cases ha : IntegralMixedFramedFullCutProbeBits.Active P (pairFst (ctx q))
  · rw [ite_eq_left ha,polynomial,dite_eq_left ha,coefficient_cast,query_normalize]
    unfold FixedWidthRowBits.value
    have hp : p q=IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H (query P (ctx q)) :=
      pulled_polynomial P D H f q
    exact congrArg (fun u : MvPolynomial (Fin (A q)) ℤ => residueBits
      (((MvPolynomial.rename Fin.succ u).coeff (nativeExponent (Equiv.refl (Fin (A q+1)))
        (V q) (Nat.fromBitsLE (target q))) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q)+1))) hp

  · rw [ite_eq_right ha,polynomial,dite_eq_right ha]
    change []=residueBits ((0 : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q)+1))
    rw [Int.cast_zero]
    rfl

end LeanCanny.Encoding.IntegralFramedCutCoefficientTest
