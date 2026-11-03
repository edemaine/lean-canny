/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiMass
public import LeanCanny.Encoding.SquareSampleCompleteTarskiParameterTest
/-! # Actual two-parameter principal signs use the same complete terminal vertex

Only literal count alignment connects the saved bank to the complete sampler.
All principal, scalar, coordinate and coefficient-sign costs are derived from
original current-Q arithmetic; there is no selected-element sign oracle.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalTarskiParameterTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open IntegralMixedFramedTerminalTarskiFamilyBits
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  SquareSampleCompleteIndexedPolynomialTest.value SquareSampleCompleteSuffixPolynomialTest.test

variable (S : SquareSampleInput.Inputs)
variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (d e center selected : List Bool→ℕ)
variable (power : List Bool→Fin 3) (negativeEta negativeEpsilon : Bool)
variable (read : List Bool→List Bool) (j delta epsilon : List Bool→ℕ)
variable (hcount : ∀ c b,arity P D H terminal (read (pair c b))=S.count c)

include hcount in
theorem dimension (c b : List Bool) :
    (family P D H L F C hs parent terminal d e center selected power negativeEta negativeEpsilon).arity
      (read (pair c b))=S.count c+2 :=by
  change 1+(arity P D H terminal (read (pair c b))+1)=S.count c+2
  rw [hcount]
  omega

noncomputable def source (hF : ∀ root,1≤F root)
    (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key) :=
  SquareSampleCompleteTarskiParameterTest.source S
    (family P D H L F C hs parent terminal d e center selected power negativeEta negativeEpsilon)
    read j delta epsilon (wholeBound P D H L F C hs parent terminal d e center selected ∘ read)
    (principalHeight P D H L F C hs parent terminal d e center selected ∘ read)
    (dimension S P D H L F C hs parent terminal d e center selected power negativeEta negativeEpsilon read hcount)
    (fun c b=>principal_degree P D H L F C hs parent terminal d e center selected power negativeEta negativeEpsilon
      (read (pair c b)) (j (pair c b)))
    (fun c b=>principal_mass P D H L F C hs parent terminal d e center selected hF hf power negativeEta negativeEpsilon
      (read (pair c b)) (j (pair c b)))

theorem evaluator (hS : S.Access) (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (IntegralMixedFramedHistoryFamilyBits.family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (bank : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hbank : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew bank)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (he : BinaryFn e) (hc : BinaryFn center) (hi : BinaryFn selected)
    (hpower : BinaryFn (fun c=>(power c).val)) (hr : read∈FP) (hj : BinaryFn j) (hdelta : BinaryFn delta) (hepsilon : BinaryFn epsilon)
    (hfactor : ∀ root,1≤F root) (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key) :
    SpaceFunction (SquareSampleCompleteIndexedPolynomialTest.value S (SquareSampleCompleteSuffixPolynomialTest.test
      (source S P D H L F C hs parent terminal d e center selected power negativeEta negativeEpsilon read j delta epsilon hcount hfactor hf))) :=by
  unfold source
  let MF:=family P D H L F C hs parent terminal d e center selected power negativeEta negativeEpsilon
  let A:=IntegralMixedFramedTerminalTarskiFamilyBits.access P D H L F C hs parent terminal d e center selected a hL hF hC I h hb
    Hnew bank hbank hp ht hd he hc hi power hpower negativeEta negativeEpsilon
  have HW:=width_unary P D H L F C hs parent terminal d e center selected a hp ht hd he hc hi
  have HWmodel : UnaryFn MF.width:=by
    unfold MF family
    dsimp only [FixedWidthTarskiPrincipalBits.Family.width]
    exact HW
  have HD : BinaryFn (degree d):=degree_binary d hd
  have HP:=IntegralMixedFramedTerminalTarskiHeadBits.degreeBound_binary P D H L F C hs parent terminal e center a hp ht he hc
  have HQ : BinaryFn (queryBound P D H L F C hs terminal selected):=(BinaryFn.const 2).mul
    ((IntegralMixedFramedWindowQuery.weight_binary P D H L F C hs terminal selected a ht hi).add (BinaryFn.const 1))
  have HR:=MultivariateTarskiDegreeBounds.principalDegreeBound_binary HD (HD.sub (BinaryFn.const 1))
    (HD.add (BinaryFn.const 2)) HP HQ
  have HB : BinaryFn (wholeBound P D H L F C hs parent terminal d e center selected):=(HP.add HQ).add HR
  have HM:=principalHeight_binary P D H L F C hs parent terminal d e center selected a hL hF hC I hp ht hd he hc hi
  have HFIT (c b : List Bool) : wholeBound P D H L F C hs parent terminal d e center selected (read (pair c b))<
      2^MF.width (read (pair c b)) :=by
    unfold MF family
    dsimp only [FixedWidthTarskiPrincipalBits.Family.width]
    unfold IntegralMixedFramedTerminalTarskiFamilyBits.width
    exact Nat.lt_size_self (wholeBound P D H L F C hs parent terminal d e center selected (read (pair c b)))
  exact SquareSampleCompleteTarskiParameterTest.evaluator S MF read j delta epsilon
    (wholeBound P D H L F C hs parent terminal d e center selected ∘ read)
    (principalHeight P D H L F C hs parent terminal d e center selected ∘ read)
    (dimension S P D H L F C hs parent terminal d e center selected power negativeEta negativeEpsilon read hcount)
    (fun c b=>principal_degree P D H L F C hs parent terminal d e center selected power negativeEta negativeEpsilon
      (read (pair c b)) (j (pair c b)))
    (fun c b=>principal_mass P D H L F C hs parent terminal d e center selected hfactor hf power negativeEta negativeEpsilon
      (read (pair c b)) (j (pair c b))) hS A HWmodel hr hj hdelta hepsilon (HB.comp hr) (HM.comp hr) HFIT


end LeanCanny.Encoding.IntegralFramedTerminalTarskiParameterTest
