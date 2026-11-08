/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankOrderTest
/-! # Fully guarded native order languages on actual complete joint roots

Both retained labels and the complete-root word are checked. In particular,
the zero reply assigned to an invalid retained label never makes it equal.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankOrderTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankOrderBits (Labels count)
open IntegralMixedFramedBankSnapshotBits (atKey)
open Turing.MultiTapeTM
open scoped Classical

noncomputable def language (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool→List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) (left right : List Bool→ℕ) (sign : SignType) : Language :=
  {q | Labels P D H key left right (pairFst (pairFst q)) ∧ q∈SquareSampleCompleteIndexedPolynomialTest.language
    (IntegralFramedBankTermTest.input P D H s hs key hpos)
    (IntegralFramedBankTermTest.test P D H s hs key hpos (IntegralMixedFramedBankOrderBits.word P D H key left right)) sign}

theorem decider (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    (key : List Bool→List Bool) (hk : key∈FP) (hpos : ∀ c,0<(atKey P D H (key c)).count)
    (left right : List Bool→ℕ) (hl : BinaryFn left) (hr : BinaryFn right) (sign : SignType) :
    SpaceDecider (language P D H s hs key hpos left right sign) := by
  have HG := ComputableInPolySpace.of_tidyPolyTime
    ((IntegralMixedFramedBankOrderBits.labels_FP P a D H key hk left right hl hr).comp
      (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).computable
  have DT := SquareSampleCompleteIndexedPolynomialTest.decider
    (IntegralFramedBankTermTest.input_access P a D H s hs hF hL key hk hpos)
    (IntegralFramedBankTermTest.test_access P a D H s hs hF hL key hk hpos _
      (IntegralMixedFramedBankOrderBits.word_FP P a D H key hk left right hl hr)) sign
  have HF := ComputableInPolySpace.of_tidyPolyTime
    (ComputableTidilyInPolyTime.const (encIn:=encBits) (encMid:=encBool) false)
  apply SpaceDecider.of_computable (HG.ite DT.computable HF)
  intro q
  change (_ ∧ _)↔(if decide (Labels P D H key left right (pairFst (pairFst q))) then decide _ else false)=true
  by_cases h : Labels P D H key left right (pairFst (pairFst q)) <;>
    simp only [h,decide_true,decide_false,ite_true,ite_false,true_and,false_and,Bool.false_eq_true,decide_eq_true_eq]

theorem packet_mem_iff (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool→List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) (hroot : ∀ c,pairFst (key c)=c)
    (left right : List Bool→ℕ) (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedBankTermTest.input P D H s hs key hpos) c w)
    (hl : left c<count P D H key c) (hr : right c<count P D H key c) (sign : SignType) :
    pair (pair c w) d∈language P D H s hs key hpos left right sign ↔
      SignType.sign ((LeanCanny.Geometry.IntegralMixedFramedBankOrder.polynomial P D H key left right c).eval₂ (Int.castRingHom ℝ)
        (SquareSampleCompleteVertices.candidate (IntegralFramedBankTermTest.input P D H s hs key hpos) c w hv).val)=sign := by
  have HL : Labels P D H key left right c := ⟨hl,hr⟩
  have HE:=packet_positive_polynomial P D H s hs key hpos hroot left right c w d hv hl hr
  simp only [value,pairFst_pair,HL,decide_true,ite_true] at HE
  change (_ ∧ (_ ∧ IntegralFramedBankTermTest.value P D H s hs key hpos _ (pair (pair c w) d)=_))↔_
  simp only [pairFst_pair,pairSnd_pair,HL,hv,true_and,HE,SquareSampleTestSign.encode_eq_iff]

end LeanCanny.Encoding.IntegralFramedBankOrderTest
