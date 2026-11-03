/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPointSemantics
/-! # Exact native membership in the marked regular source

Every original prelude leaf is checked untruncated at one complete joint
vertex. The first n+4 actual retained coordinates form the marked point;
the four remaining coordinates are proved large powers, not assumptions.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedReplayValidity
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number original source)
open IntegralMixedCandidateReplayNew (input sampleContext)
open IntegralMixedMarkedPointTest (charge language)
open IntegralMixedMarkedPointReadback (point)
open LeanCanny.Geometry.BoundedRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)

theorem accepted_iff (ctx w : List Bool) : pair ctx w∈language hn ht ha hR ↔
    ∃ hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w,
      (∀ i<number n ctx+8,((source hn ht ha R).polynomial (pair ctx (BinaryNatCode.encode i))).eval₂
        (Int.castRingHom ℝ) (IntegralMixedMarkedLeafTest.point hn ht ha hR ctx w hv i)=0) ∧
      ∃ z : Marked ((t (original ctx)).finitePolynomial (number n ctx)) (charge t ctx) (charge t ctx) (R ctx),
        z.val.val=point hn ht ha hR ctx w hv := by
  constructor
  · intro H
    change (SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext (pairFst (pair ctx w))) (pairSnd (pair ctx w)) ∧
      IntegralMixedMarkedLeafScan.holds hn ht ha hR (pair ctx w)) ∧ _ at H
    simp only [pairFst_pair,pairSnd_pair] at H
    obtain ⟨⟨hv,hl⟩,hF,hM⟩:=H
    obtain ⟨EF,EM⟩:=IntegralMixedMarkedPointSemantics.equations hn ht ha hR ctx w hv hl
    have HF := sign_eq_zero_iff.mp ((SquareSampleTestSign.encode_eq_iff _ _).mp (EF.symm.trans hF))
    have HM := sign_eq_zero_iff.mp ((SquareSampleTestSign.encode_eq_iff _ _).mp (EM.symm.trans hM))
    refine ⟨hv,(IntegralMixedMarkedLeafScan.holds_iff hn ht ha hR ctx w hv).mp hl,?_⟩
    exact ⟨⟨⟨point hn ht ha hR ctx w hv,HF⟩,HM⟩,rfl⟩
  · rintro ⟨hv,hr,z,hz⟩
    have hl:=(IntegralMixedMarkedLeafScan.holds_iff hn ht ha hR ctx w hv).mpr hr
    obtain ⟨EF,EM⟩:=IntegralMixedMarkedPointSemantics.equations hn ht ha hR ctx w hv hl
    have HF : (polynomial ((t (original ctx)).finitePolynomial (number n ctx)) (charge t ctx) (charge t ctx) (R ctx)).eval₂
        (Int.castRingHom ℝ) (point hn ht ha hR ctx w hv)=0 := by rw [←hz]; exact z.val.property
    have HM : (markPolynomial ((t (original ctx)).finitePolynomial (number n ctx)) (R ctx)).eval₂
        (Int.castRingHom ℝ) (point hn ht ha hR ctx w hv)=0 := by rw [←hz]; exact z.property
    refine ⟨?_,EF.trans (congrArg InfinitesimalSign.encode (sign_eq_zero_iff.mpr HF)),
      EM.trans (congrArg InfinitesimalSign.encode (sign_eq_zero_iff.mpr HM))⟩
    simpa only [IntegralMixedMarkedLeafScan.language,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair] using And.intro hv hl

theorem language_normalize (q : List Bool) : pair (pairFst q) (pairSnd q)∈language hn ht ha hR ↔q∈language hn ht ha hR := by
  simp only [IntegralMixedMarkedPointTest.language,Set.mem_ofPred_eq,IntegralMixedMarkedLeafScan.language,IntegralMixedMarkedLeafScan.holds,
    IntegralMixedMarkedLeafScan.probe,IntegralMixedMarkedPointTest.regularValue,IntegralMixedMarkedPointTest.markValue,
    Function.comp_apply,IntegralMixedMarkedPointTest.probe,pairFst_pair,pairSnd_pair]

theorem mem_PSPACE : language hn ht ha hR∈PSPACE := (IntegralMixedMarkedPointTest.decider hn ht ha hR).mem_PSPACE

end LeanCanny.Encoding.IntegralMixedMarkedReplayValidity
