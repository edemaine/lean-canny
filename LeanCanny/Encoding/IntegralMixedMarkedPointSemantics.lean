/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPointReadback
public import LeanCanny.Geometry.BoundedMarkedParameterSemantics
/-! # Native marked replay tests are the actual bounded regular-source equations -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPointSemantics
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number original)
open IntegralMixedCandidateReplayNew (bank input sampleContext)
open IntegralMixedMarkedPointTest (charge markWord regularWord markValue regularValue)
open IntegralMixedMarkedPointReadback (env point)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)

private theorem mark_syntax (ctx : List Bool) :
    (IntegralMixedFramedBankTermBits.source (markWord n t)).syntax ((bank hn ht ha hR).key (sampleContext ctx))=
      BoundedMarkedParameterTerm.mark (t (original ctx)) (number n ctx) := by
  change TermView.term (markWord n t (pairFst ((bank hn ht ha hR).key (sampleContext ctx))))=_
  rw [IntegralMixedMarkedPointReadback.key_root]
  exact TermView.term_toBits _

private theorem regular_syntax (ctx : List Bool) :
    (IntegralMixedFramedBankTermBits.source (regularWord n t)).syntax ((bank hn ht ha hR).key (sampleContext ctx))=
      BoundedMarkedParameterTerm.regular (t (original ctx)) (number n ctx) (IntegralMixedMarkedPointTest.degree t ctx) := by
  change TermView.term (regularWord n t (pairFst ((bank hn ht ha hR).key (sampleContext ctx))))=_
  rw [IntegralMixedMarkedPointReadback.key_root]
  exact TermView.term_toBits _

theorem mark_packet (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w) :
    markValue hn ht ha hR (pair ctx w)=InfinitesimalSign.encode
      (SignType.sign ((BoundedMarkedParameterTerm.mark (t (original ctx)) (number n ctx)).eval (env hn ht ha hR ctx w hv))) := by
  have H:=IntegralFramedBankTermCurrentQ.packet (bank hn ht ha hR) (markWord n t) (sampleContext ctx) w [] hv
  have HS:=mark_syntax hn ht ha hR ctx
  have HE:=congrArg (fun z : Term=>InfinitesimalSign.encode (SignType.sign (z.eval (env hn ht ha hR ctx w hv)))) HS
  simpa only [markValue,Function.comp_apply,IntegralMixedMarkedPointTest.probe,pairFst_pair,pairSnd_pair] using H.trans HE

theorem regular_packet (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w) :
    regularValue hn ht ha hR (pair ctx w)=InfinitesimalSign.encode
      (SignType.sign ((BoundedMarkedParameterTerm.regular (t (original ctx)) (number n ctx)
        (IntegralMixedMarkedPointTest.degree t ctx)).eval (env hn ht ha hR ctx w hv))) := by
  have H:=IntegralFramedBankTermCurrentQ.packet (bank hn ht ha hR) (regularWord n t) (sampleContext ctx) w [] hv
  have HS:=regular_syntax hn ht ha hR ctx
  have HE:=congrArg (fun z : Term=>InfinitesimalSign.encode (SignType.sign (z.eval (env hn ht ha hR ctx w hv)))) HS
  simpa only [regularValue,Function.comp_apply,IntegralMixedMarkedPointTest.probe,pairFst_pair,pairSnd_pair] using H.trans HE

theorem equations (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w)
    (hl : IntegralMixedMarkedLeafScan.holds hn ht ha hR (pair ctx w)) :
    regularValue hn ht ha hR (pair ctx w)=InfinitesimalSign.encode (SignType.sign
      ((LeanCanny.Geometry.BoundedRegularSource.polynomial ((t (original ctx)).finitePolynomial (number n ctx))
        (charge t ctx) (charge t ctx) (R ctx)).eval₂ (Int.castRingHom ℝ) (point hn ht ha hR ctx w hv))) ∧
    markValue hn ht ha hR (pair ctx w)=InfinitesimalSign.encode (SignType.sign
      ((LeanCanny.Geometry.BoundedRegularSource.markPolynomial ((t (original ctx)).finitePolynomial (number n ctx))
        (R ctx)).eval₂ (Int.castRingHom ℝ) (point hn ht ha hR ctx w hv))) := by
  obtain ⟨hr,hL,hB,hK⟩:=IntegralMixedMarkedPointReadback.parameters hn ht ha hR ctx w hv hl
  have HT : (t (original ctx)).arity≤number n ctx:=ha (original ctx)
  have HR:=LeanCanny.Geometry.BoundedMarkedParameterSemantics.regular_eval (t (original ctx)) (number n ctx)
    (charge t ctx) (R ctx) HT (env hn ht ha hR ctx w hv) hr hL hB hK
  have HM:=LeanCanny.Geometry.BoundedMarkedParameterSemantics.mark_eval (t (original ctx)) (number n ctx)
    (R ctx) HT (env hn ht ha hR ctx w hv) hr
  refine ⟨(regular_packet hn ht ha hR ctx w hv).trans ?_,(mark_packet hn ht ha hR ctx w hv).trans ?_⟩
  · exact congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v)) HR
  · exact congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v)) HM

end LeanCanny.Encoding.IntegralMixedMarkedPointSemantics
