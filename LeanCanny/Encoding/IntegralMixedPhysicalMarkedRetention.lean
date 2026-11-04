/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedSemantics
public import LeanCanny.Encoding.IntegralMixedMarkedPreludeCongruence
public import LeanCanny.Encoding.IntegralMixedPhysicalChronologicalPoint
/-! # Original leaves and marked equations survive a fresh sampled history

Only the original candidate and its first n+8 numerical bank values are
retained. The histories, complete words and sampler roots may all differ.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalMarkedRetention
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (candidate original number)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedPhysicalMarkedSemantics (env)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedPhysicalMarkedPlan.tables
 IntegralMixedFramedHistoryFamilyBits.family env


variable (cL cR wL wR : List Bool)
 (hL : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false) (sampleContext cL) wL)
 (hR : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false) (sampleContext cR) wR)
 (hc : candidate cL=candidate cR)
 (he : ∀i < number n cL+8,env hn ht ha (radius_binary hR0) false cL wL hL i=
   env hn ht ha (radius_binary hR0) false cR wR hR i)

include hc he in
theorem leaves_transfer (HL : pair cL wL∈IntegralMixedPhysicalMarkedTest.leaves hn ht ha (radius_binary hR0) false) :
    pair cR wR∈IntegralMixedPhysicalMarkedTest.leaves hn ht ha (radius_binary hR0) false :=by
  obtain ⟨_,HH⟩:=(IntegralMixedPhysicalMarkedSemantics.leaves_iff hn ht ha (radius_binary hR0) false cL wL).mp HL
  apply (IntegralMixedPhysicalMarkedSemantics.leaves_iff hn ht ha (radius_binary hR0) false cR wR).mpr
  refine ⟨hR,?_⟩
  intro i hi
  have HN:=IntegralMixedMarkedPreludeCongruence.number_eq (n:=n) cL cR hc
  have HI : i < number n cL+8:=by simpa only [Bool.false_eq_true,ite_false,HN] using hi
  have HP:=IntegralMixedMarkedPreludeCongruence.polynomial hn ht ha R0 cL cR hc i
  have HX:=HH i (by simpa only [Bool.false_eq_true,ite_false] using HI)
  change ((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha (radius R0)).polynomial
    (pair cR (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (env hn ht ha (radius_binary hR0) false cR wR hR i)=0
  rw [←HP,←he i HI]
  exact HX

include hc he in
theorem mark_eq :
    IntegralMixedPhysicalMarkedTest.markValue hn ht ha (radius_binary hR0) false (pair cL wL)=
      IntegralMixedPhysicalMarkedTest.markValue hn ht ha (radius_binary hR0) false (pair cR wR) :=by
  rw [IntegralMixedPhysicalMarkedSemantics.mark_packet hn ht ha (radius_binary hR0) false cL wL hL,
    IntegralMixedPhysicalMarkedSemantics.mark_packet hn ht ha (radius_binary hR0) false cR wR hR]
  have HO:=IntegralMixedMarkedPreludeCongruence.original_eq cL cR hc
  have HN:=IntegralMixedMarkedPreludeCongruence.number_eq (n:=n) cL cR hc
  rw [←HO,←HN]
  apply congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v))
  apply Term.eval_congr
  intro i hi
  exact he i (hi.trans_le (BoundedMarkedParameterTerm.mark_arity _ _ (ha (original cL))))

include hc he in
theorem regular_eq :
    IntegralMixedPhysicalMarkedTest.regularValue hn ht ha (radius_binary hR0) false (pair cL wL)=
      IntegralMixedPhysicalMarkedTest.regularValue hn ht ha (radius_binary hR0) false (pair cR wR) :=by
  rw [IntegralMixedPhysicalMarkedSemantics.regular_packet hn ht ha (radius_binary hR0) false cL wL hL,
    IntegralMixedPhysicalMarkedSemantics.regular_packet hn ht ha (radius_binary hR0) false cR wR hR]
  have HO:=IntegralMixedMarkedPreludeCongruence.original_eq cL cR hc
  have HN:=IntegralMixedMarkedPreludeCongruence.number_eq (n:=n) cL cR hc
  have HD : IntegralMixedMarkedPointTest.degree t cL=IntegralMixedMarkedPointTest.degree t cR:=by
    unfold IntegralMixedMarkedPointTest.degree IntegralMixedMarkedPointTest.charge
    rw [HO]
  rw [←HO,←HN,←HD]
  apply congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v))
  apply Term.eval_congr
  intro i hi
  apply he i
  apply hi.trans_le (BoundedMarkedParameterTerm.regular_arity _ _ _ (ha (original cL)) _)
  unfold IntegralMixedMarkedPointTest.degree LeanCanny.Geometry.BoundedZeroSource.powerDegree LeanCanny.Geometry.BoundedZeroSource.powerHalfDegree
  positivity

include hc he in
theorem language_transfer (HL : pair cL wL∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false) :
    pair cR wR∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false :=
  ⟨leaves_transfer hn ht ha hR0 cL cR wL wR hL hR hc he HL.1,
    (regular_eq hn ht ha hR0 cL cR wL wR hL hR hc he).symm.trans HL.2.1,
    (mark_eq hn ht ha hR0 cL cR wL wR hL hR hc he).symm.trans HL.2.2⟩


end LeanCanny.Encoding.IntegralMixedPhysicalMarkedRetention
