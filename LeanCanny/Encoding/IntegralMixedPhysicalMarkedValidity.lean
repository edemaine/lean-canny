/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedSemantics
/-! # Exact native marked acceptance at a full physical complete vertex

One full vertex supplies every original leaf and both marked equations.
All power parameters follow from untruncated leaves, including signed
outer cutoffs; no separate root witness or interpreting hom is assumed.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalMarkedValidity
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number original)
open IntegralMixedPhysicalMarkedPlan (originalSource)
open IntegralMixedPhysicalMarkedTest (input sampleContext language regularValue markValue)
open IntegralMixedPhysicalMarkedSemantics (point env)
open IntegralMixedMarkedPointTest (charge)
open LeanCanny.Geometry.BoundedRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

theorem accepted_iff (ctx w : List Bool) : pair ctx w∈language hn ht ha hR outer ↔
    ∃hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w,
      (∀i<number n ctx+(if outer then 10 else 8),((originalSource hn ht ha (R:=R) outer).polynomial
        (pair ctx (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (env hn ht ha hR outer ctx w hv i)=0) ∧
      ∃z : Marked ((t (original ctx)).finitePolynomial (number n ctx)) (charge t ctx) (charge t ctx) (R ctx),
        z.val.val=point hn ht ha hR outer ctx w hv :=by
  constructor
  · rintro ⟨hl,hF,hM⟩
    obtain ⟨hv,hr⟩:=(IntegralMixedPhysicalMarkedSemantics.leaves_iff hn ht ha hR outer ctx w).mp hl
    obtain ⟨EF,EM⟩:=IntegralMixedPhysicalMarkedSemantics.equations hn ht ha hR outer ctx w hv hr
    have HF:=sign_eq_zero_iff.mp ((SquareSampleTestSign.encode_eq_iff _ _).mp (EF.symm.trans hF))
    have HM:=sign_eq_zero_iff.mp ((SquareSampleTestSign.encode_eq_iff _ _).mp (EM.symm.trans hM))
    exact ⟨hv,hr,⟨⟨⟨point hn ht ha hR outer ctx w hv,HF⟩,HM⟩,rfl⟩⟩
  · rintro ⟨hv,hr,z,hz⟩
    obtain ⟨EF,EM⟩:=IntegralMixedPhysicalMarkedSemantics.equations hn ht ha hR outer ctx w hv hr
    have HF : (polynomial ((t (original ctx)).finitePolynomial (number n ctx)) (charge t ctx) (charge t ctx) (R ctx)).eval₂
        (Int.castRingHom ℝ) (point hn ht ha hR outer ctx w hv)=0 :=by rw [←hz]; exact z.val.property
    have HM : (markPolynomial ((t (original ctx)).finitePolynomial (number n ctx)) (R ctx)).eval₂
        (Int.castRingHom ℝ) (point hn ht ha hR outer ctx w hv)=0 :=by rw [←hz]; exact z.property
    exact ⟨(IntegralMixedPhysicalMarkedSemantics.leaves_iff hn ht ha hR outer ctx w).mpr ⟨hv,hr⟩,
      EF.trans (congrArg InfinitesimalSign.encode (sign_eq_zero_iff.mpr HF)),
      EM.trans (congrArg InfinitesimalSign.encode (sign_eq_zero_iff.mpr HM))⟩

theorem mem_PSPACE (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha hR outer))) :
    language hn ht ha hR outer∈PSPACE :=(IntegralMixedPhysicalMarkedTest.decider hn ht ha hR outer ER).mem_PSPACE

theorem outer_cutoffs (ctx w : List Bool) (h : pair ctx w∈language hn ht ha hR true) :
    ∃hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR true) (sampleContext ctx) w,
      env hn ht ha hR true ctx w hv (number n ctx+8)=
        (2:ℝ)^(IntegralMixedAuxiliaryOuterIntegerSource.exponent n t R ctx) ∧
      env hn ht ha hR true ctx w hv (number n ctx+9)=
        -(2:ℝ)^(IntegralMixedAuxiliaryOuterIntegerSource.exponent n t R ctx) :=by
  obtain ⟨hv,hr,_⟩:=(accepted_iff hn ht ha hR true ctx w).mp h
  exact ⟨hv,IntegralFramedPhysicalLeafSources.positive_cutoff hn ht ha R ctx (env hn ht ha hR true ctx w hv) hr,
    IntegralFramedPhysicalLeafSources.negative_cutoff hn ht ha R ctx (env hn ht ha hR true ctx w hv) hr⟩
end LeanCanny.Encoding.IntegralMixedPhysicalMarkedValidity
