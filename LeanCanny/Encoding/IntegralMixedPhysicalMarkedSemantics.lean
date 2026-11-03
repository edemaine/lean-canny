/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedTest
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedParameters
/-! # Exact marked-source equations on one full physical tuple -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalMarkedSemantics
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank tables represents leafSource leafCount originalSource)
open IntegralMixedPhysicalMarkedTest (input sampleContext regularValue markValue)
open IntegralMixedMarkedPointTest (charge markWord regularWord)
open IntegralMixedAuxiliaryMarkedIntegerSource (number original)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
local notation "B"=>bank hn ht ha hR outer
local notation "T"=>tables hn ht ha hR outer
local notation "rep"=>represents hn ht ha hR outer

noncomputable def env (ctx w : List Bool) (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w) : ℕ→ℝ :=
  IntegralFramedPhysicalBankTerm.env B T rep (sampleContext ctx) w hv
noncomputable def point (ctx w : List Bool) (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w) :
    Fin (number n ctx+4)→ℝ :=fun i=>env hn ht ha hR outer ctx w hv i.val

attribute [local irreducible] bank tables

private theorem holds_iff (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w) :
    IntegralFramedPhysicalIntegerLeaves.holds (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive
      (leafSource hn ht ha (R:=R) outer) (leafCount n outer) (pair (sampleContext ctx) w) ↔
    ∀i<number n ctx+(if outer then 10 else 8),((originalSource hn ht ha (R:=R) outer).polynomial
      (pair ctx (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (env hn ht ha hR outer ctx w hv i)=0 :=by
  rw [IntegralFramedPhysicalIntegerLeaves.holds_iff _ _ _ _ _ _ _ _ _ _ _ _ _ hv]
  have HC:=IntegralMixedPhysicalMarkedPlan.count_bound hn ht ha hR outer ctx
  simp only [leafCount,sampleContext,pairFst_pair] at HC ⊢
  constructor <;> intro HH i hi
  · have HE:=HH i hi
    have HX : env hn ht ha hR outer ctx w hv i=
        IntegralFramedPhysicalSquare.point (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
          (B).key (B).positive (pair ctx []) w hv
          (IntegralFramedPhysicalIntegerLeaves.coordinate (B).parameters (B).plan (B).data (B).key (B).positive (pair ctx []) (BinaryNatCode.encode i)) :=by
      simpa only [env,sampleContext] using
        IntegralFramedPhysicalBankTerm.env_coordinate B T rep (sampleContext ctx) w hv i (hi.trans_le HC)
    have HP:=IntegralMixedPhysicalMarkedPlan.source_packet hn ht ha (R:=R) outer ctx i
    have EP:=congrArg (fun p : Polynomial ℤ=>p.eval₂ (Int.castRingHom ℝ)
      (IntegralFramedPhysicalSquare.point (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (B).key (B).positive (pair ctx []) w hv
        (IntegralFramedPhysicalIntegerLeaves.coordinate (B).parameters (B).plan (B).data (B).key (B).positive (pair ctx []) (BinaryNatCode.encode i)))) HP
    exact (congrArg (fun v : ℝ=>((originalSource hn ht ha (R:=R) outer).polynomial
      (pair ctx (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) v) HX).trans (EP.symm.trans HE)
  · have HE:=HH i hi
    have HX : env hn ht ha hR outer ctx w hv i=
        IntegralFramedPhysicalSquare.point (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
          (B).key (B).positive (pair ctx []) w hv
          (IntegralFramedPhysicalIntegerLeaves.coordinate (B).parameters (B).plan (B).data (B).key (B).positive (pair ctx []) (BinaryNatCode.encode i)) :=by
      simpa only [env,sampleContext] using
        IntegralFramedPhysicalBankTerm.env_coordinate B T rep (sampleContext ctx) w hv i (hi.trans_le HC)
    have HP:=IntegralMixedPhysicalMarkedPlan.source_packet hn ht ha (R:=R) outer ctx i
    have EP:=congrArg (fun p : Polynomial ℤ=>p.eval₂ (Int.castRingHom ℝ)
      (IntegralFramedPhysicalSquare.point (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (B).key (B).positive (pair ctx []) w hv
        (IntegralFramedPhysicalIntegerLeaves.coordinate (B).parameters (B).plan (B).data (B).key (B).positive (pair ctx []) (BinaryNatCode.encode i)))) HP
    exact EP.trans ((congrArg (fun v : ℝ=>((originalSource hn ht ha (R:=R) outer).polynomial
      (pair ctx (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) v) HX).symm.trans HE)

theorem leaves_iff (ctx w : List Bool) : pair ctx w∈IntegralMixedPhysicalMarkedTest.leaves hn ht ha hR outer ↔
    ∃hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w,
      ∀i<number n ctx+(if outer then 10 else 8),((originalSource hn ht ha (R:=R) outer).polynomial
        (pair ctx (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (env hn ht ha hR outer ctx w hv i)=0 :=by
  simp only [IntegralMixedPhysicalMarkedTest.leaves,IntegralMixedPhysicalMarkedTest.leafQuery,
    Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,IntegralFramedPhysicalIntegerLeaves.language]
  constructor
  · rintro ⟨hv,_,HH⟩
    exact ⟨hv,(holds_iff hn ht ha hR outer ctx w hv).mp HH⟩
  · rintro ⟨hv,HH⟩
    exact ⟨hv,IntegralMixedPhysicalMarkedPlan.count_bound hn ht ha hR outer ctx,
      (holds_iff hn ht ha hR outer ctx w hv).mpr HH⟩

private theorem mark_syntax (ctx : List Bool) :
    (IntegralMixedFramedBankTermBits.source (markWord n t)).syntax ((B).key (sampleContext ctx))=
      BoundedMarkedParameterTerm.mark (t (original ctx)) (number n ctx) :=by
  change TermView.term (markWord n t (pairFst ((B).key (sampleContext ctx))))=_
  have HK : pairFst ((B).key (sampleContext ctx))=ctx :=by
    simpa only [sampleContext] using IntegralMixedPhysicalMarkedPlan.key_root hn ht ha hR outer ctx
  exact (congrArg (fun r=>TermView.term (markWord n t r)) HK).trans (TermView.term_toBits _)
private theorem regular_syntax (ctx : List Bool) :
    (IntegralMixedFramedBankTermBits.source (regularWord n t)).syntax ((B).key (sampleContext ctx))=
      BoundedMarkedParameterTerm.regular (t (original ctx)) (number n ctx) (IntegralMixedMarkedPointTest.degree t ctx) :=by
  change TermView.term (regularWord n t (pairFst ((B).key (sampleContext ctx))))=_
  have HK : pairFst ((B).key (sampleContext ctx))=ctx :=by
    simpa only [sampleContext] using IntegralMixedPhysicalMarkedPlan.key_root hn ht ha hR outer ctx
  exact (congrArg (fun r=>TermView.term (regularWord n t r)) HK).trans (TermView.term_toBits _)

theorem mark_packet (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w) :
    markValue hn ht ha hR outer (pair ctx w)=InfinitesimalSign.encode
      (SignType.sign ((BoundedMarkedParameterTerm.mark (t (original ctx)) (number n ctx)).eval (env hn ht ha hR outer ctx w hv))) :=by
  have H:=IntegralFramedPhysicalBankTerm.packet B T rep (sampleContext ctx) w hv (markWord n t) []
  rw [mark_syntax hn ht ha hR outer ctx] at H
  simpa only [markValue,Function.comp_apply,IntegralMixedPhysicalMarkedTest.probe,IntegralMixedPhysicalMarkedTest.leafQuery,
    pairFst_pair,pairSnd_pair,env] using H

theorem regular_packet (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w) :
    regularValue hn ht ha hR outer (pair ctx w)=InfinitesimalSign.encode
      (SignType.sign ((BoundedMarkedParameterTerm.regular (t (original ctx)) (number n ctx)
        (IntegralMixedMarkedPointTest.degree t ctx)).eval (env hn ht ha hR outer ctx w hv))) :=by
  have H:=IntegralFramedPhysicalBankTerm.packet B T rep (sampleContext ctx) w hv (regularWord n t) []
  rw [regular_syntax hn ht ha hR outer ctx] at H
  simpa only [regularValue,Function.comp_apply,IntegralMixedPhysicalMarkedTest.probe,IntegralMixedPhysicalMarkedTest.leafQuery,
    pairFst_pair,pairSnd_pair,env] using H

theorem equations (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w)
    (hr : ∀i<number n ctx+(if outer then 10 else 8),((originalSource hn ht ha (R:=R) outer).polynomial
      (pair ctx (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (env hn ht ha hR outer ctx w hv i)=0) :
    regularValue hn ht ha hR outer (pair ctx w)=InfinitesimalSign.encode (SignType.sign
      ((LeanCanny.Geometry.BoundedRegularSource.polynomial ((t (original ctx)).finitePolynomial (number n ctx))
        (charge t ctx) (charge t ctx) (R ctx)).eval₂ (Int.castRingHom ℝ) (point hn ht ha hR outer ctx w hv))) ∧
    markValue hn ht ha hR outer (pair ctx w)=InfinitesimalSign.encode (SignType.sign
      ((LeanCanny.Geometry.BoundedRegularSource.markPolynomial ((t (original ctx)).finitePolynomial (number n ctx))
        (R ctx)).eval₂ (Int.castRingHom ℝ) (point hn ht ha hR outer ctx w hv))) :=by
  obtain ⟨hRad,hL,hB,hK⟩:=IntegralMixedPhysicalMarkedPlan.parameters hn ht ha R outer ctx (env hn ht ha hR outer ctx w hv) hr
  have HR:=LeanCanny.Geometry.BoundedMarkedParameterSemantics.regular_eval (t (original ctx)) (number n ctx)
    (charge t ctx) (R ctx) (ha (original ctx)) (env hn ht ha hR outer ctx w hv) hRad hL hB hK
  have HM:=LeanCanny.Geometry.BoundedMarkedParameterSemantics.mark_eval (t (original ctx)) (number n ctx)
    (R ctx) (ha (original ctx)) (env hn ht ha hR outer ctx w hv) hRad
  exact ⟨(regular_packet hn ht ha hR outer ctx w hv).trans (congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v)) HR),
    (mark_packet hn ht ha hR outer ctx w hv).trans (congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v)) HM)⟩
end LeanCanny.Encoding.IntegralMixedPhysicalMarkedSemantics
