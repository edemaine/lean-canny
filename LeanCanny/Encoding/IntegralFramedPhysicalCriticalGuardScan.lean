/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalGuardTest
public import LeanCanny.Computation.SpaceFunctionQuantifiers
public import LeanCanny.Geometry.IntegralMixedFramedCriticalGuard

/-! # Native universal physical correlation on one complete vertex

Every creating birth is tested through the datum; sampler context and word
stay fixed. Inactive commands contribute the zero guard.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalCriticalGuardScan
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan prefixLength)
open IntegralMixedHeaderTablesBits (Tables)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open IntegralFramedPhysicalCriticalGuardTest (keyDatum)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedFramedCriticalGuardBits.polynomial
  LeanCanny.Geometry.IntegralMixedFramedCriticalGuard.actualPoint

def stage (z : List Bool) :=(pairSnd z).length
theorem stage_unary : UnaryFn stage:=UnaryFn.length pairSnd_mem_FP

variable (S : SquareSampleInput.Inputs)
variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (T : Tables) (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (key : List Bool→List Bool)
variable (hcount : ∀ c d,IntegralMixedFramedCriticalGuardBits.count P T (keyDatum key) (pair c d)=S.count c)

noncomputable def holds (q : List Bool) : Prop := ∀i<prefixLength P (key (pairFst q)),
  IntegralFramedPhysicalCriticalGuardTest.value S P D H T L F C hs key stage hcount
    (pair q (List.replicate i true))=InfinitesimalSign.encode 0

theorem holds_evaluator (hS : S.Access) (a : Access P) (hT : IntegralMixedHeaderTablesBits.Access T)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (ctl : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hctl : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew ctl)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) (hk : key∈FP) :
    SpaceFunction (fun q=>[decide (holds S P D H T L F C hs key hcount q)]) := by
  have E:=(IntegralFramedPhysicalCriticalGuardTest.evaluator S P D H T L F C hs key stage hcount
    hS a hT Hnew ctl hctl hL hF hC hk stage_unary).postcompose
    (fun z=>[decide (z=InfinitesimalSign.encode 0)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  have HN:=((IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp (mem_FP_comp pairFst_mem_FP hk))
  exact (E.forall_unary HN).congr (funext fun q=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [holds,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq])

noncomputable def language : Language := {q |
  SquareSampleCompleteVertices.Valid S (pairFst q) (pairSnd q) ∧holds S P D H T L F C hs key hcount q}

theorem decider (hS : S.Access) (a : Access P) (hT : IntegralMixedHeaderTablesBits.Access T)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (ctl : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hctl : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew ctl)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) (hk : key∈FP) :
    SpaceDecider (language S P D H T L F C hs key hcount) := by
  have E:=(SquareSampleCompleteVertices.decider hS).flagEvaluator
  have A:=holds_evaluator S P D H T L F C hs key hcount hS a hT Hnew ctl hctl hL hF hC hk
  apply (E.andFlags A).decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,
    List.cons.injEq,and_true,decide_eq_true_eq]

theorem holds_iff (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    holds S P D H T L F C hs key hcount (pair c w) ↔∀i<prefixLength P (key c),
      ((IntegralFramedPhysicalCriticalGuardTest.source S P D H T L F C hs key stage hcount).polynomial
        c (List.replicate i true)).eval₂ (Int.castRingHom ℝ)
        (fun j=>(SquareSampleCompleteVertices.candidate S c w hv).val
          (Fin.cast ((IntegralFramedPhysicalCriticalGuardTest.source S P D H T L F C hs key stage hcount).dimension
            c (List.replicate i true)) (FixedWidthSuffixLiftBits.shift 0 j)))=0 := by
  simp only [holds,pairFst_pair]
  simp_rw [IntegralFramedPhysicalCriticalGuardTest.packet S P D H T L F C hs key stage hcount c w _ hv,
    SquareSampleTestSign.encode_eq_iff,sign_eq_zero_iff]

noncomputable def point (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (d : List Bool) :
    Fin (IntegralMixedFramedCriticalGuardBits.count P T (keyDatum key) (pair c d))→ℝ :=
  fun j=>(SquareSampleCompleteVertices.candidate S c w hv).val
    (Fin.cast ((IntegralFramedPhysicalCriticalGuardTest.source S P D H T L F C hs key stage hcount).dimension c d)
      (FixedWidthSuffixLiftBits.shift 0 j))

theorem active_guard (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
    (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w)
    (hh : holds S P D H T L F C hs key hcount (pair c w)) (i : ℕ) (hi : i<prefixLength P (key c))
    (ha : IntegralMixedFramedCriticalGuardBits.Active P T (keyDatum key) stage (pair c (List.replicate i true))) :
    LeanCanny.Geometry.IntegralMixedFramedCriticalGuard.actualPoint P D H T hr (keyDatum key) stage
      (pair c (List.replicate i true)) ha (point S P D H T L F C hs key hcount c w hv (List.replicate i true))=
      (point S P D H T L F C hs key hcount c w hv (List.replicate i true))
        ⟨IntegralMixedFramedCriticalGuardBits.physical P T (keyDatum key) stage (pair c (List.replicate i true)),
          IntegralMixedFramedCriticalGuardBits.physical_lt P D H T hr (keyDatum key) stage
            (pair c (List.replicate i true)) ha⟩^
        IntegralMixedFramedCriticalGuardBits.physicalPower P (keyDatum key) stage (pair c (List.replicate i true)) := by
  have HZ:=(holds_iff S P D H T L F C hs key hcount c w hv).mp hh i hi
  exact (LeanCanny.Geometry.IntegralMixedFramedCriticalGuard.zero_iff_actualPoint P D H T hr
    (keyDatum key) stage (pair c (List.replicate i true)) ha _).mp HZ

end LeanCanny.Encoding.IntegralFramedPhysicalCriticalGuardScan
