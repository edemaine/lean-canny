/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardProfile
public import LeanCanny.Encoding.SquareSampleCompleteSuffixPolynomialTest

/-! # Physical correlation tests retain one complete sampler context and word

The chronological creating birth lives only in the test datum. Coefficients
come from the actual retained denominator and original header programs.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalCriticalGuardTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedHeaderTablesBits (Tables)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedFramedPhysicalIndex.prefixArity IntegralMixedFramedPhysicalIndex.scalarColumn
  IntegralMixedFramedCriticalGuardBits.atKey IntegralMixedCommandHeaderBits.lookup
  UniformIntegralPowerSchedule.birth UniformIntegralPowerSchedule.physical

def canonical (z : List Bool) :=pair (pairFst z) (pairSnd z)
def coefficientContext (q : List Bool) :=canonical (RationalSubstitution.IntegerBits.context q)
theorem canonical_FP : canonical∈FP:=mem_FP_pair pairFst_mem_FP pairSnd_mem_FP
theorem coefficientContext_FP : coefficientContext∈FP:=
  mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP canonical_FP

def keyDatum (key : List Bool→List Bool) (z : List Bool) :=key (pairFst z)
theorem keyDatum_FP (key : List Bool→List Bool) (hk : key∈FP) : keyDatum key∈FP:=
  mem_FP_comp pairFst_mem_FP hk

variable (S : SquareSampleInput.Inputs)
variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (T : Tables) (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (key : List Bool→List Bool) (stage : List Bool→ℕ)
variable (hcount : ∀ c d,IntegralMixedFramedCriticalGuardBits.count P T (keyDatum key) (pair c d)=S.count c)

theorem polynomial_reindex (read k : List Bool→List Bool) (j : List Bool→ℕ) (q : List Bool) :
    IntegralMixedFramedCriticalGuardBits.polynomial P D H T (k∘read) (j∘read) q=
      IntegralMixedFramedCriticalGuardBits.polynomial P D H T k j (read q) := rfl

attribute [local irreducible] IntegralMixedFramedCriticalGuardBits.polynomial

noncomputable def source : SquareSampleCompleteSuffixPolynomialTest.Source S where
  arity c d:=IntegralMixedFramedCriticalGuardBits.count P T (keyDatum key) (pair c d)
  newer _ _:=0
  polynomial c d:=IntegralMixedFramedCriticalGuardBits.polynomial P D H T (keyDatum key) stage (pair c d)
  degree c d:=IntegralMixedFramedCriticalGuardBits.degree P (keyDatum key) stage (pair c d)
  mass c d:=IntegralMixedFramedCriticalGuardBits.mass P L F C (keyDatum key) (pair c d)
  dimension c d:=(Nat.zero_add _).trans (hcount c d)
  polynomial_degree c d:=IntegralMixedFramedCriticalGuardBits.polynomial_degree P D H T (keyDatum key) stage (pair c d)
  polynomial_mass c d:=IntegralMixedFramedCriticalGuardBits.polynomial_mass P D H T (keyDatum key) stage L F C hs (pair c d)

theorem access (a : Access P) (hT : IntegralMixedHeaderTablesBits.Access T)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (ctl : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hctl : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew ctl)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) (hk : key∈FP) (hj : UnaryFn stage) :
    (source S P D H T L F C hs key stage hcount).Access := by
  have HK:=keyDatum_FP key hk
  have HD:=IntegralMixedFramedCriticalGuardBits.degree_binary P a (keyDatum key) stage HK hj
  have HM:=IntegralMixedFramedCriticalGuardBits.mass_binary P a L F C (keyDatum key) hL hF hC HK
  refine ⟨UnaryFn.const 0,HD.comp canonical_FP,HM.comp canonical_FP,?_⟩
  let ctx:=coefficientContext
  let k:=keyDatum key∘ctx
  let j:=stage∘ctx
  let W:=fun q=>(IntegralMixedFramedCriticalGuardBits.degree P (keyDatum key) stage (ctx q)).size
  have HC : ctx∈FP:=coefficientContext_FP
  have HDC : BinaryFn (IntegralMixedFramedCriticalGuardBits.degree P (keyDatum key) stage∘ctx):=HD.comp HC
  have HW : UnaryFn W:=(UnaryFn.length HDC.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)
  have E:=IntegralMixedFramedCriticalGuardBits.coefficient_evaluator P a D H Hnew ctl hctl T hT k j W
    RationalSubstitution.IntegerBits.selectedDegree pairSnd (mem_FP_comp HC HK) (hj.comp HC) HW
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
  apply E.congr
  funext q
  unfold SquareSampleCompleteSuffixPolynomialTest.coefficient
    SquareSampleCompleteSuffixPolynomialTest.oldCoefficient
  unfold FixedWidthRowBits.value
  rw [polynomial_reindex P D H T ctx (keyDatum key) stage q]
  simp only [source,ctx,k]
  rfl

noncomputable def value : List Bool→List Bool :=
  SquareSampleCompleteIndexedPolynomialTest.value S (SquareSampleCompleteSuffixPolynomialTest.test
    (source S P D H T L F C hs key stage hcount))

theorem evaluator (hS : S.Access) (a : Access P) (hT : IntegralMixedHeaderTablesBits.Access T)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (ctl : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hctl : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew ctl)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) (hk : key∈FP) (hj : UnaryFn stage) :
    SpaceFunction (value S P D H T L F C hs key stage hcount) :=
  SquareSampleCompleteSuffixPolynomialTest.evaluator hS _ (access S P D H T L F C hs key stage hcount
    a hT Hnew ctl hctl hL hF hC hk hj)

theorem packet (c w d : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    value S P D H T L F C hs key stage hcount (pair (pair c w) d)=InfinitesimalSign.encode (SignType.sign
      (((source S P D H T L F C hs key stage hcount).polynomial c d).eval₂ (Int.castRingHom ℝ)
        (fun i=>(SquareSampleCompleteVertices.candidate S c w hv).val
          (Fin.cast ((source S P D H T L F C hs key stage hcount).dimension c d)
            (FixedWidthSuffixLiftBits.shift 0 i))))) :=
  SquareSampleCompleteSuffixPolynomialTest.packet _ c w d hv

end LeanCanny.Encoding.IntegralFramedPhysicalCriticalGuardTest
