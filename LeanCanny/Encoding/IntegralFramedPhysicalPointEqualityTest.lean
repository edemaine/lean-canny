/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPointEquality
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalGuardTest
/-! # Two creating powers are compared on one unchanged full vertex -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalPointEqualityTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHeaderTablesBits (Tables)
open IntegralFramedPhysicalCriticalGuardTest (keyDatum canonical coefficientContext)
open IntegralMixedFramedPointEqualityBits (polynomial degree point Admissible)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] polynomial
  IntegralMixedFramedPhysicalIndex.prefixArity UniformIntegralPowerSchedule.physical
variable (S : SquareSampleInput.Inputs) (P : Parameters) (T : Tables)
  (key : List Bool→List Bool) (left right coordinate : List Bool→ℕ)
  (hcount : ∀ c d,IntegralMixedFramedCriticalGuardBits.count P T (keyDatum key) (pair c d)=S.count c)

theorem polynomial_reindex (read k : List Bool→List Bool) (l r i : List Bool→ℕ) (q : List Bool) :
    polynomial P T (k∘read) (l∘read) (r∘read) (i∘read) q=polynomial P T k l r i (read q) :=by
  unfold polynomial
  rfl

noncomputable def source : SquareSampleCompleteSuffixPolynomialTest.Source S where
  arity c d:=IntegralMixedFramedCriticalGuardBits.count P T (keyDatum key) (pair c d)
  newer _ _:=0
  polynomial c d:=polynomial P T (keyDatum key) left right coordinate (pair c d)
  degree c d:=degree P (keyDatum key) left right (pair c d)
  mass _ _:=1
  dimension c d:=(Nat.zero_add _).trans (hcount c d)
  polynomial_degree c d:=IntegralMixedFramedPointEqualityBits.polynomial_degree P T (keyDatum key) left right coordinate (pair c d)
  polynomial_mass c d:=IntegralMixedFramedPointEqualityBits.polynomial_mass P T (keyDatum key) left right coordinate (pair c d)

theorem access (a : Access P) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hk : key∈FP) (hl : UnaryFn left) (hr : UnaryFn right) (hi : BinaryFn coordinate) :
    (source S P T key left right coordinate hcount).Access :=by
  have HK:=IntegralFramedPhysicalCriticalGuardTest.keyDatum_FP key hk
  have HD:=IntegralMixedFramedPointEqualityBits.degree_binary P (keyDatum key) left right a HK hl hr
  refine ⟨UnaryFn.const 0,HD.comp IntegralFramedPhysicalCriticalGuardTest.canonical_FP,BinaryFn.const 1,?_⟩
  let ctx:=coefficientContext
  let k:=keyDatum key∘ctx
  let l:=left∘ctx
  let r:=right∘ctx
  let i:=coordinate∘ctx
  let W:=fun q=>(degree P (keyDatum key) left right (ctx q)).size
  have HC : ctx∈FP:=IntegralFramedPhysicalCriticalGuardTest.coefficientContext_FP
  have HDC : BinaryFn (degree P (keyDatum key) left right∘ctx):=HD.comp HC
  have HW : UnaryFn W:=(UnaryFn.length HDC.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)
  have E:=IntegralMixedFramedPointEqualityBits.coefficient_evaluator P T k l r i a hT W
    RationalSubstitution.IntegerBits.selectedDegree pairSnd (mem_FP_comp HC HK)
    (hl.comp HC) (hr.comp HC) (hi.comp HC) HW RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
  apply E.congr
  funext q
  unfold SquareSampleCompleteSuffixPolynomialTest.coefficient SquareSampleCompleteSuffixPolynomialTest.oldCoefficient
  unfold FixedWidthRowBits.value
  rw [polynomial_reindex P T ctx (keyDatum key) left right coordinate q]
  simp only [source,ctx,k]
  rfl

noncomputable def value :=SquareSampleCompleteIndexedPolynomialTest.value S
  (SquareSampleCompleteSuffixPolynomialTest.test (source S P T key left right coordinate hcount))
theorem evaluator (hS : S.Access) (a : Access P) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hk : key∈FP) (hl : UnaryFn left) (hr : UnaryFn right) (hi : BinaryFn coordinate) :
    SpaceFunction (value S P T key left right coordinate hcount) :=
  SquareSampleCompleteSuffixPolynomialTest.evaluator hS _
    (access S P T key left right coordinate hcount a hT hk hl hr hi)

noncomputable def tuple (c w d : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    Fin (IntegralMixedFramedCriticalGuardBits.count P T (keyDatum key) (pair c d))→ℝ :=
  fun j=>(SquareSampleCompleteVertices.candidate S c w hv).val (Fin.cast (hcount c d) j)

theorem packet (c w d : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    value S P T key left right coordinate hcount (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign ((polynomial P T (keyDatum key) left right coordinate (pair c d)).eval₂
        (Int.castRingHom ℝ) (tuple S P T key hcount c w d hv))) :=by
  have HC (i : Fin (IntegralMixedFramedCriticalGuardBits.count P T (keyDatum key) (pair c d))) :
      Fin.cast ((source S P T key left right coordinate hcount).dimension c d)
        (FixedWidthSuffixLiftBits.shift 0 i)=Fin.cast (hcount c d) i :=by
    apply Fin.ext
    change 0+i.val=i.val
    omega
  have HE:=SquareSampleCompleteSuffixPolynomialTest.packet (source S P T key left right coordinate hcount) c w d hv
  have HT : (fun i : Fin (IntegralMixedFramedCriticalGuardBits.count P T (keyDatum key) (pair c d))=>
      (SquareSampleCompleteVertices.candidate S c w hv).val
        (Fin.cast ((source S P T key left right coordinate hcount).dimension c d)
          (FixedWidthSuffixLiftBits.shift 0 i)))=tuple S P T key hcount c w d hv :=by
    funext i
    exact congrArg (SquareSampleCompleteVertices.candidate S c w hv).val (HC i)
  change value S P T key left right coordinate hcount (pair (pair c w) d)=InfinitesimalSign.encode
    (SignType.sign ((polynomial P T (keyDatum key) left right coordinate (pair c d)).eval₂ (Int.castRingHom ℝ)
      (fun i : Fin (IntegralMixedFramedCriticalGuardBits.count P T (keyDatum key) (pair c d))=>
        (SquareSampleCompleteVertices.candidate S c w hv).val
          (Fin.cast ((source S P T key left right coordinate hcount).dimension c d)
            (FixedWidthSuffixLiftBits.shift 0 i))))) at HE
  rw [HT] at HE
  exact HE

theorem zero_iff (c w d : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w)
    (h : Admissible P T (keyDatum key) left right coordinate (pair c d)) :
    value S P T key left right coordinate hcount (pair (pair c w) d)=InfinitesimalSign.encode 0 ↔
      point P T (keyDatum key) left (pair c d) h.1 (tuple S P T key hcount c w d hv) ⟨coordinate (pair c d),h.2.2⟩=
      point P T (keyDatum key) right (pair c d) h.2.1 (tuple S P T key hcount c w d hv) ⟨coordinate (pair c d),h.2.2⟩ :=by
  rw [packet S P T key left right coordinate hcount c w d hv,
    SquareSampleTestSign.encode_eq_iff,sign_eq_zero_iff,
    IntegralMixedFramedPointEqualityBits.polynomial_eval P T (keyDatum key) left right coordinate (pair c d) h,sub_eq_zero]

end LeanCanny.Encoding.IntegralFramedPhysicalPointEqualityTest
