/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceHeadMetadata
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalBranchSign
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullSemantics
public import LeanCanny.Algebra.CoefficientFinitePhysicalQuery
/-! # Literal historical head signs at the same full decoded tuple -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTraceHeadQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem coordinate (I : SquareSampleInput.Inputs) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid I c w) (k : ℕ) :
    SquareSampleCompleteCoordinateSign.value I (pair (pair c w) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign (CoefficientFinitePhysicalQuery.natural
        (SquareSampleCompleteVertices.candidate I c w hw).val (min k (I.count c-1)))) := by
  rw [SquareSampleCompleteCoordinateSign.value, SquareSampleCompleteUnivariateTest.packet]
  simp only [SquareSampleCompleteCoordinateSign.identitySource, pow_one, Polynomial.eval₂_X]
  let i := SquareSampleInput.selected I c (BinaryNatCode.encode k)
  have hi : i.val = min k (I.count c-1) := by
    simp only [i, SquareSampleInput.selected, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [← hi]
  apply congrArg (fun v : ℝ => InfinitesimalSign.encode (SignType.sign v))
  exact (show CoefficientFinitePhysicalQuery.natural
    (SquareSampleCompleteVertices.candidate I c w hw).val i.val =
    (SquareSampleCompleteVertices.candidate I c w hw).val i from dite_eq_left i.isLt).symm

private theorem natural_heq {N M : ℕ} (h : N = M) (z : Fin N → ℝ) (w : Fin M → ℝ) (he : HEq z w) :
    CoefficientFinitePhysicalQuery.natural z = CoefficientFinitePhysicalQuery.natural w := by
  cases h
  cases eq_of_heq he
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)

noncomputable def column (ctx : List Bool) (j : ℕ) := CoefficientMarkedRecordTraceHeadMetadata.column hn ht ha
  (IntegralFramedTraceCutScan.stagePacket (pair ctx []) j)

/-- The selected coordinate is clamped exactly as in the native reader,
including out-of-range stage requests. All original columns are derived. -/
theorem value (ctx w : List Bool) (j : ℕ)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w)
    (z : Fin (CoefficientMarkedRecordCriticalBranchSign.count hn ht ha ctx) → ℝ)
    (hz : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw).val z) :
    IntegralMixedPhysicalTraceCutGuards.head hn ht ha hR false
      (IntegralFramedTraceCutScan.stagePacket (pair ctx w) j) =
    InfinitesimalSign.encode (SignType.sign (CoefficientFinitePhysicalQuery.natural z
      (min (column hn ht ha ctx j) (CoefficientMarkedRecordCriticalBranchSign.count hn ht ha ctx-1)))) := by
  have hc := (CoefficientMarkedRecordCriticalFullSemantics.full_count hn ht ha hR ctx).symm
  have hnatur := natural_heq hc _ z hz
  have hcolumn := CoefficientMarkedRecordTraceHeadMetadata.column_eq hn ht ha hR
    (IntegralFramedTraceCutScan.stagePacket (pair ctx w) j)
  have hs : CoefficientMarkedRecordTraceHeadMetadata.column hn ht ha
      (IntegralFramedTraceCutScan.stagePacket (pair ctx w) j) = column hn ht ha ctx j := by
    simp only [column, CoefficientMarkedRecordTraceHeadMetadata.column, CoefficientMarkedRecordTraceHeadMetadata.age,
      IntegralFramedTraceCutGuards.root, IntegralFramedTraceCutGuards.stage,
      IntegralFramedTraceCutScan.stagePacket, pairFst_pair, pairSnd_pair]
  unfold IntegralMixedPhysicalTraceCutGuards.head IntegralMixedPhysicalTraceCutGuards.headQuery
  simp only [Function.comp_apply, IntegralMixedPhysicalTraceCutGuards.sample,
    IntegralFramedTraceCutGuards.root, IntegralFramedTraceCutGuards.word,
    IntegralFramedTraceCutScan.stagePacket, pairFst_pair, pairSnd_pair]
  simp only [IntegralFramedTraceCutScan.stagePacket, pairFst_pair, pairSnd_pair] at hcolumn hs
  rw [hcolumn, hs, coordinate _ _ _ hw, hnatur, hc]
  rfl

end LeanCanny.Encoding.CoefficientMarkedRecordTraceHeadQuery
