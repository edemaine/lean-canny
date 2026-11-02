/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCanonicalUnitRules
public import LeanCanny.Encoding.WordListRecords
/-! # Original limit-cut records for one auxiliary-coordinate continuation

The original dimension is n; the once-augmented spatial source has ambient
n+2. Retained parameters are named by their original scalar birth labels.
Neither the physical eta coordinate nor the formal nilpotent coordinate is
allocated a producer label.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryLimitRecord
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def row (k m0 i : ℕ) : List Bool :=
  pair [decide (0 < i ∧ i < k+1)] (BinaryNatCode.encode (m0+i-1))

noncomputable def rows (n k m0 : ℕ) : List Bool :=
  WordList.encode ((List.range (n+3)).map (row k m0))

noncomputable def record (n k m0 c d : ℕ) : List Bool :=
  WordList.encode [[],[],BinaryNatCode.encode k,BinaryNatCode.encode (n+1-k),[],[],[],
    rows n k m0,BinaryNatCode.encode c,BinaryNatCode.encode d]

theorem rows_get (n k m0 i : ℕ) (hi : i<n+3) :
    WordList.get (rows n k m0) i=row k m0 i := by
  rw [rows,WordList.get_encode]
  simp only [List.getElem?_map,List.getElem?_range hi,Option.map_some,Option.getD_some]

theorem record_field (n k m0 c d i : ℕ) :
    IntegralMixedUnitRecordCode.field (record n k m0 c d) i =
      ([[],[],BinaryNatCode.encode k,BinaryNatCode.encode (n+1-k),[],[],[],
        rows n k m0,BinaryNatCode.encode c,BinaryNatCode.encode d][i]?).getD [] :=
  WordList.get_encode _ _

attribute [local irreducible] rows row record

theorem rows_FP {N K M : List Bool → ℕ} (hN : UnaryFn N) (hK : BinaryFn K) (hM : BinaryFn M) :
    (fun q => rows (N q) (K q) (M q)) ∈ FP := by
  have HK : BinaryFn (fun p => K (pairFst p)) := hK.comp pairFst_mem_FP
  have HM : BinaryFn (fun p => M (pairFst p)) := hM.comp pairFst_mem_FP
  have HI : BinaryFn (fun p : List Bool => (pairSnd p).length) := BinaryFn.ofUnary UnaryFn.index
  have HF := ((BinaryFn.const 0).lt HI).and (HI.lt (HK.add (BinaryFn.const 1)))
  have HR := mem_FP_pair HF.flag_mem_FP ((HM.add HI).sub (BinaryFn.const 1)).bits_mem_FP
  have HE := mem_FP_pair HR (constFn_mem_FP [])
  have H := flatMap_range_mem_FP HE ((hN.add (UnaryFn.const 3)).replicate_mem_FP true)
  exact mem_FP_of_eq H (fun q => by
    simp only [rows, FrozenCoordinatePermutationBits.encode_flatMap, List.flatMap_map,
      row, pairFst_pair, pairSnd_pair, List.length_replicate])

theorem record_FP {N K M C D : List Bool → ℕ} (hN : UnaryFn N) (hK : BinaryFn K)
    (hM : BinaryFn M) (hC : BinaryFn C) (hD : BinaryFn D) :
    (fun q => record (N q) (K q) (M q) (C q) (D q)) ∈ FP := by
  have H0 := constFn_mem_FP ([] : List Bool)
  have HO := ((BinaryFn.ofUnary hN).add (BinaryFn.const 1)).sub hK
  have H := mem_FP_pair H0 (mem_FP_pair H0 (mem_FP_pair hK.bits_mem_FP (mem_FP_pair HO.bits_mem_FP
    (mem_FP_pair H0 (mem_FP_pair H0 (mem_FP_pair H0 (mem_FP_pair (rows_FP hN hK hM)
      (mem_FP_pair hC.bits_mem_FP (mem_FP_pair hD.bits_mem_FP H0)))))))))
  exact mem_FP_of_eq H (fun q => by simp only [record,WordList.encode])
end LeanCanny.Encoding.IntegralMixedAuxiliaryLimitRecord
