/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
public import LeanCanny.Encoding.IntegralMixedCausalRecordTables
/-! # Native original tables for an integer prelude and absolute-birth records

Only original codes and unary births are serialized. All integer headers,
bodies and slope modes are fixed; their polynomial coefficients stay in the
charged source. No current denominator appears in any table.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def code (N : List Bool→ℕ) (z : List Bool) :=
  IntegralMixedCausalRecordPlanBits.code (pairFst z) ((pairSnd z).length-N (pairFst z))

theorem code_FP {N : List Bool→ℕ} (hN : UnaryFn N) : code N∈FP := by
  have HI := UnaryFn.index.sub (hN.comp pairFst_mem_FP)
  have H:=mem_FP_comp (mem_FP_pair pairFst_mem_FP (HI.replicate_mem_FP true)) IntegralMixedCausalRecordPlanBits.reader_FP
  exact mem_FP_of_eq H (fun z=>by simp only [Function.comp_apply,IntegralMixedCausalRecordPlanBits.reader,
    pairFst_pair,pairSnd_pair,List.length_replicate,code])

def headerEntry (P : Parameters) (N : List Bool→ℕ) (z : List Bool) :=
  pair (if (pairSnd z).length<N (pairFst z) then IntegralMixedCommandHeaderBits.encode IntegralMixedCommandHeaderBits.zero else
    IntegralMixedCommandHeaderBits.encode (IntegralMixedCausalUnitHeaderBits.header (P.ambient (pairFst z))
      (P.degree (pairFst z)) (code N z))) []
noncomputable def modeEntry (P : Parameters) (N : List Bool→ℕ) (z : List Bool) :=
  pair (if (pairSnd z).length<N (pairFst z) then pair [false] (BinaryNatCode.encode 0) else
    IntegralMixedCausalRecordPlanBits.mode (P.ambient (pairFst z)) (code N z)) []
noncomputable def bodyEntry (P : Parameters) (N : List Bool→ℕ) (z : List Bool) :=
  pair (if (pairSnd z).length<N (pairFst z) then [] else
    IntegralMixedCausalUnitBodyBits.body (P.ambient (pairFst z)) (pairSnd z).length (code N z)) []

noncomputable def headerTable (P : Parameters) (N : List Bool→ℕ) (root : List Bool) :=
  WordList.encode ((List.range (N root+IntegralMixedCausalRecordPlanBits.count root)).map fun b=>
    pairFst (headerEntry P N (pair root (List.replicate b true))))
noncomputable def modeTable (P : Parameters) (N : List Bool→ℕ) (root : List Bool) :=
  WordList.encode ((List.range (N root+IntegralMixedCausalRecordPlanBits.count root)).map fun b=>
    pairFst (modeEntry P N (pair root (List.replicate b true))))
noncomputable def bodyTable (P : Parameters) (N : List Bool→ℕ) (root : List Bool) :=
  WordList.encode ((List.range (N root+IntegralMixedCausalRecordPlanBits.count root)).map fun b=>
    pairFst (bodyEntry P N (pair root (List.replicate b true))))

attribute [local irreducible] IntegralMixedCausalUnitHeaderBits.header IntegralMixedCausalUnitBodyBits.body IntegralMixedCausalRecordPlanBits.mode

theorem headerEntry_FP (P : Parameters) (a : Access P) {N : List Bool→ℕ} (hN : UnaryFn N) : headerEntry P N∈FP := by
  have HB := (BinaryFn.ofUnary UnaryFn.index).lt (BinaryFn.ofUnary (hN.comp pairFst_mem_FP))
  exact mem_FP_pair (HB.ite_mem_FP (constFn_mem_FP _) (IntegralMixedCausalUnitHeaderBits.header_FP
    (a.ambient.comp pairFst_mem_FP) (a.degree.comp pairFst_mem_FP) (code_FP hN))) (constFn_mem_FP [])

theorem modeEntry_FP (P : Parameters) (a : Access P) {N : List Bool→ℕ} (hN : UnaryFn N) : modeEntry P N∈FP := by
  have HB := (BinaryFn.ofUnary UnaryFn.index).lt (BinaryFn.ofUnary (hN.comp pairFst_mem_FP))
  exact mem_FP_pair (HB.ite_mem_FP (constFn_mem_FP _) (IntegralMixedCausalRecordPlanBits.mode_FP
    (a.ambient.comp pairFst_mem_FP) (code_FP hN))) (constFn_mem_FP [])

theorem bodyEntry_FP (P : Parameters) (a : Access P) {N : List Bool→ℕ} (hN : UnaryFn N) : bodyEntry P N∈FP := by
  have HB := (BinaryFn.ofUnary UnaryFn.index).lt (BinaryFn.ofUnary (hN.comp pairFst_mem_FP))
  have HP:=mem_FP_pair (code_FP hN) (mem_FP_pair
    (UnaryFn.index.replicate_mem_FP true) ((a.ambient.comp pairFst_mem_FP).replicate_mem_FP true))
  have HW:=mem_FP_comp HP IntegralMixedCausalUnitBodyBits.writer_FP
  have HE : (fun z=>IntegralMixedCausalUnitBodyBits.body (P.ambient (pairFst z)) (pairSnd z).length (code N z))∈FP :=
    mem_FP_of_eq HW (fun z=>by simp only [Function.comp_apply,IntegralMixedCausalUnitBodyBits.writer,
      pairFst_pair,pairSnd_pair,List.length_replicate])
  exact mem_FP_pair (HB.ite_mem_FP (constFn_mem_FP []) HE) (constFn_mem_FP [])

theorem headerTable_FP (P : Parameters) (a : Access P) {N : List Bool→ℕ} (hN : UnaryFn N) : headerTable P N∈FP := by
  apply mem_FP_of_eq (flatMap_range_mem_FP (headerEntry_FP P a hN)
    ((hN.add IntegralMixedCausalRecordPlanBits.count_unary).replicate_mem_FP true))
  intro root
  simp only [headerTable,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    headerEntry,pairFst_pair,List.length_replicate]

theorem modeTable_FP (P : Parameters) (a : Access P) {N : List Bool→ℕ} (hN : UnaryFn N) : modeTable P N∈FP := by
  apply mem_FP_of_eq (flatMap_range_mem_FP (modeEntry_FP P a hN)
    ((hN.add IntegralMixedCausalRecordPlanBits.count_unary).replicate_mem_FP true))
  intro root
  simp only [modeTable,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    modeEntry,pairFst_pair,List.length_replicate]

theorem bodyTable_FP (P : Parameters) (a : Access P) {N : List Bool→ℕ} (hN : UnaryFn N) : bodyTable P N∈FP := by
  apply mem_FP_of_eq (flatMap_range_mem_FP (bodyEntry_FP P a hN)
    ((hN.add IntegralMixedCausalRecordPlanBits.count_unary).replicate_mem_FP true))
  intro root
  simp only [bodyTable,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    bodyEntry,pairFst_pair,List.length_replicate]

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
