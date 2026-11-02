/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryLimitCommand
/-! # Native chronological auxiliary records with the original input preserved -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryLimitRecords
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Choice and degree readers receive the original word and a unary frozen count. -/
noncomputable def entry (N M C D : List Bool → ℕ) (p : List Bool) :=
  IntegralMixedAuxiliaryLimitRecord.record (N (pairFst p)) (pairSnd p).length (M (pairFst p)) (C p) (D p)

noncomputable def table (N M C D : List Bool → ℕ) (q : List Bool) :=
  WordList.encode ((List.range (N q)).map (fun k => entry N M C D (pair q (List.replicate k true))))

/-- Replace the record field while retaining the original input and advice word. -/
noncomputable def prepare (N M C D : List Bool → ℕ) (q : List Bool) :=
  pair (pairFst q) (pair (table N M C D q) (pairSnd q))

theorem entry_FP {N M C D : List Bool → ℕ} (hN : UnaryFn N) (hM : BinaryFn M)
    (hC : BinaryFn C) (hD : BinaryFn D) : entry N M C D ∈ FP :=
  IntegralMixedAuxiliaryLimitRecord.record_FP (hN.comp pairFst_mem_FP) (BinaryFn.ofUnary UnaryFn.index)
    (hM.comp pairFst_mem_FP) hC hD

attribute [local irreducible] entry

theorem table_FP {N M C D : List Bool → ℕ} (hN : UnaryFn N) (hM : BinaryFn M)
    (hC : BinaryFn C) (hD : BinaryFn D) : table N M C D ∈ FP := by
  have H := flatMap_range_mem_FP (mem_FP_pair (entry_FP hN hM hC hD) (constFn_mem_FP []))
    (hN.replicate_mem_FP true)
  exact mem_FP_of_eq H (fun q => by
    simp only [table,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,List.length_replicate])

theorem prepare_FP {N M C D : List Bool → ℕ} (hN : UnaryFn N) (hM : BinaryFn M)
    (hC : BinaryFn C) (hD : BinaryFn D) : prepare N M C D ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair (table_FP hN hM hC hD) pairSnd_mem_FP)

theorem count_table (N M C D : List Bool → ℕ) (q : List Bool) :
    WordListRecords.count (table N M C D q) = N q := by
  rw [table,WordListRecords.count_encode,List.length_map,List.length_range]

theorem table_get (N M C D : List Bool → ℕ) (q : List Bool) (k : ℕ) (hk : k<N q) :
    WordList.get (table N M C D q) k =
      IntegralMixedAuxiliaryLimitRecord.record (N q) k (M q)
        (C (pair q (List.replicate k true))) (D (pair q (List.replicate k true))) := by
  rw [table,WordList.get_encode]
  simp only [List.getElem?_map,List.getElem?_range hk,Option.map_some,Option.getD_some,
    entry,pairFst_pair,pairSnd_pair,List.length_replicate]

theorem prepare_input (N M C D : List Bool → ℕ) (q : List Bool) :
    pairFst (prepare N M C D q)=pairFst q := pairFst_pair _ _

theorem prepare_records (N M C D : List Bool → ℕ) (q : List Bool) :
    pairFst (pairSnd (prepare N M C D q))=table N M C D q := by
  rw [prepare,pairSnd_pair,pairFst_pair]

theorem prepare_advice (N M C D : List Bool → ℕ) (q : List Bool) :
    pairSnd (pairSnd (prepare N M C D q))=pairSnd q := by
  rw [prepare,pairSnd_pair,pairSnd_pair]
end LeanCanny.Encoding.IntegralMixedAuxiliaryLimitRecords
