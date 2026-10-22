/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedMetadataTable
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer

/-! # Decoding a metadata cell into its tree node

The cell word starts with its degree/direction bit, then one zero per node
height, then a one and the node index. The decoder is FP on arbitrary words;
every genuine cell recovers exactly its original node address.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedMetadataAddress
open LeanCanny.Encoding Turing.MultiTapeTM

def zeroPrefix : List Bool → List Bool
  | false :: t => true :: zeroPrefix t
  | _ => []

private def prefixT : Transducer Bool Bool where
  q₀ := false
  step seen b := (seen || b, if seen || b then [] else [true])
  final _ := []
  length_step_le seen b := by cases seen <;> cases b <;> decide
  length_final_le _ := by simp

private theorem prefixT_done (w : List Bool) : prefixT.run true w = [] := by
  induction w with
  | nil => rfl
  | cons b t ih =>
    rw [Transducer.run_cons]
    change [] ++ prefixT.run true t = []
    exact ih

private theorem prefixT_run (w : List Bool) : prefixT.run false w = zeroPrefix w := by
  induction w with
  | nil => rfl
  | cons b t ih =>
    rw [Transducer.run_cons]
    cases b with
    | false =>
      change [true] ++ prefixT.run false t = true :: zeroPrefix t
      rw [ih]
      rfl
    | true =>
      change [] ++ prefixT.run true t = []
      exact prefixT_done t

theorem zeroPrefix_FP : zeroPrefix ∈ FP := by
  refine ComputableTidilyInPolyTime.of_linear ⟨8, ?_⟩
  exact (prefixT.computableTidilyInTimeAndSpace fun w => (prefixT_run w).symm).mono
    (fun w => by simp only [encBits_apply]; omega) (fun _ => Nat.zero_le _)

def keyWord (w : List Bool) : List Bool := w.drop 1
def heightWord (w : List Bool) : List Bool := zeroPrefix (keyWord w)
def indexWord (w : List Bool) : List Bool := (keyWord w).drop ((heightWord w).length + 1)

def query (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (heightWord (pairSnd p)) (indexWord (pairSnd p)))

theorem heightWord_FP : heightWord ∈ FP :=
  mem_FP_comp (drop_mem_FP id_mem_FP (UnaryFn.const 1)) zeroPrefix_FP

theorem indexWord_FP : indexWord ∈ FP :=
  drop_mem_FP (drop_mem_FP id_mem_FP (UnaryFn.const 1)) ((UnaryFn.length heightWord_FP).add (UnaryFn.const 1))

theorem query_FP : query ∈ FP := by
  have hh := mem_FP_comp pairSnd_mem_FP heightWord_FP
  have hi := mem_FP_comp pairSnd_mem_FP indexWord_FP
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_pair hh hi)
  exact mem_FP_of_eq h (fun p => by simp only [Function.comp_apply, query])

theorem zeroPrefix_padding (h : ℕ) (t : List Bool) :
    zeroPrefix (List.replicate h false ++ true :: t) = List.replicate h true := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [List.replicate_succ, List.cons_append, zeroPrefix, ih]

theorem key_bits (h i : ℕ) :
    (BalancedMetadataTable.key h i).bits = List.replicate h false ++ true :: i.bits := by
  induction h with
  | zero => simp only [BalancedMetadataTable.key_zero, Nat.bit1_bits, List.replicate_zero, List.nil_append]
  | succ h ih =>
    have hn : BalancedMetadataTable.key h i ≠ 0 := by unfold BalancedMetadataTable.key; positivity
    rw [BalancedMetadataTable.key_succ, Nat.bit0_bits _ hn, ih]
    simp only [List.replicate_succ, List.cons_append]

theorem cell_bits (which : Bool) (h i : ℕ) :
    (2 * BalancedMetadataTable.key h i + if which then 1 else 0).bits =
      which :: (List.replicate h false ++ true :: i.bits) := by
  have hn : BalancedMetadataTable.key h i ≠ 0 := by unfold BalancedMetadataTable.key; positivity
  cases which <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero,
    Nat.bit0_bits _ hn, Nat.bit1_bits, key_bits]

theorem heightWord_cell (which : Bool) (h i : ℕ) :
    heightWord (BinaryNatCode.encode (2 * BalancedMetadataTable.key h i + if which then 1 else 0)) = List.replicate h true := by
  simp only [heightWord, keyWord, BinaryNatCode.encode, cell_bits, List.drop_succ_cons, List.drop_zero, zeroPrefix_padding]

theorem indexWord_cell (which : Bool) (h i : ℕ) :
    indexWord (BinaryNatCode.encode (2 * BalancedMetadataTable.key h i + if which then 1 else 0)) = BinaryNatCode.encode i := by
  unfold indexWord
  rw [heightWord_cell]
  simp only [List.length_replicate, keyWord, BinaryNatCode.encode, cell_bits,
    List.drop_succ_cons, List.drop_zero]
  simp [List.drop_append, List.drop_replicate]

theorem query_cell (which : Bool) (c : List Bool) (h i : ℕ) :
    query (pair c (BinaryNatCode.encode (2 * BalancedMetadataTable.key h i + if which then 1 else 0))) =
      BalancedParameterContext.packet c h i := by
  simp only [query, pairFst_pair, pairSnd_pair, heightWord_cell, indexWord_cell, BalancedParameterContext.packet]

end LeanCanny.Algebra.BalancedMetadataAddress
