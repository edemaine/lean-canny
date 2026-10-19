/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.MonomialCountData
public import LeanCanny.ETR.NNFFP
public import LeanCanny.Encoding.BinaryMulFP

/-!
# A certified binary monomial-count reader

Each tree-fold frame retains its raw children and their binary counts.
Addition and multiplication use the existing FP binary arithmetic. A linear
comparison with the raw frame bounds the entire encoded stack, including runs
on malformed bitstrings. No monomial list or unary count is constructed.
-/

@[expose] public section

namespace LeanCanny.ETR.MonomialCount
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets

def countsCode (xs : List Data) : List Bool := DynamicTreeFold.stackBits (fun d => BinaryNatCode.encode (countData d)) xs
def code (xs : List Data) : List Bool := pair (Data.l xs).toBits (countsCode xs)
def raw (frame : List Bool) : List Bool := pairFst frame
def counts (frame : List Bool) : List Bool := pairSnd frame
def secondCount (frame : List Bool) : List Bool := pairFst (pairSnd (counts frame))
def thirdCount (frame : List Bool) : List Bool := pairFst (pairSnd (pairSnd (counts frame)))

def finish (frame : List Bool) : List Bool :=
  if NNF.HasTwo 2 (raw frame) then BinaryNat.add (pair (secondCount frame) (thirdCount frame))
  else if NNF.HasTwo 3 (raw frame) then BinaryNat.mul (pair (secondCount frame) (thirdCount frame)) else [true]

theorem secondCount_mem_FP : secondCount ∈ FP :=
  mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem thirdCount_mem_FP : thirdCount ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairFst_mem_FP

theorem finish_mem_FP : finish ∈ FP := by
  have hargs := mem_FP_pair secondCount_mem_FP thirdCount_mem_FP
  have ha := mem_FP_comp hargs BinaryNat.add_mem_FP
  have hm := mem_FP_comp hargs BinaryNat.mul_mem_FP
  have h := ((NNF.hasTwo_fppred 2).comp pairFst_mem_FP).ite_mem_FP ha
    (((NNF.hasTwo_fppred 3).comp pairFst_mem_FP).ite_mem_FP hm (constFn_mem_FP [true]))
  refine mem_FP_of_eq (g := finish) h ?_
  intro frame
  simp only [finish, raw, Function.comp_apply]
  rfl

theorem finish_code (xs : List Data) : finish (code xs) = BinaryNatCode.encode (countData (.l xs)) := by
  rcases xs with _ | ⟨tag, _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩⟩ <;>
    simp [finish, code, raw, counts, secondCount, thirdCount, countsCode, DynamicTreeFold.stackBits,
      NNF.hasTwo_toBits, NNF.two, countData, BinaryNat.add_pair, BinaryNat.mul_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs <;> rfl

def combineBits (packet : List Bool) : List Bool :=
  let child := pairFst (pairSnd packet)
  let parent := pairSnd (pairSnd packet)
  pair (consNode (raw child) (raw parent)) (pair (finish child) (counts parent))

theorem combineBits_mem_FP : combineBits ∈ FP := by
  have hc := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hp := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hrc := mem_FP_comp hc pairFst_mem_FP
  have hrp := mem_FP_comp hp pairFst_mem_FP
  have hf := mem_FP_comp hc finish_mem_FP
  have hcp := mem_FP_comp hp pairSnd_mem_FP
  exact mem_FP_pair (consNode_mem_FP hrc hrp) (mem_FP_pair hf hcp)

theorem combineBits_code (z : List Bool) (child parent : List Data) :
    combineBits (pair z (pair (code child) (code parent))) = code (NNF.combine child parent) := by
  simp only [combineBits, pairFst_pair, pairSnd_pair, finish_code]
  simp only [code, raw, counts, countsCode, NNF.combine, pairFst_pair, pairSnd_pair,
    consNode_toBits, DynamicTreeFold.stackBits]

theorem countsCode_length_le (xs : List Data) : (countsCode xs).length ≤ 6 * (Data.l xs).size := by
  induction xs with
  | nil => simp [countsCode, DynamicTreeFold.stackBits]
  | cons d ds ih =>
    have hd := countData_size_le d
    have hp := @Data.size_pos d
    simp only [countsCode, DynamicTreeFold.stackBits, pair_length, BinaryNatCode.length_encode,
      Data.cons_size] at *
    omega

theorem code_length_le (xs : List Data) : (code xs).length ≤ 10 * (Data.l xs).size := by
  have hc := countsCode_length_le xs
  have hp := @Data.size_pos (.l xs)
  simp only [code, pair_length, Data.length_toBits]
  omega

theorem run_code_mem_FP :
    (fun bits => DynamicTreeFold.encode code (TreeFold.run [] NNF.combine bits)) ∈ FP := by
  have hg : ∀ child parent : List Data, (NNF.reference (NNF.combine child parent)).length ≤
      (NNF.reference child).length + (NNF.reference parent).length + 0 := by
    intro child parent
    simp [NNF.reference, NNF.combine, Data.cons_size]
  refine DynamicTreeFold.runEncoded_mem_FP (fun _ => []) (fun _ => NNF.combine) code
    (fun _ => code []) combineBits (constFn_mem_FP (code [])) combineBits_mem_FP
    (fun _ => rfl) combineBits_code ((PolyBound.const 100).add ((PolyBound.const 100).mul PolyBound.id))
    (fun z t ht => ?_)
  have hc := DynamicTreeFold.encode_length_le_mul code NNF.reference 10 (by decide)
    (fun xs => by simpa only [NNF.reference, List.length_replicate] using code_length_le xs)
    (TreeFold.run [] NNF.combine t)
  have hr := DynamicTreeFold.run_encode_length_le ([] : List Data) NNF.combine NNF.reference 0 hg t
  simp only [NNF.reference, List.length_replicate, Data.size_empty] at hr
  have hh := hc.trans (Nat.mul_le_mul_left 10 hr)
  have hl := ht.length_le
  omega

def extract (state : List Bool) : List Bool := pairFst (counts (pairFst (state.drop 1)))

theorem extract_mem_FP : extract ∈ FP := by
  have hf := mem_FP_comp (drop_mem_FP id_mem_FP (UnaryFn.const 1)) pairFst_mem_FP
  exact mem_FP_comp (mem_FP_comp hf pairSnd_mem_FP) pairFst_mem_FP

def read (bits : List Bool) : List Bool := extract (DynamicTreeFold.encode code (TreeFold.run [] NNF.combine bits))

theorem read_mem_FP : read ∈ FP := mem_FP_comp run_code_mem_FP extract_mem_FP

theorem read_toBits (d : Data) : read d.toBits = BinaryNatCode.encode (countData d) := by
  simp [read, extract, TreeFold.run_toBits, NNF.foldData_identity, NNF.combine,
    DynamicTreeFold.encode, DynamicTreeFold.stackBits, code, counts, countsCode]

theorem read_term (t : Term) : read t.toData.toBits = BinaryNatCode.encode t.monomialCount := by
  rw [read_toBits, countData_term]

end LeanCanny.ETR.MonomialCount
