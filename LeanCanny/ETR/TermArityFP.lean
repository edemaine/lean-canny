/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TermView
public import LeanCanny.ETR.NNFFP
public import LeanCanny.Computation.BoundedMaximum

/-! # Polynomial-time exact source arity

A raw tree fold computes syntax arity, keeping numeric payloads separate from
arithmetic children. Its encoded stack has linear length on all inputs.
Validation then supplies the exact arity of the total source view, in unary
as well as binary, for the coordinate layout of the tube systems.
-/

@[expose] public section

namespace LeanCanny.ETR.TermArity
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation

def arityData : Data → ℕ
  | .l [tag, a] => if tag = Codec.unary 1 then (a.size - 2) / 2 + 1 else 0
  | .l [tag, a, b] =>
    if tag = Codec.unary 2 ∨ tag = Codec.unary 3 then max (arityData a) (arityData b) else 0
  | _ => 0

theorem arityData_term (t : Term) : arityData t.toData = t.arity := by
  induction t with
  | const z => simp [arityData, Term.toData, Term.arity, Codec.unary]
  | var i =>
    simp only [Term.toData, arityData, ite_true, Codec.unary_size, Term.arity]
    omega
  | add t u ht hu => simp [arityData, Term.toData, Term.arity, ht, hu]
  | mul t u ht hu => simp [arityData, Term.toData, Term.arity, ht, hu]

theorem arityData_le_size (d : Data) : arityData d ≤ d.size := by
  have key : ∀ (n : ℕ) (d : Data), d.size ≤ n → arityData d ≤ d.size := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      rintro ⟨xs⟩ hn
      rcases xs with _ | ⟨tag, _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩⟩
      · simp [arityData]
      · simp [arityData]
      · have hdiv := Nat.div_le_self (a.size - 2) 2
        simp only [arityData]
        split_ifs <;> simp only [Data.cons_size, Data.size_empty] <;> omega
      · have ha := ih a.size ((Data.size_lt_of_mem (by simp : a ∈ [tag, a, b])).trans_le hn) a le_rfl
        have hb := ih b.size ((Data.size_lt_of_mem (by simp : b ∈ [tag, a, b])).trans_le hn) b le_rfl
        simp only [arityData]
        split_ifs <;> simp only [Data.cons_size, Data.size_empty] <;> omega
      · simp [arityData]
  exact key d.size d le_rfl

theorem arityData_size_le (d : Data) : (arityData d).size ≤ d.size + 1 := by
  have h := Nat.size_le.mpr ((arityData_le_size d).trans_lt (Nat.lt_two_pow_self : d.size < 2 ^ d.size))
  omega

def countsCode (xs : List Data) : List Bool := DynamicTreeFold.stackBits (fun d => BinaryNatCode.encode (arityData d)) xs
def code (xs : List Data) : List Bool := pair (Data.l xs).toBits (countsCode xs)
def raw (frame : List Bool) : List Bool := pairFst frame
def counts (frame : List Bool) : List Bool := pairSnd frame
def secondCount (frame : List Bool) : List Bool := pairFst (pairSnd (counts frame))
def thirdCount (frame : List Bool) : List Bool := pairFst (pairSnd (pairSnd (counts frame)))

def finish (frame : List Bool) : List Bool :=
  if NNF.HasOne 1 (raw frame) then
    BinaryNat.succ (BinaryNatCode.encode (Codec.unaryValue (NNF.second (raw frame))))
  else if NNF.HasTwo 2 (raw frame) ∨ NNF.HasTwo 3 (raw frame) then
    BoundedMaximum.maximum (pair (secondCount frame) (thirdCount frame)) else []

theorem secondCount_mem_FP : secondCount ∈ FP :=
  mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem thirdCount_mem_FP : thirdCount ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairFst_mem_FP

theorem finish_mem_FP : finish ∈ FP := by
  have hv := bits_mem_FP (Codec.unaryValue_unary.comp (mem_FP_comp pairFst_mem_FP NNF.second_mem_FP))
  have hs := mem_FP_comp hv BinaryNat.succ_mem_FP
  have hm := mem_FP_comp (mem_FP_pair secondCount_mem_FP thirdCount_mem_FP) BoundedMaximum.maximum_mem_FP
  have h := ((NNF.hasOne_fppred 1).comp pairFst_mem_FP).ite_mem_FP hs
    ((((NNF.hasTwo_fppred 2).comp pairFst_mem_FP).or ((NNF.hasTwo_fppred 3).comp pairFst_mem_FP)).ite_mem_FP hm (constFn_mem_FP []))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem finish_code (xs : List Data) : finish (code xs) = BinaryNatCode.encode (arityData (.l xs)) := by
  rcases xs with _ | ⟨tag, _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩⟩ <;>
    simp [finish, code, raw, counts, secondCount, thirdCount, countsCode, DynamicTreeFold.stackBits,
      NNF.hasOne_toBits, NNF.hasTwo_toBits, NNF.one, NNF.two, NNF.second, arityData,
      BinaryNat.succ_eq_bits, Codec.unaryValue, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  all_goals
    split_ifs <;> first | rfl | exact BoundedMaximum.maximum_codes _ _

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
    have hd := arityData_size_le d
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

theorem read_toBits (d : Data) : read d.toBits = BinaryNatCode.encode (arityData d) := by
  simp [read, extract, TreeFold.run_toBits, NNF.foldData_identity, NNF.combine,
    DynamicTreeFold.encode, DynamicTreeFold.stackBits, code, counts, countsCode]

theorem read_term (t : Term) : read t.toData.toBits = BinaryNatCode.encode t.arity := by
  rw [read_toBits, arityData_term]

end LeanCanny.ETR.TermArity

namespace LeanCanny.ETR.TermArity
open Complexity
open LeanCanny.Encoding

noncomputable def arity (source : List Bool → List Bool) (c : List Bool) : ℕ := (TermView.term (source c)).arity

theorem arity_unary {source : List Bool → List Bool} (hs : source ∈ FP) : UnaryFn (arity source) := by
  have hn := mem_FP_comp hs TermView.normalize_mem_FP
  have hr := mem_FP_comp hn read_mem_FP
  have hcap := UnaryFn.fromBitsLE_min hr (UnaryFn.length hn)
  apply hcap.of_eq
  intro c
  simp only [Function.comp_apply, TermView.normalize_eq_term, read_term, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Data.length_toBits, arity]
  exact min_eq_left (Term.arity_le_dataSize _)

end LeanCanny.ETR.TermArity
