/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TermArityFP

/-! # Exact formula arity in polynomial time

The existing term-arity fold is extended with formula-arity summaries. Keeping
both summaries prevents integer payloads from being counted as variables.
-/

@[expose] public section

namespace LeanCanny.ETR.FormulaArity
open LeanCanny.Encoding LeanCanny.Encoding.Brackets LeanCanny.Computation Turing.MultiTapeTM

def arityData : Data → ℕ
  | .l [tag, a] =>
    if tag = Codec.unary 1 ∨ tag = Codec.unary 2 then TermArity.arityData a
    else if tag = Codec.unary 3 then arityData a else 0
  | .l [tag, a, b] =>
    if tag = Codec.unary 4 ∨ tag = Codec.unary 5 then max (arityData a) (arityData b) else 0
  | _ => 0

theorem arityData_formula (p : Formula) : arityData p.toData = p.arity := by
  induction p <;> simp_all [arityData, Formula.toData, Formula.arity,
    TermArity.arityData_term, Codec.unary]

theorem arityData_le_size (d : Data) : arityData d ≤ d.size := by
  induction d using Data.inductionChildren with
  | node xs ih =>
    rcases xs with _ | ⟨tag, _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩⟩
    · simp [arityData]
    · simp [arityData]
    · have ha := ih a (by simp)
      have ht := TermArity.arityData_le_size a
      simp only [arityData]
      split_ifs <;> simp only [Data.cons_size, Data.size_empty] <;> omega
    · have ha := ih a (by simp)
      have hb := ih b (by simp)
      simp only [arityData]
      split_ifs <;> simp only [Data.cons_size, Data.size_empty] <;> omega
    · simp [arityData]

theorem arityData_size_le (d : Data) : (arityData d).size ≤ d.size + 1 := by
  have h := Nat.size_le.mpr ((arityData_le_size d).trans_lt
    (Nat.lt_two_pow_self : d.size < 2 ^ d.size))
  omega

def countsCode (xs : List Data) : List Bool :=
  DynamicTreeFold.stackBits (fun d => BinaryNatCode.encode (arityData d)) xs

def code (xs : List Data) : List Bool := pair (TermArity.code xs) (countsCode xs)

def raw (f : List Bool) : List Bool := TermArity.raw (pairFst f)
def secondTerm (f : List Bool) : List Bool := TermArity.secondCount (pairFst f)
def secondFormula (f : List Bool) : List Bool := pairFst (pairSnd (pairSnd f))
def thirdFormula (f : List Bool) : List Bool := pairFst (pairSnd (pairSnd (pairSnd f)))

theorem raw_mem_FP : raw ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem secondTerm_mem_FP : secondTerm ∈ FP :=
  mem_FP_comp pairFst_mem_FP TermArity.secondCount_mem_FP
theorem secondFormula_mem_FP : secondFormula ∈ FP :=
  mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem thirdFormula_mem_FP : thirdFormula ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairFst_mem_FP

attribute [local irreducible] raw secondTerm secondFormula thirdFormula

def finish (f : List Bool) : List Bool :=
  if NNF.HasOne 1 (raw f) ∨ NNF.HasOne 2 (raw f) then secondTerm f
  else if NNF.HasOne 3 (raw f) then secondFormula f
  else if NNF.HasTwo 4 (raw f) ∨ NNF.HasTwo 5 (raw f) then
    BoundedMaximum.maximum (pair (secondFormula f) (thirdFormula f)) else []

theorem finish_mem_FP : finish ∈ FP := by
  have hm := mem_FP_comp (mem_FP_pair secondFormula_mem_FP thirdFormula_mem_FP)
    BoundedMaximum.maximum_mem_FP
  have ha := ((NNF.hasOne_fppred 1).or (NNF.hasOne_fppred 2)).comp raw_mem_FP
  have hn := (NNF.hasOne_fppred 3).comp raw_mem_FP
  have hb := ((NNF.hasTwo_fppred 4).or (NNF.hasTwo_fppred 5)).comp raw_mem_FP
  exact mem_FP_of_eq (ha.ite_mem_FP secondTerm_mem_FP
    (hn.ite_mem_FP secondFormula_mem_FP (hb.ite_mem_FP hm (constFn_mem_FP []))))
    (fun _ => by simp only [finish, Function.comp_apply])

theorem finish_code (xs : List Data) : finish (code xs) = BinaryNatCode.encode (arityData (.l xs)) := by
  rcases xs with _ | ⟨tag, _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩⟩ <;>
    simp [finish, code, raw, secondTerm, secondFormula, thirdFormula,
      TermArity.secondCount, TermArity.counts, TermArity.code, TermArity.raw,
      TermArity.countsCode, countsCode, DynamicTreeFold.stackBits, NNF.hasOne_toBits,
      NNF.hasTwo_toBits, NNF.one, NNF.two, arityData, BoundedMaximum.maximum_codes]
  all_goals first | rfl | (split_ifs <;> rfl)

def combineBits (packet : List Bool) : List Bool :=
  let child := pairFst (pairSnd packet)
  let parent := pairSnd (pairSnd packet)
  pair (TermArity.combineBits (pair (pairFst packet) (pair (pairFst child) (pairFst parent))))
    (pair (finish child) (pairSnd parent))

theorem combineBits_mem_FP : combineBits ∈ FP := by
  have hc := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hp := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have htc := mem_FP_comp hc pairFst_mem_FP
  have htp := mem_FP_comp hp pairFst_mem_FP
  have hargs := mem_FP_pair pairFst_mem_FP (mem_FP_pair htc htp)
  have ht := mem_FP_comp hargs TermArity.combineBits_mem_FP
  have hf := mem_FP_comp hc finish_mem_FP
  have hr := mem_FP_comp hp pairSnd_mem_FP
  exact mem_FP_pair ht (mem_FP_pair hf hr)

theorem combineBits_code (z : List Bool) (child parent : List Data) :
    combineBits (pair z (pair (code child) (code parent))) = code (NNF.combine child parent) := by
  have hc0 : pairFst (code child) = TermArity.code child := by simp only [code, pairFst_pair]
  have hp0 : pairFst (code parent) = TermArity.code parent := by simp only [code, pairFst_pair]
  have hp1 : pairSnd (code parent) = countsCode parent := by simp only [code, pairSnd_pair]
  simp only [combineBits, pairFst_pair, pairSnd_pair, hc0, hp0, hp1,
    TermArity.combineBits_code, finish_code]
  rfl

theorem countsCode_length_le (xs : List Data) : (countsCode xs).length ≤ 6 * (Data.l xs).size := by
  induction xs with
  | nil => simp [countsCode, DynamicTreeFold.stackBits]
  | cons d ds ih =>
    have hd := arityData_size_le d
    have hp := @Data.size_pos d
    simp only [countsCode, DynamicTreeFold.stackBits, pair_length,
      BinaryNatCode.length_encode, Data.cons_size] at *
    omega

theorem code_length_le (xs : List Data) : (code xs).length ≤ 30 * (Data.l xs).size := by
  have ht := TermArity.code_length_le xs
  have hf := countsCode_length_le xs
  have hp := @Data.size_pos (.l xs)
  simp only [code, pair_length]
  omega

theorem run_code_mem_FP :
    (fun bits => DynamicTreeFold.encode code (TreeFold.run [] NNF.combine bits)) ∈ FP := by
  have hg : ∀ child parent : List Data, (NNF.reference (NNF.combine child parent)).length ≤
      (NNF.reference child).length + (NNF.reference parent).length + 0 := by
    intro child parent
    simp [NNF.reference, NNF.combine, Data.cons_size]
  refine DynamicTreeFold.runEncoded_mem_FP (fun _ => []) (fun _ => NNF.combine) code
    (fun _ => code []) combineBits (constFn_mem_FP _) combineBits_mem_FP
    (fun _ => rfl) combineBits_code
    ((PolyBound.const 1000).add ((PolyBound.const 1000).mul PolyBound.id)) ?_
  intro z t ht
  have hc := DynamicTreeFold.encode_length_le_mul code NNF.reference 30 (by decide)
    (fun xs => by simpa only [NNF.reference, List.length_replicate] using code_length_le xs)
    (TreeFold.run [] NNF.combine t)
  have hr := DynamicTreeFold.run_encode_length_le ([] : List Data) NNF.combine NNF.reference 0 hg t
  simp only [NNF.reference, List.length_replicate, Data.size_empty] at hr
  have hh := hc.trans (Nat.mul_le_mul_left 30 hr)
  have hl := ht.length_le
  omega

def extract (state : List Bool) : List Bool := pairFst (pairSnd (pairFst (state.drop 1)))

theorem extract_mem_FP : extract ∈ FP := by
  have hf := mem_FP_comp (drop_mem_FP id_mem_FP (UnaryFn.const 1)) pairFst_mem_FP
  have hs := mem_FP_comp hf pairSnd_mem_FP
  exact mem_FP_comp hs pairFst_mem_FP

def read (bits : List Bool) : List Bool :=
  extract (DynamicTreeFold.encode code (TreeFold.run [] NNF.combine bits))

theorem read_mem_FP : read ∈ FP := mem_FP_comp run_code_mem_FP extract_mem_FP

theorem read_toBits (d : Data) : read d.toBits = BinaryNatCode.encode (arityData d) := by
  simp [read, extract, TreeFold.run_toBits, NNF.foldData_identity, NNF.combine,
    DynamicTreeFold.encode, DynamicTreeFold.stackBits, code, countsCode]

theorem read_formula (p : Formula) : read p.encode = BinaryNatCode.encode p.arity := by
  rw [Formula.encode, read_toBits, arityData_formula]

/-- A total unary arity reader; malformed inputs are capped by their bit length. -/
def value (bits : List Bool) : ℕ := min (Nat.fromBitsLE (read bits)) bits.length

theorem value_unary : UnaryFn value :=
  UnaryFn.fromBitsLE_min read_mem_FP (UnaryFn.length id_mem_FP)

theorem value_encode (p : Formula) : value p.encode = p.arity := by
  rw [value, read_formula]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact min_eq_left (by simpa only [Formula.encode, Data.length_toBits] using p.arity_le_dataSize)

end LeanCanny.ETR.FormulaArity
