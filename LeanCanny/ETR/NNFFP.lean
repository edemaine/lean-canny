/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.NNFEncoding
public import LeanCanny.ETR.Complexity

/-!
# Polynomial-time negation normalization

The stack stores raw children and both candidate polarities. A comparison with
an additive raw-size encoding bounds every intermediate stack, including runs
on malformed input. The public normalizer rejects malformed formulas to falsum.
-/

@[expose] public section

namespace LeanCanny.ETR.NNF
open Complexity
open LeanCanny.Encoding
open Brackets

theorem dual_lists_size (xs : List Data) :
    (Data.l (xs.map (fun d => (dual d).1))).size +
      (Data.l (xs.map (fun d => (dual d).2))).size ≤ 20 * (Data.l xs).size := by
  induction xs with
  | nil => simp [Data.size_empty]
  | cons d ds ih =>
      have hd := dual_size d
      simp only [List.map_cons, Data.cons_size] at *
      omega

theorem code_length_le (xs : List Data) : (code xs).length ≤ 50 * (Data.l xs).size := by
  have hs := dual_lists_size xs
  have hp := @Data.size_pos (.l xs)
  simp only [code, pair_length, Data.length_toBits]
  omega

def reference (xs : List Data) : List Bool := List.replicate (Data.l xs).size false

theorem run_code_mem_FP :
    (fun bits => DynamicTreeFold.encode code (TreeFold.run [] combine bits)) ∈ FP := by
  have hg : ∀ child parent : List Data, (reference (combine child parent)).length ≤
      (reference child).length + (reference parent).length + 0 := by
    intro child parent
    simp [reference, combine, Data.cons_size]
  refine DynamicTreeFold.runEncoded_mem_FP (fun _ => []) (fun _ => combine) code
    (fun _ => code []) combineBits (constFn_mem_FP (code [])) combineBits_mem_FP
    (fun _ => rfl) combineBits_code
    ((PolyBound.const 350).add ((PolyBound.const 300).mul PolyBound.id))
    (fun z t ht => ?_)
  have hc := DynamicTreeFold.encode_length_le_mul code reference 50 (by decide)
    (fun xs => by simpa only [reference, List.length_replicate] using code_length_le xs)
    (TreeFold.run [] combine t)
  have hr := DynamicTreeFold.run_encode_length_le ([] : List Data) combine reference 0 hg t
  simp only [reference, List.length_replicate, Data.size_empty] at hr
  have hh := hc.trans (Nat.mul_le_mul_left 50 hr)
  have hl := ht.length_le
  omega

theorem foldData_identity (d : Data) : TreeFold.foldData ([] : List Data) combine d = d.asList := by
  have key : ∀ (n : ℕ) (d : Data), d.size ≤ n →
      TreeFold.foldData ([] : List Data) combine d = d.asList := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        rintro ⟨xs⟩ hn
        rw [TreeFold.foldData]
        have hc : ∀ c ∈ xs, Data.l (TreeFold.foldData [] combine c) = c := by
          intro c hmem
          rw [ih c.size ((Data.size_lt_of_mem hmem).trans_le hn) c le_rfl, Data.asList_l]
        have hl : ∀ ys : List Data,
            (∀ c ∈ ys, Data.l (TreeFold.foldData [] combine c) = c) →
            (ys.map (TreeFold.foldData [] combine)).foldr combine [] = ys := by
          intro ys
          induction ys with
          | nil => intro _; rfl
          | cons c cs ihcs =>
              intro h
              rw [List.map_cons, List.foldr_cons, combine, h c (List.mem_cons_self ..),
                ihcs (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))]
        simpa only [Data.l_asList] using hl xs hc
  exact key d.size d le_rfl

def extract (positive : Bool) (state : List Bool) : List Bool :=
  let frame := pairFst (state.drop 1)
  firstChild (if positive then pos frame else neg frame)

theorem extract_mem_FP (positive : Bool) : extract positive ∈ FP := by
  have hf := mem_FP_comp (drop_mem_FP id_mem_FP (UnaryFn.const 1)) pairFst_mem_FP
  cases positive
  · exact mem_FP_comp (mem_FP_comp hf neg_mem_FP) firstChild_mem_FP
  · exact mem_FP_comp (mem_FP_comp hf pos_mem_FP) firstChild_mem_FP

def transformBits (positive : Bool) (bits : List Bool) : List Bool :=
  extract positive (DynamicTreeFold.encode code (TreeFold.run [] combine bits))

theorem transformBits_mem_FP (positive : Bool) : transformBits positive ∈ FP :=
  mem_FP_comp run_code_mem_FP (extract_mem_FP positive)

theorem transformBits_toBits (positive : Bool) (d : Data) :
    transformBits positive d.toBits = (if positive then (dual d).1 else (dual d).2).toBits := by
  cases positive <;>
    simp [transformBits, extract, TreeFold.run_toBits, foldData_identity, combine,
      DynamicTreeFold.encode, DynamicTreeFold.stackBits, code, pos, neg]

/-- A total normalizer: malformed input strings become the false formula. -/
def normalize (bits : List Bool) : List Bool :=
  if Grammar.recognizeFormula bits = true then transformBits true bits else falseData.toBits

theorem normalize_mem_FP : normalize ∈ FP :=
  (FPPred.of_flag Grammar.recognizeFormula_mem_FP).ite_mem_FP
    (transformBits_mem_FP true) (constFn_mem_FP falseData.toBits)

theorem normalize_encode (p : Formula) : normalize p.encode = (p.nnf true).encode := by
  rw [normalize, ite_eq_left (Grammar.recognizeFormula_encode p)]
  change transformBits true p.toData.toBits = _
  rw [transformBits_toBits, dual_formula]
  rfl

/-- The total writer has linear output length, including its malformed-input branch. -/
theorem normalize_length_le (bits : List Bool) : (normalize bits).length ≤ 20 * bits.length + 4 := by
  by_cases hr : Grammar.recognizeFormula bits = true
  · obtain ⟨p, rfl⟩ := (Grammar.recognizeFormula_true_iff bits).mp hr
    have hs := dual_size p.toData
    rw [dual_formula] at hs
    rw [normalize_encode]
    simp only [Formula.encode, Data.length_toBits] at *
    omega
  · rw [normalize, ite_eq_right hr, Data.length_toBits, falseData_size]
    omega

def language : Language := {bits | ∃ p : Formula,
  bits = p.encode ∧ p.IsNNF = true ∧ p.Satisfiable}

@[simp] theorem encode_mem_language (p : Formula) :
    p.encode ∈ language ↔ p.IsNNF = true ∧ p.Satisfiable := by
  simp [language, Formula.encode_injective.eq_iff]

theorem normalize_correct (bits : List Bool) :
    bits ∈ ETR.language ↔ normalize bits ∈ language := by
  by_cases hr : Grammar.recognizeFormula bits = true
  · obtain ⟨p, rfl⟩ := (Grammar.recognizeFormula_true_iff bits).mp hr
    rw [ETR.encode_mem_language, normalize_encode, encode_mem_language, Formula.nnf_isNNF]
    exact (Iff.intro (fun h => ⟨rfl, p.satisfiable_nnf.mpr h⟩) (fun h => p.satisfiable_nnf.mp h.2))
  · have hn : bits ∉ ETR.language := by
      rintro ⟨p, hp, _⟩
      have he := (Formula.decode_eq_some_iff bits p).mp hp
      exact hr (he ▸ Grammar.recognizeFormula_encode p)
    have hf : falseData.toBits ∉ language := by
      change Formula.falsum.encode ∉ language
      simp
    simp [normalize, hr, hn, hf]

theorem etr_reduces_to_nnf : ETR.language ≤ₚ language :=
  ⟨normalize, normalize_mem_FP, normalize_correct⟩

end LeanCanny.ETR.NNF
