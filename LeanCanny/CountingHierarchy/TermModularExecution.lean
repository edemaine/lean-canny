/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.TermModularCombine

/-! # Uniform native modular evaluation of encoded expression trees -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.TermModular

open LeanCanny.Encoding LeanCanny.ETR Turing.MultiTapeTM
open Brackets

 def allowance (P : Parameters) (z : List Bool) : ℕ := 2 * (cap P z).size + 1

 theorem allowance_unary (P : Parameters) (hP : Access P) : UnaryFn (allowance P) := by
  have hsize := (ComputableInPolyTime.binary_size.comp (cap_binary P hP).computableInPolyTime).tidy
  exact ((UnaryFn.const 2).mul hsize).add (UnaryFn.const 1)

 def run (P : Parameters) (source : List Bool → List Bool) (z : List Bool) : List Bool :=
  DynamicTreeFold.encode (code P z) (TreeFold.run [] NNF.combine (source z))

 theorem run_FP (P : Parameters) (hP : Access P) (source : List Bool → List Bool) (hs : source ∈ FP) :
    run P source ∈ FP := by
  let bound := fun z => 15 + (source z).length * (14 + 2 * allowance P z)
  have hB : UnaryFn bound := (UnaryFn.const 15).add ((UnaryFn.length hs).mul
    ((UnaryFn.const 14).add ((UnaryFn.const 2).mul (allowance_unary P hP))))
  have hpoly : PolyBounded List.length bound := by
    simpa only [encBits_apply, encUnary_apply, List.length_replicate] using hB.polyBounded_length
  refine DynamicTreeFold.sourceEncoded_mem_FP_context source hs (fun _ => []) (fun _ => NNF.combine)
    (code P) (fun z => code P z []) (combineBits P) ?_ (combineBits_FP P hP)
    (fun _ => rfl) (combineBits_code P) hpoly ?_
  · have heq (z : List Bool) : code P z [] = pair Data.empty.toBits [] := by simp [code]
    exact mem_FP_of_eq (constFn_mem_FP (pair Data.empty.toBits [])) (fun z => (heq z).symm)
  · intro z t ht
    have h := DynamicTreeFold.run_encode_length_le ([] : List Data) NNF.combine (code P z)
      (allowance P z) (code_growth P z) t
    rw [code_empty_length] at h
    have hfactor : 2 * 6 + 2 * allowance P z + 2 = 14 + 2 * allowance P z := by omega
    rw [hfactor] at h
    have hm := Nat.mul_le_mul_right (14 + 2 * allowance P z) ht.length_le
    dsimp only [bound]
    omega

 def extract (state : List Bool) : ℕ := (values (pairFst (state.drop 1)))[0]?.getD 0

 theorem extract_binary : BinaryFn extract := by
  have hf : (fun s : List Bool => pairFst (s.drop 1)) ∈ FP :=
    mem_FP_comp (drop_mem_FP id_mem_FP (UnaryFn.const 1)) pairFst_mem_FP
  have hv := values_FP.comp (FP.computable hf)
  have h : ComputableInPolyTime (fun s => extract s) encBits encNat := by
    simpa only [extract, List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 hv.computableInPolyTime (ComputableInPolyTime.const 0)
  exact h.tidy

 def write (P : Parameters) (source : List Bool → List Bool) (z : List Bool) : ℕ := extract (run P source z)

 theorem write_binary (P : Parameters) (hP : Access P) (source : List Bool → List Bool) (hs : source ∈ FP) :
    BinaryFn (write P source) := extract_binary.comp (FP.computable (run_FP P hP source hs))

 theorem write_data (P : Parameters) (source : List Bool → List Bool) (z : List Bool) (d : Data)
    (hd : source z = d.toBits) : write P source z = value (P.prime z) (P.coordinate z) d := by
  simp [write, run, hd, TreeFold.run_toBits, NNF.foldData_identity, NNF.combine,
    DynamicTreeFold.encode, DynamicTreeFold.stackBits, extract, values_code]

 theorem write_term_cast (P : Parameters) (source : List Bool → List Bool) (z : List Bool)
    [Fact (P.prime z).Prime] (t : Term) (ht : source z = t.toData.toBits) :
    (write P source z : ZMod (P.prime z)) = t.eval (fun i => (P.coordinate z i : ZMod (P.prime z))) := by
  rw [write_data P source z t.toData ht]
  exact value_term_cast _ t

end LeanCanny.CountingHierarchy.TermModular
