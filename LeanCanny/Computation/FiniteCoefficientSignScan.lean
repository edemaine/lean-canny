/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.SpaceFunctionBinaryQuantifiers
public import LeanCanny.Computation.SpaceFunctionBranch
public import LeanCanny.Algebra.InfinitesimalSignSpace
/-! # Binary finite scans for leading, higher and lower coefficient signs

The input vertex remains fixed in every child request. The scan stores
binary counters and never a list of child replies.
-/
@[expose] public section
namespace LeanCanny.Computation.FiniteCoefficientSignScan
open LeanCanny.Encoding LeanCanny.Algebra Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def query (q : List Bool) (e k : ℕ) := pair q (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k))
abbrev Zero (sign : List Bool→List Bool) (q : List Bool) (e k : ℕ) :=
  sign (query q e k)=InfinitesimalSign.encode 0

abbrev Guards (sign head : List Bool→List Bool) (choice degree cap : List Bool→ℕ) (q : List Bool) : Prop :=
  (∀ k<choice q,∀ e<cap q+1,Zero sign q e k) ∧
  ¬Zero sign q (degree q) (choice q) ∧
  (∀ e<cap q+1,degree q<e→Zero sign q e (choice q)) ∧
  (head q≠InfinitesimalSign.encode 0 ∨ Zero sign q 0 (choice q))

private theorem zero_space {sign : List Bool→List Bool} (E : SpaceFunction sign)
    (f : List Bool→List Bool) (hf : f∈FP) :
    SpaceFunction (fun q=>[decide (sign (f q)=InfinitesimalSign.encode 0)]) :=
  (E.precompose f hf).postcompose _ (stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP

private theorem not_space {f : List Bool→List Bool} (E : SpaceFunction f) :
    SpaceFunction (fun q=>[decide (f q≠[true])]) :=
  E.postcompose _ (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP

theorem evaluator (sign head : List Bool→List Bool) (choice degree cap : List Bool→ℕ)
    (ES : SpaceFunction sign) (EH : SpaceFunction head)
    (hK : BinaryFn choice) (hD : BinaryFn degree) (hN : BinaryFn cap) :
    SpaceFunction (fun q=>[decide (Guards sign head choice degree cap q)]) := by
  let lowerQuery:=fun z=>query (pairFst (pairFst z)) (Nat.fromBitsLE (pairSnd z)) (Nat.fromBitsLE (pairSnd (pairFst z)))
  have hlow : lowerQuery∈FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (BinaryFn.fromBits pairSnd_mem_FP).bits_mem_FP
      (BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)).bits_mem_FP)
  have hNp : BinaryFn (fun z=>cap (pairFst z)) := hN.comp pairFst_mem_FP
  have hKp : BinaryFn (fun z=>choice (pairFst z)) := hK.comp pairFst_mem_FP
  have hDp : BinaryFn (fun z=>degree (pairFst z)) := hD.comp pairFst_mem_FP
  have EL:=((zero_space ES lowerQuery hlow).forall_binary
    (hNp.add (BinaryFn.const 1))).forall_binary hK
  have EL' : SpaceFunction (fun q=>[decide (∀ k<choice q,∀ e<cap q+1,Zero sign q e k)]) :=
    EL.congr (by
      funext q
      apply congrArg List.singleton
      apply Bool.eq_iff_iff.mpr
      simp only [lowerQuery,query,Zero,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
        List.cons.injEq,and_true,decide_eq_true_eq])
  let chosen:=fun q=>query q (degree q) (choice q)
  have hchosen : chosen∈FP := mem_FP_pair id_mem_FP (mem_FP_pair hD.bits_mem_FP hK.bits_mem_FP)
  have EC:=(not_space (zero_space ES chosen hchosen)).congr (show
    (fun q=>[decide ([decide (sign (chosen q)=InfinitesimalSign.encode 0)]≠[true])])=
      (fun q=>[decide (¬Zero sign q (degree q) (choice q))]) by
        funext q
        apply congrArg List.singleton
        apply Bool.eq_iff_iff.mpr
        simp only [chosen,Zero,ne_eq,List.cons.injEq,and_true,decide_eq_true_eq])
  let highQuery:=fun z=>query (pairFst z) (Nat.fromBitsLE (pairSnd z)) (choice (pairFst z))
  have hhigh : highQuery∈FP := mem_FP_pair pairFst_mem_FP
    (mem_FP_pair (BinaryFn.fromBits pairSnd_mem_FP).bits_mem_FP hKp.bits_mem_FP)
  have hlt : FPPred (fun z=>degree (pairFst z)<Nat.fromBitsLE (pairSnd z)) :=
    hDp.lt (BinaryFn.fromBits pairSnd_mem_FP)
  have EB:=SpaceFunction.branch _ hlt.flag_mem_FP (zero_space ES highQuery hhigh)
    (SpaceFunction.ofFP _ (constFn_mem_FP [true]))
  have EB' : SpaceFunction (fun z=>[decide (degree (pairFst z)<Nat.fromBitsLE (pairSnd z)→
      Zero sign (pairFst z) (Nat.fromBitsLE (pairSnd z)) (choice (pairFst z)))]) := EB.congr (by
    funext z
    simp only [highQuery,Zero,decide_eq_true_eq]
    by_cases h:degree (pairFst z)<Nat.fromBitsLE (pairSnd z) <;> simp only [h,ite_true,ite_false,true_implies,false_implies,decide_true])
  have EHi:=(EB'.forall_binary (hN.add (BinaryFn.const 1))).congr (show _=
      (fun q=>[decide (∀ e<cap q+1,degree q<e→Zero sign q e (choice q))]) by
    funext q
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,List.cons.injEq,and_true,decide_eq_true_eq])
  let constant:=fun q=>query q 0 (choice q)
  have hconst : constant∈FP := mem_FP_pair id_mem_FP (mem_FP_pair (constFn_mem_FP _) hK.bits_mem_FP)
  have ER:=((EH.pairOutputs (zero_space ES constant hconst)).postcompose _
    ((stringEq_fppred pairFst_mem_FP (constFn_mem_FP (InfinitesimalSign.encode 0))).not.or
      (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true]))).flag_mem_FP).congr (show _=
      (fun q=>[decide (head q≠InfinitesimalSign.encode 0 ∨ Zero sign q 0 (choice q))]) by
    funext q
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [constant,Zero,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq])
  exact (EL'.andFlags (EC.andFlags (EHi.andFlags ER))).congr (by
    funext q
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Guards,List.cons.injEq,and_true,decide_eq_true_eq])

end LeanCanny.Computation.FiniteCoefficientSignScan
