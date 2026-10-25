/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.ImplicitGraphPSPACE
public import LeanCanny.Computation.SpaceFunctionComposition
public import LeanCanny.Computation.SpaceDeciderFunction
public import LeanCanny.Encoding.BracketsFP

/-! # Native bounded scans of space-bounded flag routines

The binary loop counter is capped before conversion to a unary child index.
This retains polynomial preparation costs on all typed inputs, including
counters beyond the actual loop range. Child running time is unrestricted.
-/

@[expose] public section
namespace LeanCanny.Computation.SpaceFunction
open Turing.MultiTapeTM LeanCanny.Encoding.Brackets
open scoped Classical

theorem andFlags {f g : List Bool → List Bool} (hf : SpaceFunction f) (hg : SpaceFunction g) :
    SpaceFunction (fun c => [decide (f c = [true] ∧ g c = [true])]) := by
  have hp := (stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).and
    (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true]))
  exact ((hf.pairOutputs hg).postcompose _ hp.flag_mem_FP).congr
    (funext fun c => by simp only [Function.comp_apply, pairFst_pair, pairSnd_pair])

theorem forall_unary {test : List Bool → List Bool} {count : List Bool → ℕ}
    (ht : SpaceFunction test) (hn : UnaryFn count) :
    SpaceFunction (fun c => [decide (∀ k < count c, test (pair c (List.replicate k true)) = [true])]) := by
  have hpar := ComputableTidilyInPolyTime.fst encBits encNat
  have hcounter := ComputableTidilyInPolyTime.snd encBits encNat
  have hcap := ComputableTidilyInPolyTime.comp hn hpar
  have hdecode := ComputableTidilyInPolyTime.bitsBoundedBinaryValueWithInput hcap
    (ComputableTidilyInPolyTime.bitsReverse.comp hcounter.encoded)
  have hindex : ComputableTidilyInPolyTime (fun p : List Bool × ℕ => min p.2 (count p.1))
      (encPair encBits encNat) encUnary := by
    apply hdecode.of_enc_eq
    intro p
    apply congrArg encUnary
    simp [Cslib.BitString.boundedBinaryValue_eq, Cslib.BitString.binaryValue_reverse_bits,
      encNat_apply, Nat.min_comm]
  have hpacket := pair_computable hpar hindex.encoded
  have heq := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).computable
  have hchild := (ComputableTidilyInPolySpace.of_polyTime heq).comp
    (ht.computable.comp (.of_polyTime hpacket))
  have hchild' : ComputableTidilyInPolySpace
      (fun p : List Bool × ℕ => decide (test (pair p.1 (List.replicate (min p.2 (count p.1)) true)) = [true]))
      (encPair encBits encNat) encBool := by
    apply hchild.congr
    intro p
    apply Bool.eq_iff_iff.mpr
    simp only [encUnary_apply, id_eq]
    simp only [decide_eq_true_eq]
    exact Iff.of_eq (@decide_eq_true_eq _ _)
  have hall := ImplicitGraph.forall_below_computable hchild'
    (ComputableTidilyInPolyTime.unary_to_binary.comp hn)
  let L : Language := {c | ∀ k < count c, test (pair c (List.replicate k true)) = [true]}
  have hd : SpaceDecider L := SpaceDecider.of_computable hall (fun c => by
    simp only [L, Set.mem_ofPred_eq, decide_eq_true_eq, Function.comp_apply]
    constructor
    · intro h k hk
      rw [Nat.min_eq_left (Nat.le_of_lt hk)]
      exact h k hk
    · intro h k hk
      simpa only [Nat.min_eq_left (Nat.le_of_lt hk)] using h k hk)
  apply hd.flagEvaluator.congr
  funext c
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rfl

end LeanCanny.Computation.SpaceFunction
