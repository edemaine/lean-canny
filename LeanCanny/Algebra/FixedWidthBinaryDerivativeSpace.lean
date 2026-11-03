/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthDerivativeSpace
public import LeanCanny.Computation.PolyTimeBinaryRange
public import LeanCanny.Algebra.MacaulayEntryEncoding
/-! # Partial-derivative coefficient space with a binary degree ceiling

Only exponent-block arity and widths are unary. The degree is compared in
binary, so a compact original source does not need a unary degree reader.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthDerivativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical

theorem bounded_binary_fppred (A V bound : List Bool→ℕ) (target : List Bool→List Bool)
    (hA : UnaryFn A) (hV : UnaryFn V) (hb : BinaryFn bound) (ht : target∈FP) :
    FPPred (FixedWidthQuery.Bounded A V target bound) := by
  have HR : BinaryFn (fun p=>Nat.fromBitsLE
      (FixedWidthQuery.read A V target (MacaulayBits.loopQuery p))) :=
    BinaryFn.fromBits (mem_FP_comp MacaulayBits.loopQuery_mem_FP (FixedWidthQuery.read_mem_FP hA hV ht))
  apply ((HR.le (hb.comp pairFst_mem_FP)).forall_lt hA).of_iff
  intro q
  simp only [FixedWidthQuery.Bounded, MacaulayBits.loopQuery, pairFst_pair, pairSnd_pair,
    List.length_replicate, Function.comp_apply]
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro hi
  rw [FixedWidthQuery.read_packet]
  simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits,FixedWidthQuery.entry,hi,ite_true]

theorem evaluator_binary (A W V D selected : List Bool→ℕ) (target modulus : List Bool→List Bool)
    {coefficient : List Bool→List Bool} (E : SpaceFunction coefficient)
    (hA : UnaryFn A) (hW : UnaryFn W) (hV : UnaryFn V) (hD : BinaryFn D)
    (hs : UnaryFn selected) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (value A W V D selected target modulus coefficient) := by
  have EQ := ((E.precompose (query A W V selected target)
    (query_mem_FP A W V selected target hA hW hV hs ht)).withInput).postcompose
    (finish A V selected target modulus) (finish_mem_FP A V selected target modulus hA hV hs ht hm)
  have hb := bounded_binary_fppred A V (fun q=>D q-1) target hA hV (hD.sub (BinaryFn.const 1)) ht
  have EB := SpaceFunction.branch (fun q=>decide (FixedWidthQuery.Bounded A V target (fun q=>D q-1) q))
    hb.flag_mem_FP EQ (SpaceFunction.ofFP (fun _=>[]) (constFn_mem_FP []))
  exact EB.congr (funext fun q=>by simp only [value,Function.comp_apply,decide_eq_true_eq])

end LeanCanny.Algebra.FixedWidthDerivativeBits
