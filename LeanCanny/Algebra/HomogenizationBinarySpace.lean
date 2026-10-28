/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogenizationSpace
public import LeanCanny.Computation.PolyTimeBinaryRange

/-! # Native homogenization with a binary degree allowance

Only the number of exponent blocks and their widths are unary. The original
clipped degree test and coefficient packet also support binary degree bounds.
-/

@[expose] public section
namespace LeanCanny.Algebra.HomogenizationBits
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial

theorem total_binary {N A W D : List Bool → ℕ} (hN : UnaryFn N) (hA : UnaryFn A)
    (hW : UnaryFn W) (hD : BinaryFn D) : BinaryFn (total N A W D) := by
  have hr := BinaryFn.fromBits (mem_FP_comp MacaulayBits.loopQuery_mem_FP (read_mem_FP hN hW))
  have hd := ((hD.add (BinaryFn.const 1)).comp pairFst_mem_FP).comp pairFst_mem_FP
  have hc := (BinaryFn.ite (hr.le hd) hr hd).of_eq (fun _ => (min_def _ _).symm)
  have ha := ((hA.add (UnaryFn.const 1)).comp pairFst_mem_FP).comp pairFst_mem_FP
  have ht := BinaryFn.ite (FPPred.lt UnaryFn.index ha) hc (BinaryFn.const 0)
  refine (BinaryFn.sum ((hN.add (UnaryFn.const 1)).comp pairFst_mem_FP) ht).of_eq (fun q => ?_)
  simp only [MacaulayBits.loopQuery, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.length_replicate, read, FixedWidthQuery.read_packet, MacaulayBits.fromBits_encode, total]
  apply Finset.sum_congr rfl
  intro i hi
  have hn : i < N (pairFst q) + 1 := Finset.mem_range.mp hi
  simp only [FixedWidthQuery.entry, Function.comp_apply, hn, ite_true, FixedWidthQuery.coordinate,
    rankTarget, BinaryNat.normalize_eq_bits, entry]

theorem evaluator_binary_degree {N A W D : List Bool → ℕ} (hN : UnaryFn N) (hA : UnaryFn A)
    (hW : UnaryFn W) (hD : BinaryFn D) {reader : List Bool → List Bool} (E : SpaceFunction reader) :
    SpaceFunction (value N A W D reader) := by
  have hg := (total_binary hN hA hW hD).eq (hD.comp pairFst_mem_FP)
  have EC := E.precompose (oldQuery W) (oldQuery_mem_FP hW)
  exact (SpaceFunction.branch (fun q => decide (total N A W D q = D (pairFst q))) hg.flag_mem_FP
    EC (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (funext fun q => by simp only [value, decide_eq_true_eq, Function.comp_apply])

end LeanCanny.Algebra.HomogenizationBits
