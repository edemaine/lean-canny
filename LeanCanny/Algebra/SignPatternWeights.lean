/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignPatternSource
public import LeanCanny.Algebra.IntegerSmallProductSpace
import Mathlib.Tactic.FinCases

/-! # Certified signed pattern weights for ternary queries -/

@[expose] public section

namespace LeanCanny.Algebra.SignPatternBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation

def weightWord (p : List Bool) : List Bool :=
  if pairFst p = [] then
    if pairSnd p = [] then SignStatisticBits.integerCode 2
    else if pairSnd p = [false, true] then SignStatisticBits.integerCode (-2) else SignStatisticBits.integerCode 0
  else if pairFst p = [true] then
    if pairSnd p = [true] then SignStatisticBits.integerCode (-1)
    else if pairSnd p = [false, true] then SignStatisticBits.integerCode 1 else SignStatisticBits.integerCode 0
  else if pairSnd p = [true] ∨ pairSnd p = [false, true] then SignStatisticBits.integerCode 1
  else SignStatisticBits.integerCode 0

theorem weightWord_mem_FP : weightWord ∈ FP := by
  have h0 := stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [])
  have h1 := stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true])
  have h2 := stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [false, true])
  have hz := h0.ite_mem_FP (constFn_mem_FP (SignStatisticBits.integerCode 2))
    (h2.ite_mem_FP (constFn_mem_FP (SignStatisticBits.integerCode (-2))) (constFn_mem_FP (SignStatisticBits.integerCode 0)))
  have hn := h1.ite_mem_FP (constFn_mem_FP (SignStatisticBits.integerCode (-1)))
    (h2.ite_mem_FP (constFn_mem_FP (SignStatisticBits.integerCode 1)) (constFn_mem_FP (SignStatisticBits.integerCode 0)))
  have hp := (h1.or h2).ite_mem_FP (constFn_mem_FP (SignStatisticBits.integerCode 1)) (constFn_mem_FP (SignStatisticBits.integerCode 0))
  have h := (stringEq_fppred pairFst_mem_FP (constFn_mem_FP [])).ite_mem_FP hz
    ((stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).ite_mem_FP hn hp)
  refine mem_FP_of_eq (g := weightWord) h ?_
  intro p
  simp only [weightWord]

theorem weightWord_codes (s : SignType) (e : Fin 3) :
    weightWord (pair (InfinitesimalSign.encode s) (BinaryNatCode.encode e.val)) =
      SignStatisticBits.integerCode (RootSignQueries.weight s e) := by
  cases s <;> fin_cases e <;> rfl

theorem weight_abs_le (s : SignType) (e : Fin 3) : (RootSignQueries.weight s e).natAbs ≤ 2 := by
  cases s <;> fin_cases e <;> decide

def patternQuery (p : List Bool) : List Bool := pair (original p) (pairSnd p)
theorem patternQuery_mem_FP : patternQuery ∈ FP := mem_FP_pair original_mem_FP pairSnd_mem_FP

def factor {F : Family} (a : Access F) (p : List Bool) : List Bool :=
  weightWord (pair (a.pattern (patternQuery p)) ((queryAccess a).exponent p))

theorem factor_mem_FP {F : Family} (a : Access F) (hF : ControlsPolyTime F) (hs : a.pattern ∈ FP) : factor a ∈ FP := by
  have hp := mem_FP_comp patternQuery_mem_FP hs
  have he := queryExponent_mem_FP a hF
  have h := mem_FP_comp (mem_FP_pair hp he) weightWord_mem_FP
  refine mem_FP_of_eq (g := factor a) h ?_
  intro p
  simp only [factor, Function.comp_apply]

theorem factor_packet {F : Family} (a : Access F) (q : List Bool) (i : ℕ) :
    factor a (pair q (BinaryNatCode.encode i)) = SignStatisticBits.integerCode
      (RootSignQueries.weight (F.pattern (pairFst q) i)
        (Ternary.exponent (Nat.fromBitsLE (F.count (pairFst q))) (Nat.fromBitsLE (pairSnd q)) i)) := by
  simp only [factor, patternQuery, original, queryIndex, queryAccess, pairFst_pair, pairSnd_pair,
    a.pattern_eq, Ternary.digit_exponent]
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using weightWord_codes (F.pattern (pairFst q) i)
    (Ternary.exponent (Nat.fromBitsLE (F.count (pairFst q))) (Nat.fromBitsLE (pairSnd q)) i)

noncomputable def weightEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F) (hs : a.pattern ∈ FP) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (weight F q)) := by
  have hc := mem_FP_comp pairFst_mem_FP hF.count
  have hu := hF.countUnary.comp pairFst_mem_FP
  let E := IntegerSmallProductBits.evaluator (SpaceFunction.ofFP (factor a) (factor_mem_FP a hF hs))
    (F.count ∘ pairFst) hc hu
    (fun q i => RootSignQueries.weight (F.pattern (pairFst q) i)
      (Ternary.exponent (Nat.fromBitsLE (F.count (pairFst q))) (Nat.fromBitsLE (pairSnd q)) i))
    (factor_packet a) (fun q i => weight_abs_le _ _)
  refine E.congr (funext fun q => ?_)
  rfl

end LeanCanny.Algebra.SignPatternBits
