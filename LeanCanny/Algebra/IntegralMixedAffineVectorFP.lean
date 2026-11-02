/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalExpressionArity
public import LeanCanny.ETR.TermSumFP
/-! # Native serialization of finite affine sums from original syntax entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedAffineCode
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Encoding.Brackets
open IntegralMixedHistory
open FlatAffineExceptionalMixedExpressions (sum)
set_option backward.isDefEq.respectTransparency false

def reversePacket (N : List Bool → ℕ) (p : List Bool) :=
  pair (pairFst p) (List.replicate (N (pairFst p) - 1 - (pairSnd p).length) true)

theorem reversePacket_FP (N : List Bool → ℕ) (hN : UnaryFn N) : reversePacket N ∈ FP :=
  mem_FP_pair pairFst_mem_FP ((((hN.comp pairFst_mem_FP).sub (UnaryFn.const 1)).sub (UnaryFn.length pairSnd_mem_FP)).replicate_mem_FP true)

def sumCode (N : List Bool → ℕ) (E : List Bool → List Bool) (q : List Bool) :=
  ETR.TermSum.collapse (wrap ((List.range (N q)).flatMap fun j => E (pair q (List.replicate (N q - 1 - j) true))))

theorem sumCode_FP (N : List Bool → ℕ) (E : List Bool → List Bool) (hN : UnaryFn N) (hE : E ∈ FP) : sumCode N E ∈ FP := by
  have HE := mem_FP_comp (f := reversePacket N) (g := E) (reversePacket_FP N hN) hE
  have HF := flatMap_range_mem_FP HE (hN.replicate_mem_FP true)
  have HW := mem_FP_comp HF wrap_mem_FP
  have HC := mem_FP_comp HW ETR.TermSum.collapse_mem_FP
  exact mem_FP_of_eq HC (fun q => by simp only [sumCode, Function.comp_apply, reversePacket, pairFst_pair, pairSnd_pair, List.length_replicate])

theorem term_sum (xs : List AffineExpr) : term (sum xs) = (xs.map term).foldr ETR.Term.add (.const 0) := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    change ETR.Term.add (term e) (term (sum xs)) = ETR.Term.add (term e) ((xs.map term).foldr ETR.Term.add (.const 0))
    rw [ih]

theorem sumCode_eq (N : List Bool → ℕ) (e : (q : List Bool) → Fin (N q) → AffineExpr) (E : List Bool → List Bool)
    (he : ∀ q j (hj : j < N q), E (pair q (List.replicate j true)) = encode (e q ⟨j, hj⟩)) (q : List Bool) :
    sumCode N E q = encode (sum (List.ofFn (e q))) := by
  have HL : (List.range (N q)).map (fun j => E (pair q (List.replicate (N q - 1 - j) true))) =
      ((List.ofFn (fun i => term (e q i))).reverse.map (fun t => t.toData.toBits)) := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_reverse, List.length_ofFn]
    · intro j hj hj'
      have HJ : j < N q := by simpa only [List.length_map, List.length_range] using hj
      simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_ofFn, List.getElem_ofFn]
      exact he q _ (by omega)
  have HF := congrArg List.flatten HL
  change (List.range (N q)).flatMap (fun j => E (pair q (List.replicate (N q - 1 - j) true))) =
    ETR.SumSquares.forest ((List.ofFn (fun i => term (e q i))).reverse) at HF
  unfold sumCode
  rw [HF]
  have HW (ts : List ETR.Term) : wrap (ETR.SumSquares.forest ts) = ETR.SumSquares.listBits ts := by
    simp only [ETR.SumSquares.forest, ETR.SumSquares.listBits, Data.toBits_l, wrap, List.map_map, Function.comp_def]
  rw [HW, ETR.TermSum.collapse_listBits]
  unfold encode
  apply congrArg (fun t : ETR.Term => t.toData.toBits)
  rw [term_sum, List.map_ofFn, List.foldr_eq_foldl_reverse]
  rfl
end LeanCanny.Algebra.IntegralMixedAffineCode
