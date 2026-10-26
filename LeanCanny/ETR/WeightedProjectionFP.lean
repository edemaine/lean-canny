/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ProjectionCollisionFP

/-! # Native weighted projections and rational-cut formulas -/

@[expose] public section
namespace LeanCanny.ETR.WeightedProjection
open LeanCanny.Encoding.Brackets
open scoped BigOperators

def summand (v : ℕ → ℕ) (i : ℕ) : Term := .mul (.const (v i : ℤ)) (.var i)
def term (n : ℕ) (v : ℕ → ℕ) : Term :=
  TermSum.accumulate ((List.range n).map (summand v)) (.const 0)

private theorem sum_range (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem eval_term (n : ℕ) (v : ℕ → ℕ) (x : ℕ → ℝ) :
    (term n v).eval x = ProjectionCollision.projection n v x := by
  rw [term, TermSum.eval_accumulate]
  simp only [List.map_map, Function.comp_def, summand, Term.eval, Int.cast_zero,
    zero_add, Int.cast_natCast]
  exact sum_range n _

private theorem listBits_wrap (ts : List Term) : SumSquares.listBits ts = wrap (SumSquares.forest ts) := by
  simp only [SumSquares.listBits, SumSquares.forest, Data.toBits_l, List.map_map, Function.comp_def]
  rfl

theorem term_FP {n : List Bool → ℕ} {v : List Bool → ℕ → ℕ} (hn : UnaryFn n)
    (hv : BinaryFn (fun p => v (pairFst p) (pairSnd p).length)) :
    (fun c => (term (n c) (v c)).toData.toBits) ∈ FP := by
  have hs := Codec.taggedTwo_mem_FP 3 (Term.nat_toBits_mem_FP hv)
    (Term.variableBits_mem_FP (UnaryFn.length pairSnd_mem_FP))
  have hs' : (fun p => (summand (v (pairFst p)) (pairSnd p).length).toData.toBits) ∈ FP :=
    mem_FP_of_eq hs (fun _ => by simp only [summand, Term.mul_toBits, Term.variableBits_eq])
  have hf := flatMap_range_mem_FP hs' hn.mem_FP
  have h := mem_FP_comp (mem_FP_comp hf wrap_mem_FP) TermSum.collapse_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, List.length_replicate, pairFst_pair, pairSnd_pair]
  have he : (List.range (n c)).flatMap (fun i => (summand (v c) i).toData.toBits) =
      SumSquares.forest ((List.range (n c)).map (summand (v c))) := by
    simp only [SumSquares.forest, List.map_map, List.flatten_eq_flatMap,
      List.flatMap_map, Function.comp_def, id_eq]
  rw [he, ← listBits_wrap, TermSum.collapse_listBits]
  rfl

def cut (n : ℕ) (v : ℕ → ℕ) (positive negative denominator : ℕ) : Term :=
  .add (.add (.mul (.const (denominator : ℤ)) (term n v)) (.const (negative : ℤ)))
    (.mul (.const (-1)) (.const (positive : ℤ)))

theorem eval_cut (n : ℕ) (v : ℕ → ℕ) (positive negative denominator : ℕ) (x : ℕ → ℝ) :
    (cut n v positive negative denominator).eval x =
      (denominator : ℝ) * ProjectionCollision.projection n v x + negative - positive := by
  simp [cut, Term.eval, eval_term, sub_eq_add_neg]

theorem cut_FP {n : List Bool → ℕ} {v : List Bool → ℕ → ℕ}
    {positive negative denominator : List Bool → ℕ} (hn : UnaryFn n)
    (hv : BinaryFn (fun p => v (pairFst p) (pairSnd p).length))
    (hp : BinaryFn positive) (hm : BinaryFn negative) (hd : BinaryFn denominator) :
    (fun c => (cut (n c) (v c) (positive c) (negative c) (denominator c)).toData.toBits) ∈ FP := by
  have h := Codec.taggedTwo_mem_FP 2
    (Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 (Term.nat_toBits_mem_FP hd) (term_FP hn hv))
      (Term.nat_toBits_mem_FP hm))
    (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (Term.const (-1)).toData.toBits) (Term.nat_toBits_mem_FP hp))
  exact mem_FP_of_eq h (fun _ => by simp only [cut, Term.add_toBits, Term.mul_toBits])

end LeanCanny.ETR.WeightedProjection
