/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TermSumFP
public import LeanCanny.ETR.NumericLiteralFP
public import LeanCanny.ETR.ComplexPairedQuery

/-! # Native projection-collision formulas

Weights are supplied in binary. The formula states equality of the two
weighted projections and inequality in one specified coordinate. The two
spatial tuples occupy alternating logical variables.
-/

@[expose] public section
namespace LeanCanny.ETR.ProjectionCollision
open LeanCanny.Encoding.Brackets ComplexCircuit.RealQuery.Interleaved
open scoped BigOperators

def difference (i : ℕ) : Term := .add (.var (even i)) (.mul (.const (-1)) (.var (odd i)))
def term (v : ℕ → ℕ) (i : ℕ) : Term := .mul (.const (v i : ℤ)) (difference i)
def terms (n : ℕ) (v : ℕ → ℕ) : List Term := (List.range n).map (term v)
def sum (n : ℕ) (v : ℕ → ℕ) : Term := TermSum.accumulate (terms n v) (.const 0)
def formula (n : ℕ) (v : ℕ → ℕ) (i : ℕ) : Formula :=
  .and (.eqZero (sum n v)) (.not (.eqZero (difference i)))
def projection (n : ℕ) (v : ℕ → ℕ) (x : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range n, (v i : ℝ) * x i

theorem difference_eval (i : ℕ) (x : ℕ → ℝ) :
    (difference i).eval x = x (even i) - x (odd i) := by
  simp [difference, Term.eval, sub_eq_add_neg]

private theorem sum_range (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem sum_eval (n : ℕ) (v : ℕ → ℕ) (x : ℕ → ℝ) :
    (sum n v).eval x = projection n v (x ∘ even) - projection n v (x ∘ odd) := by
  rw [sum, TermSum.eval_accumulate]
  simp only [terms, List.map_map, Function.comp_def, term, Term.eval, Int.cast_zero,
    zero_add, Int.cast_natCast, difference_eval]
  rw [sum_range]
  simp only [mul_sub, Finset.sum_sub_distrib, projection]

theorem formula_holds (n : ℕ) (v : ℕ → ℕ) (i : ℕ) (x : ℕ → ℝ) :
    (formula n v i).Holds x ↔ projection n v (x ∘ even) = projection n v (x ∘ odd) ∧
      x (even i) ≠ x (odd i) := by
  simp only [formula, Formula.Holds, sum_eval, difference_eval, sub_eq_zero]

theorem difference_mem_FP {i : List Bool → ℕ} (hi : UnaryFn i) :
    (fun c => (difference (i c)).toData.toBits) ∈ FP := by
  have he := (UnaryFn.const 2).mul hi
  have ho := he.add (UnaryFn.const 1)
  have h := Codec.taggedTwo_mem_FP 2 (Term.variableBits_mem_FP he)
    (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (Term.const (-1)).toData.toBits) (Term.variableBits_mem_FP ho))
  apply mem_FP_of_eq h
  intro c
  simp only [difference, even, odd, Term.add_toBits, Term.mul_toBits, Term.variableBits_eq]

private theorem listBits_wrap (ts : List Term) :
    SumSquares.listBits ts = wrap (SumSquares.forest ts) := by
  simp only [SumSquares.listBits, SumSquares.forest, Data.toBits_l, List.map_map, Function.comp_def]
  rfl

theorem sum_mem_FP {n : List Bool → ℕ} {v : List Bool → ℕ → ℕ} (hn : UnaryFn n)
    (hv : BinaryFn (fun p => v (pairFst p) (pairSnd p).length)) :
    (fun c => (sum (n c) (v c)).toData.toBits) ∈ FP := by
  have ht := Codec.taggedTwo_mem_FP 3 (Term.nat_toBits_mem_FP hv)
    (difference_mem_FP (UnaryFn.length pairSnd_mem_FP))
  have ht' : (fun p => (term (v (pairFst p)) (pairSnd p).length).toData.toBits) ∈ FP :=
    mem_FP_of_eq ht (fun _ => by simp only [term, Term.mul_toBits])
  have hterms := flatMap_range_mem_FP ht' hn.mem_FP
  have h := mem_FP_comp (mem_FP_comp hterms wrap_mem_FP) TermSum.collapse_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, List.length_replicate, pairFst_pair, pairSnd_pair]
  have he : (List.range (n c)).flatMap (fun i => (term (v c) i).toData.toBits) =
      SumSquares.forest (terms (n c) (v c)) := by
    simp only [terms, SumSquares.forest, List.map_map, List.flatten_eq_flatMap,
      List.flatMap_map, Function.comp_def, id_eq]
  rw [he, ← listBits_wrap, TermSum.collapse_listBits]
  rfl

theorem formula_mem_FP {n i : List Bool → ℕ} {v : List Bool → ℕ → ℕ}
    (hn : UnaryFn n) (hi : UnaryFn i) (hv : BinaryFn (fun p => v (pairFst p) (pairSnd p).length)) :
    (fun c => (formula (n c) (v c) (i c)).encode) ∈ FP := by
  have h := Codec.taggedTwo_mem_FP 4 (Codec.taggedOne_mem_FP 1 (sum_mem_FP hn hv))
    (Codec.taggedOne_mem_FP 3 (Codec.taggedOne_mem_FP 1 (difference_mem_FP hi)))
  apply mem_FP_of_eq h
  intro c
  simp only [formula, Formula.encode, Formula.toData, Codec.taggedOne_toBits, Codec.taggedTwo_toBits]

end LeanCanny.ETR.ProjectionCollision
