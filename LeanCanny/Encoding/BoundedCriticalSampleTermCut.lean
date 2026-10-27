/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleLineTerm

/-! # Native comparisons with arithmetic values at actual samples

A fresh variable beyond the endpoint term's arity supplies the comparison
coordinate. Rational substitution constructs a polynomial with exactly the
signs of `t - endpoint`. No endpoint coefficients or comparison oracle are
supplied. Malformed endpoint words use the total zero-term view.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleTermCut
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open scoped Classical

def free (read : List Bool → List Bool) (u : List Bool) : ℕ := (TermView.normalize (read u)).length

theorem free_unary (read : List Bool → List Bool) (hr : read ∈ FP) : UnaryFn (free read) :=
  UnaryFn.length (mem_FP_comp hr TermView.normalize_mem_FP)

def cut (read : List Bool → List Bool) (u : List Bool) : List Bool :=
  Codec.taggedTwo 2 (Term.variableBits (free read u))
    (Codec.taggedTwo 3 (Term.const (-1)).toData.toBits (TermView.normalize (read u)))

theorem cut_FP (read : List Bool → List Bool) (hr : read ∈ FP) : cut read ∈ FP :=
  Codec.taggedTwo_mem_FP 2 (Term.variableBits_mem_FP (free_unary read hr))
    (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP _) (mem_FP_comp hr TermView.normalize_mem_FP))

theorem cut_term (read : List Bool → List Bool) (u : List Bool) :
    TermView.term (cut read u) = .add (.var (free read u)) (.mul (.const (-1)) (TermView.term (read u))) := by
  have he : cut read u = (Term.add (.var (free read u)) (.mul (.const (-1)) (TermView.term (read u)))).toData.toBits := by
    simp only [cut, Term.add_toBits, Term.mul_toBits, Term.variableBits_eq, TermView.normalize_eq_term]
  rw [he, TermView.term_toBits]

theorem arity_le_free (read : List Bool → List Bool) (u : List Bool) :
    (TermView.term (read u)).arity ≤ free read u := by
  have H := (TermView.term (read u)).arity_le_dataSize
  simpa only [free, TermView.normalize_eq_term, Data.length_toBits] using H

noncomputable def family (P : Readers) (read : List Bool → List Bool) : BoundedAlgebraicSlice.Family :=
  BoundedCriticalSampleLineTerm.family P (free read) (cut read)

noncomputable def access {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : (family P read).Access :=
  BoundedCriticalSampleLineTerm.access h (BinaryFn.ofUnary (free_unary read hr)) (cut read) (cut_FP read hr) ha

noncomputable def value (P : Readers) (read : List Bool → List Bool) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) : ℝ :=
  (TermView.term (read (pair c r))).eval (Formula.extend x.val)

theorem sign_sample (P : Readers) (read : List Bool → List Bool) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (t : ℝ) :
    SignType.sign (((family P read).slice (pair c r) (BoundedCriticalSampleLabels.parameter P c x).val).eval t) =
      SignType.sign (t - value P read c r x) := by
  rw [family, BoundedCriticalSampleLineTerm.sign_sample, cut_term]
  simp only [Term.eval, Function.update_self, Int.cast_neg, Int.cast_one, neg_one_mul]
  have he := (TermView.term (read (pair c r))).eval_congr
    (Function.update (Formula.extend x.val) (free read (pair c r)) t) (Formula.extend x.val) (fun i hi => by
      have hn : i ≠ free read (pair c r) := by have := arity_le_free read (pair c r); omega
      exact Function.update_of_ne hn t (Formula.extend x.val))
  rw [he]
  rfl

end LeanCanny.Encoding.BoundedCriticalSampleTermCut
