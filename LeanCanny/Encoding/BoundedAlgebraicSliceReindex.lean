/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceOperations

/-! # Reindexing algebraic-slice sources with native query preparation -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice
open LeanCanny.Algebra LeanCanny.Computation Polynomial MatrixPower

def Family.comp (F : Family) (f : List Bool → List Bool) : Family where
  polynomial c := F.polynomial (f c)
  degree c := F.degree (f c)
  parameterDegree c := F.parameterDegree (f c)
  mass c := F.mass (f c)
  polynomial_degree c := F.polynomial_degree (f c)
  coefficient_degree c := F.coefficient_degree (f c)
  coefficient_mass c := F.coefficient_mass (f c)

def readerQuery (f : List Bool → List Bool) (z : List Bool) : List Bool :=
  pair (pair (f (pairFst (pairFst z))) (pairSnd (pairFst z))) (pairSnd z)
theorem readerQuery_FP {f : List Bool → List Bool} (hf : f ∈ FP) : readerQuery f ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hf
  exact mem_FP_pair (mem_FP_pair hc (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

def Family.Access.comp {F : Family} (A : F.Access) (f : List Bool → List Bool) (hf : f ∈ FP) : (F.comp f).Access where
  reader := {
    coefficient := A.reader.coefficient ∘ readerQuery f
    evaluator := A.reader.evaluator.precompose (readerQuery f) (readerQuery_FP hf)
    coefficient_eq q u v := by
      simp only [Function.comp_apply, readerQuery, pairFst_pair, pairSnd_pair]
      have H := A.reader.coefficient_eq (pair (f (pairFst q)) (pairSnd q)) u v
      simp only [pairFst_pair] at H
      refine H.trans ?_
      exact congrArg₂ (fun (a : ℤ) (n : ℕ) => residueBits (a : ZMod n)) rfl (by rw [pairSnd_pair]) }
  degree_binary := A.degree_binary.comp hf
  parameterDegree_binary := A.parameterDegree_binary.comp hf
  mass_binary := A.mass_binary.comp hf

theorem Family.slice_comp (F : Family) (f : List Bool → List Bool) (c : List Bool) (t : ℝ) :
    (F.comp f).slice c t = F.slice (f c) t := rfl

end LeanCanny.Encoding.BoundedAlgebraicSlice
