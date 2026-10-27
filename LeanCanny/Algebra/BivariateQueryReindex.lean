/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BivariateQueryProductBounds

/-! # Reindexing native bivariate families

An FP context reader preserves all coefficient certificates and binary bounds.
The factor index and the two coefficient indices are passed through unchanged.
-/

@[expose] public section
namespace LeanCanny.Algebra.BivariateQueryProductBits
open LeanCanny.Encoding LeanCanny.Computation

noncomputable def Family.comp (F : Family) (read : List Bool → List Bool) : Family where
  polynomial c := F.polynomial (read c)
  exponent c := F.exponent (read c)
  count c := F.count (read c)
  degree c := F.degree (read c)
  parameterDegree c := F.parameterDegree (read c)
  mass c := F.mass (read c)
  polynomial_degree c := F.polynomial_degree (read c)
  coefficient_degree c := F.coefficient_degree (read c)
  coefficient_mass c := F.coefficient_mass (read c)

def reindexQuery (read : List Bool → List Bool) (z : List Bool) : List Bool :=
  pair (pair (pair (read (pairFst (pairFst (pairFst z)))) (pairSnd (pairFst (pairFst z))))
    (pairSnd (pairFst z))) (pairSnd z)

theorem reindexQuery_FP (read : List Bool → List Bool) (hr : read ∈ FP) : reindexQuery read ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP) hr
  have hi := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair hc hi) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def Access.comp {F : Family} (A : Access F) (read : List Bool → List Bool) (hr : read ∈ FP) :
    Access (F.comp read) where
  reader := {
    coefficient := A.reader.coefficient ∘ reindexQuery read
    evaluator := A.reader.evaluator.precompose (reindexQuery read) (reindexQuery_FP read hr)
    coefficient_eq q u v := by
      simp only [Function.comp_apply, reindexQuery, pairFst_pair, pairSnd_pair]
      rw [A.reader.coefficient_eq]
      exact congrArg₂ (fun (a : ℤ) (m : ℕ) => MatrixPower.residueBits (a : ZMod m))
        (by simp only [Family.comp, pairFst_pair, pairSnd_pair])
        (by rw [pairSnd_pair]) }
  exponent := fun z => A.exponent (pair (read (pairFst z)) (pairSnd z))
  exponent_eq c i := by
    simp only [pairFst_pair, pairSnd_pair, Family.comp]
    exact A.exponent_eq (read c) i
  exponent_FP := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hr) pairSnd_mem_FP) A.exponent_FP
  count_binary := A.count_binary.comp hr
  degree_binary := A.degree_binary.comp hr
  parameterDegree_binary := A.parameterDegree_binary.comp hr
  mass_binary := A.mass_binary.comp hr

end LeanCanny.Algebra.BivariateQueryProductBits
