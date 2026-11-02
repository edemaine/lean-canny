/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerBounds
public import LeanCanny.Algebra.IntegralMixedSourceIntegerLookup
public import LeanCanny.Encoding.BoundedRegularLowCoefficient
/-! # Original-only geometry and literal regular-source marked integer plans

The radius occurs in source coefficients, never in the horizon, degree or
scalar width. Huge annihilators and power leaves are charged integer sources.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedIntegerSource (number original degreeBound)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem original_FP : original∈FP := mem_FP_comp (f:=pairFst) (g:=pairFst) pairFst_mem_FP pairFst_mem_FP

def degree (t : List Bool → Term) (context : List Bool) :=
  LeanCanny.Geometry.BoundedZeroSource.powerDegree (t (original context)).toData.size

theorem degree_binary {t : List Bool → Term} (ht : (fun q=>(t q).toData.toBits)∈FP) : BinaryFn (degree t) :=
  BoundedZeroControls.powerDegree_binary
    (BinaryFn.ofUnary ((LeanCanny.Geometry.AuxiliaryCandidateRegularLift.allowance_unary ht).comp original_FP))

noncomputable def parameters {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) :=
  IntegralMixedSourceIntegerPrelude.parameters (fun c=>number n c+3) (degree t)
    (degreeBound hn ht ha) (fun c=>number n c+8)

theorem access {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) : Access (parameters hn ht ha) :=
  IntegralMixedSourceIntegerPrelude.access ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 3))
    (degree_binary ht) (IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound_binary hn ht ha)
    ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8))

noncomputable def spatial (n : List Bool → ℕ) (t : List Bool → Term) (R : List Bool → ℕ) (context : List Bool) :=
  BoundedRegularLowModularTerm.source (BoundedRegularLowCoefficient.readers (number n) (t∘original) R) context

theorem spatial_degree (n : List Bool → ℕ) (t : List Bool → Term) (R : List Bool → ℕ) (context : List Bool) :
    (spatial n t R context).degree=degree t context := by
  simp only [spatial,BoundedRegularLowModularTerm.source,BoundedRegularLowCoefficient.readers,
    BoundedFullWriter.degree,BoundedFullWriter.controls,BoundedSourceWriter.degree,BoundedSourceWriter.size,
    Function.comp_apply,TermView.term_toBits,degree]

theorem source_degree_cap {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool → ℕ) (context : List Bool) (i : ℕ) :
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).degree (pair context (BinaryNatCode.encode i))≤
      2^(parameters hn ht ha).width context := by
  have H:=IntegralMixedAuxiliaryMarkedIntegerSource.degree_le hn ht ha R (pair context (BinaryNatCode.encode i))
  rw [pairFst_pair] at H
  exact H.trans (IntegralMixedSourceIntegerPrelude.bound_cap _ _ _ _ context)

noncomputable def plan {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (R : List Bool → ℕ) :=
  IntegralMixedSourceIntegerPrelude.plan (parameters hn ht ha) (spatial n t R) (spatial_degree n t R)
    (IntegralMixedSourceIntegerPrelude.source_cap _ _ _ _)
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R) (fun c=>number n c+8)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R) (source_degree_cap hn ht ha R)
    (fun context=>by change number n context+8+2≤number n context+8+2+1; omega)

theorem integerOriginal {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :
    IntegralMixedIntegerFamilyBits.Original (parameters hn ht ha)
      (IntegralMixedFramedIntegerBits.polynomial (parameters hn ht ha) (plan hn ht ha R)) :=
  IntegralMixedSourceIntegerPrelude.original (parameters hn ht ha) (access hn ht ha)
    (spatial n t R) (spatial_degree n t R) (IntegralMixedSourceIntegerPrelude.source_cap _ _ _ _)
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R) (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha hR)
    (fun c=>number n c+8) ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8))
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R) (source_degree_cap hn ht ha R)
    (fun context=>by change number n context+8+2≤number n context+8+2+1; omega)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
