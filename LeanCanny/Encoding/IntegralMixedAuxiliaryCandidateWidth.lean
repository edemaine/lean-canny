/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateSource
public import LeanCanny.Encoding.IntegralMixedAuxiliaryPositiveNativeSquare
/-! # One original polynomial bounds the vertex width for every advice prefix -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
set_option backward.isDefEq.respectTransparency false

noncomputable def input {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :=
  IntegralMixedAuxiliaryPositivePrefix.input (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
    (IntegralMixedAuxiliaryPreparedRoot.term_FP ht) (fun q => ha (pairFst q)) id

theorem native_access {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    (input hn ht ha).Access :=
  IntegralMixedAuxiliaryPositivePrefix.native_access (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
    (IntegralMixedAuxiliaryPreparedRoot.term_FP ht) (fun q => ha (pairFst q)) id id_mem_FP

noncomputable def actualWidth {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (q : List Bool) :=
  SquareSampleCompleteVertices.width (input hn ht ha) (source n t q)

theorem actualWidth_unary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    UnaryFn (actualWidth hn ht ha) :=
  (SquareSampleCompleteVertices.width_unary (native_access hn ht ha)).comp (source_FP hn ht)

theorem width_polynomial {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    ∃ p : Polynomial ℕ, ∀ q,actualWidth hn ht ha q≤p.eval (pairFst q).length := by
  obtain ⟨r,hr⟩:=source_length_polynomial hn ht
  obtain ⟨p,hp⟩:=output_length_poly_of_mem_FP
    (SquareSampleCompleteVertices.width_unary (native_access hn ht ha)).mem_FP
  refine ⟨p.comp r,fun q => ?_⟩
  have HW : actualWidth hn ht ha q≤p.eval (source n t q).length := by
    simpa only [actualWidth,List.length_replicate] using hp (source n t q)
  simpa only [Polynomial.eval_comp] using HW.trans (p.eval_mono (hr q))

noncomputable def vertexPolynomial {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : Polynomial ℕ :=
  Classical.choose (width_polynomial hn ht ha)

noncomputable def vertexBudget {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) := (vertexPolynomial hn ht ha).eval original.length

theorem polynomial_eval_unary (p : Polynomial ℕ) : UnaryFn (fun q : List Bool => p.eval q.length) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial j r =>
    simpa only [Polynomial.eval_monomial,id_eq] using
      (UnaryFn.const r).mul ((UnaryFn.length id_mem_FP).pow_const j)

theorem vertexBudget_unary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    UnaryFn (vertexBudget hn ht ha) := polynomial_eval_unary _

theorem actualWidth_le_budget {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (q : List Bool) :
    actualWidth hn ht ha q≤vertexBudget hn ht ha (pairFst q) :=
  Classical.choose_spec (width_polynomial hn ht ha) q
end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
