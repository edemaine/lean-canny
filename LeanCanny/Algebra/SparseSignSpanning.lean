/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MonomialEvaluationBasis
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import Mathlib.Basic.Sign.Basic

/-! # Sparse moments span functions on a finite set of signatures

Point-separating features generate every function on a finite set. If the
features satisfy x³=x, monomials mentioning only logarithmically many features
suffice. The number of features need not be polynomially bounded.
-/

@[expose] public section
namespace LeanCanny.Algebra.SparseSignSpanning
open Submodule MvPolynomial
open scoped Classical

variable {σ α K : Type*} [Field K] [Fintype α]

theorem single_in_range (v : σ → α → K)
    (hsep : ∀ x y : α, x ≠ y → ∃ i, v i x ≠ v i y) (x : α) :
    ∃ p : MvPolynomial σ K, aeval v p = Pi.single x 1 := by
  let index : ∀ y : α, y ≠ x → σ := fun y hy => Classical.choose (hsep x y (Ne.symm hy))
  have hindex : ∀ y hy, v (index y hy) x ≠ v (index y hy) y :=
    fun y hy => Classical.choose_spec (hsep x y (Ne.symm hy))
  let factor : α → MvPolynomial σ K := fun y =>
    if hy : y = x then 1 else
      C ((v (index y hy) x - v (index y hy) y)⁻¹) * (X (index y hy) - C (v (index y hy) y))
  refine ⟨∏ y, factor y, ?_⟩
  funext z
  simp only [map_prod, Finset.prod_apply]
  by_cases hz : z = x
  · subst z
    rw [Pi.single_eq_same]
    apply Finset.prod_eq_one
    intro y _
    by_cases hy : y = x
    · simp [factor, hy]
    · simp only [factor, dite_eq_right hy, map_mul, map_sub, aeval_C, aeval_X,
        Pi.mul_apply, Pi.sub_apply, Pi.algebraMap_apply, Algebra.algebraMap_self]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr (hindex y hy))
  · rw [Pi.single_eq_of_ne hz]
    apply Finset.prod_eq_zero (Finset.mem_univ z)
    simp [factor, hz]

theorem span_eq_top (v : σ → α → K)
    (hsep : ∀ x y : α, x ≠ y → ∃ i, v i x ≠ v i y) :
    span K (Set.range (MonomialEvaluationBasis.vector (aeval (R := K) v))) = ⊤ := by
  apply top_unique
  intro f _
  have hs : ∀ x : α, (Pi.single x 1 : α → K) ∈
      span K (Set.range (MonomialEvaluationBasis.vector (aeval (R := K) v))) := by
    intro x
    obtain ⟨p, hp⟩ := single_in_range v hsep x
    rw [← hp]
    exact MonomialEvaluationBasis.image_mem_span _ p
  have he : f = ∑ x : α, f x • (Pi.single x 1 : α → K) := by
    ext y
    simp [Pi.single_apply, smul_eq_mul]
  rw [he]
  exact sum_mem (fun x _ => smul_mem _ _ (hs x))

theorem sparse_span_eq_top (m : MonomialOrder σ) (v : σ → α → K) (w : ℕ)
    (hcard : Fintype.card α ≤ 2 ^ w)
    (hsep : ∀ x y : α, x ≠ y → ∃ i, v i x ≠ v i y)
    (hcube : ∀ i x, v i x ^ 3 = v i x) :
    span K (MonomialEvaluationBasis.vector (aeval (R := K) v) ''
      {d | d.support.card ≤ w ∧ ∀ i, d i ≤ 2}) = ⊤ := by
  rw [← MonomialEvaluationBasis.sparse_span m (aeval (R := K) v) w ?_ ?_]
  · exact span_eq_top v hsep
  · simpa only [Module.finrank_fintype_fun_eq_card] using hcard
  · intro i
    ext x
    simp only [aeval_X, Pi.pow_apply]
    exact hcube i x

theorem signatures_span (m : MonomialOrder σ) (s : α → σ → SignType)
    (hs : Function.Injective s) (w : ℕ) (hcard : Fintype.card α ≤ 2 ^ w) :
    span ℚ (MonomialEvaluationBasis.vector (aeval (R := ℚ) (fun i x => (s x i : ℚ))) ''
      {d | d.support.card ≤ w ∧ ∀ i, d i ≤ 2}) = ⊤ := by
  have hi : Function.Injective (fun a : SignType => (a : ℚ)) := by
    intro a b h
    cases a <;> cases b <;> first | rfl | norm_num [SignType.cast] at h
  apply sparse_span_eq_top m _ w hcard
  · intro x y hxy
    by_contra! he
    exact hxy (hs (funext (fun i => hi (he i))))
  · intro i x
    cases s x i <;> norm_num [SignType.cast]

end LeanCanny.Algebra.SparseSignSpanning
