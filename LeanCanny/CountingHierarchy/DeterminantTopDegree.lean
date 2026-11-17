/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! # Stability of the top degree of a polynomial determinant -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial
open scoped Classical BigOperators

variable {A σ κ : Type*} [CommRing A]

private theorem product_degree_le (s : Finset κ) (f : κ → MvPolynomial σ A)
    (d : ℕ) (hf : ∀ i ∈ s, (f i).totalDegree ≤ d) :
    (∏ i ∈ s, f i).totalDegree ≤ s.card * d := by
  apply (totalDegree_finsetProd _ _).trans
  exact (Finset.sum_le_sum hf).trans_eq (by simp)

/-- Perturbing each factor below degree `d` changes a nonempty product
 only below its maximal possible degree. -/
theorem product_difference_degree_lt (s : Finset κ) (hs : s.Nonempty)
    (f g : κ → MvPolynomial σ A) (d : ℕ)
    (hf : ∀ i ∈ s, (f i).totalDegree ≤ d)
    (hg : ∀ i ∈ s, (g i).totalDegree ≤ d)
    (hd : ∀ i ∈ s, (f i - g i).totalDegree < d) :
    ((∏ i ∈ s, f i) - ∏ i ∈ s, g i).totalDegree < s.card * d := by
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hga := hg a (Finset.mem_insert_self _ _)
    have hda := hd a (Finset.mem_insert_self _ _)
    have hf' : ∀ i ∈ s, (f i).totalDegree ≤ d := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' : ∀ i ∈ s, (g i).totalDegree ≤ d := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hd' : ∀ i ∈ s, (f i - g i).totalDegree < d := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    by_cases hs0 : s = ∅
    · subst s
      simpa using hda
    · have hsub := ih (Finset.nonempty_iff_ne_empty.mpr hs0) hf' hg' hd'
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
        Nat.add_mul, one_mul]
      have heq : f a * (∏ i ∈ s, f i) - g a * (∏ i ∈ s, g i) =
          (f a - g a) * (∏ i ∈ s, f i) +
            g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) := by ring
      rw [heq]
      apply (totalDegree_add _ _).trans_lt
      apply max_lt_iff.mpr
      constructor
      · have hm := totalDegree_mul (f a - g a) (∏ i ∈ s, f i)
        have hp := product_degree_le s f d hf'
        omega
      · have hm := totalDegree_mul (g a) ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)
        omega

/-- A uniform degree bound for determinants over any commutative ring. -/
theorem polynomial_det_degree_le {n : ℕ} (M : Matrix (Fin n) (Fin n) (MvPolynomial σ A))
    (d : ℕ) (hM : ∀ i j, (M i j).totalDegree ≤ d) : M.det.totalDegree ≤ n * d := by
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro π _
  apply (totalDegree_smul_le _ _).trans
  simpa using product_degree_le Finset.univ (fun j => M (π j) j) d (fun j _ => hM (π j) j)

/-- Lower-degree changes to matrix entries preserve all coefficients at
 the maximal determinant degree. -/
theorem polynomial_det_top_coefficient {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) (MvPolynomial σ A))
    (d : ℕ) (hM : ∀ i j, (M i j).totalDegree ≤ d)
    (hN : ∀ i j, (N i j).totalDegree ≤ d)
    (hd : ∀ i j, (M i j - N i j).totalDegree < d)
    (e : σ →₀ ℕ) (he : n * d ≤ e.degree) : M.det.coeff e = N.det.coeff e := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hpos : 0 < n * d := by
      have hdpos := hd ⟨0, by omega⟩ ⟨0, by omega⟩
      exact Nat.mul_pos (by omega) (by omega)
    have hdeg : (M.det - N.det).totalDegree < n * d := by
      rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
      apply lt_of_le_of_lt (totalDegree_finsetSum_le (d := n * d - 1) ?_) (by omega)
      intro π _
      rw [← smul_sub]
      apply (totalDegree_smul_le _ _).trans
      have hb := product_difference_degree_lt Finset.univ
        (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
        (fun j => M (π j) j) (fun j => N (π j) j) d
        (fun j _ => hM (π j) j) (fun j _ => hN (π j) j) (fun j _ => hd (π j) j)
      simp only [Finset.card_univ, Fintype.card_fin] at hb
      omega
    have hz := coeff_eq_zero_of_totalDegree_lt (hdeg.trans_le he)
    simpa only [coeff_sub, sub_eq_zero] using hz

end LeanCanny.CountingHierarchy
