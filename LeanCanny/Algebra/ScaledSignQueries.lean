/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integer product queries recover sign-pattern counts

For each requested sign, a quadratic polynomial on `{-1,0,1}` is twice its
indicator. Expanding the product of these local indicators expresses `2^k`
times a sign-pattern count as an integer combination of `3^k` product sign
queries. This identity introduces neither rational denominators nor a choice
of matrix rows. It specifies a counting stage, not an algorithm for evaluating
the underlying sign queries or the full BKR workspace bound.
-/

@[expose] public section

namespace LeanCanny.Algebra.RootSignQueries
open Polynomial
open scoped BigOperators

def weight (s : SignType) (e : Fin 3) : ℤ :=
  match s, e.val with
  | .zero, 0 => 2
  | .zero, 2 => -2
  | .neg, 1 => -1
  | .neg, 2 => 1
  | .pos, 1 => 1
  | .pos, 2 => 1
  | _, _ => 0

theorem weight_indicator (s t : SignType) :
    (∑ e : Fin 3, weight s e * (t : ℤ) ^ e.val) = if t = s then 2 else 0 := by
  cases s <;> cases t <;> decide

open scoped Classical

theorem query_count {J : Type*} [Fintype J] : Fintype.card (J → Fin 3) = 3 ^ Fintype.card J := by
  simp only [Fintype.card_fun, Fintype.card_fin]

def patternWeight {J : Type*} [Fintype J] (σ : J → SignType) (e : J → Fin 3) : ℤ := ∏ i, weight (σ i) (e i)

theorem product_indicator {J : Type*} [Fintype J] (σ t : J → SignType) :
    (∑ e : J → Fin 3, patternWeight σ e * ∏ i, (t i : ℤ) ^ (e i).val) =
      if t = σ then 2 ^ Fintype.card J else 0 := by
  classical
  calc
    _ = ∑ e : J → Fin 3, ∏ i, weight (σ i) (e i) * (t i : ℤ) ^ (e i).val := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.prod_mul_distrib]
      rfl
    _ = ∏ i, ∑ e : Fin 3, weight (σ i) e * (t i : ℤ) ^ e.val :=
      (Fintype.prod_sum (fun (i : J) (e : Fin 3) => weight (σ i) e * (t i : ℤ) ^ e.val)).symm
    _ = ∏ i, if t i = σ i then (2 : ℤ) else 0 := by simp only [weight_indicator]
    _ = _ := by
      by_cases h : t = σ
      · subst t
        simp
      · rw [ite_eq_right h]
        obtain ⟨i, hi⟩ : ∃ i, t i ≠ σ i := by simpa only [funext_iff, not_forall] using h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [hi, ↓reduceIte])

noncomputable def signSum (Z : Finset ℝ) (q : ℝ[X]) : ℤ := ∑ x ∈ Z, (SignType.sign (q.eval x) : ℤ)

noncomputable def signCount {J : Type*} (Z : Finset ℝ) (Q : J → ℝ[X]) (σ : J → SignType) : ℕ :=
  (Z.filter fun x => ∀ i, SignType.sign ((Q i).eval x) = σ i).card

noncomputable def queryPolynomial {R : Type*} [CommSemiring R] {J : Type*} [Fintype J]
    (Q : J → R[X]) (e : J → Fin 3) : R[X] := ∏ i, Q i ^ (e i).val

theorem sign_eval_queryPolynomial {J : Type*} [Fintype J] (Q : J → ℝ[X]) (e : J → Fin 3) (x : ℝ) :
    (SignType.sign ((queryPolynomial Q e).eval x) : ℤ) = ∏ i, (SignType.sign ((Q i).eval x) : ℤ) ^ (e i).val := by
  let φ : ℝ →*₀ ℤ := SignType.castHom.comp signHom
  change φ ((queryPolynomial Q e).eval x) = ∏ i, φ ((Q i).eval x) ^ (e i).val
  simp only [queryPolynomial, Polynomial.eval_prod, Polynomial.eval_pow, map_prod, map_pow]

theorem weighted_queries_eq_count {J : Type*} [Fintype J] (Z : Finset ℝ) (Q : J → ℝ[X]) (σ : J → SignType) :
    (∑ e : J → Fin 3, patternWeight σ e * signSum Z (queryPolynomial Q e)) =
      2 ^ Fintype.card J * (signCount Z Q σ : ℤ) := by
  classical
  simp only [signSum, Finset.mul_sum, sign_eval_queryPolynomial]
  rw [Finset.sum_comm]
  simp_rw [product_indicator]
  have heq (x : ℝ) : (fun i => SignType.sign ((Q i).eval x)) = σ ↔ ∀ i, SignType.sign ((Q i).eval x) = σ i := funext_iff
  simp_rw [heq]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, signCount]
  rw [mul_comm]
  congr 1
  apply congrArg (fun s : Finset ℝ => (s.card : ℤ))
  ext x
  simp only [Finset.mem_filter]

noncomputable def tarskiQuery (p q : ℝ[X]) : ℤ := signSum p.roots.toFinset q

noncomputable def scaledRootCount {J : Type*} [Fintype J] (p : ℝ[X]) (Q : J → ℝ[X]) (σ : J → SignType) : ℤ :=
  ∑ e : J → Fin 3, patternWeight σ e * tarskiQuery p (queryPolynomial Q e)

theorem scaledRootCount_eq {J : Type*} [Fintype J] (p : ℝ[X]) (Q : J → ℝ[X]) (σ : J → SignType) :
    scaledRootCount p Q σ = 2 ^ Fintype.card J * (signCount p.roots.toFinset Q σ : ℤ) :=
  weighted_queries_eq_count p.roots.toFinset Q σ

theorem scaledRootCount_zero_left {J : Type*} [Fintype J] (Q : J → ℝ[X]) (σ : J → SignType) :
    scaledRootCount 0 Q σ = 0 := by
  rw [scaledRootCount_eq]
  simp [signCount]

theorem root_signCount_pos {J : Type*} (p : ℝ[X]) (hp : p ≠ 0) (Q : J → ℝ[X]) (σ : J → SignType) :
    0 < signCount p.roots.toFinset Q σ ↔ ∃ x : ℝ, p.eval x = 0 ∧ ∀ i, SignType.sign ((Q i).eval x) = σ i := by
  classical
  simp only [signCount, Finset.card_pos, Finset.Nonempty, Finset.mem_filter, Multiset.mem_toFinset,
    Polynomial.mem_roots hp, Polynomial.IsRoot.def]

theorem scaledRootCount_pos_iff {J : Type*} [Fintype J] (p : ℝ[X]) (hp : p ≠ 0) (Q : J → ℝ[X]) (σ : J → SignType) :
    0 < scaledRootCount p Q σ ↔ ∃ x : ℝ, p.eval x = 0 ∧ ∀ i, SignType.sign ((Q i).eval x) = σ i := by
  rw [scaledRootCount_eq, mul_pos_iff_of_pos_left (by positivity : (0 : ℤ) < 2 ^ Fintype.card J), Int.natCast_pos,
    root_signCount_pos p hp]

end LeanCanny.Algebra.RootSignQueries
