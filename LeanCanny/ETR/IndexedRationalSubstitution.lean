/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.IndexedExpansionSize
public import LeanCanny.Algebra.IndexedRationalSubstitutionBounds

/-!
# Rational substitution for actual ETR expression trees

The indexed source is constructed from the original arithmetic syntax. Width
twice the syntax degree bound clears every denominator with an even power.
Its evaluation, sign, degree, and coefficient budgets therefore apply directly
to ETR terms, with no assumed expanded polynomial representation.
-/

@[expose] public section

namespace LeanCanny.ETR.Term
open Polynomial
open scoped BigOperators
open LeanCanny.Algebra

noncomputable def clearedRational (t : Term) (A : ℕ) (n d : ℕ → ℤ[X]) : ℤ[X] :=
  RationalSubstitution.Indexed.cleared A t.monomialCount (2 * t.degreeBound)
    t.monomialCoefficient t.monomialExponent n d

theorem exponent_le_clearingWidth (t : Term) (r i : ℕ) : t.monomialExponent r i ≤ 2 * t.degreeBound :=
  (t.monomialExponent_le r i).trans (by omega)

theorem eval₂_clearedRational {K : Type*} [Field K] (t : Term) (A : ℕ) (hA : t.arity ≤ A)
    (n d : ℕ → ℤ[X]) (x : K) (hd : ∀ i, i < A → (d i).eval₂ (Int.castRingHom K) x ≠ 0) :
    (t.clearedRational A n d).eval₂ (Int.castRingHom K) x =
      (∏ i ∈ Finset.range A, (d i).eval₂ (Int.castRingHom K) x ^ (2 * t.degreeBound)) *
        t.eval (fun i => (n i).eval₂ (Int.castRingHom K) x / (d i).eval₂ (Int.castRingHom K) x) := by
  rw [clearedRational, RationalSubstitution.Indexed.eval₂_cleared (Int.castRingHom K) x A t.monomialCount
    (2 * t.degreeBound) t.monomialCoefficient t.monomialExponent n d (fun r _ i _ => t.exponent_le_clearingWidth r i) hd]
  rw [t.eval₂_indexed_source (fun i => (n i).eval₂ (Int.castRingHom K) x / (d i).eval₂ (Int.castRingHom K) x) A hA]

theorem sign_clearedRational (t : Term) (A : ℕ) (hA : t.arity ≤ A) (n d : ℕ → ℤ[X]) (x : ℝ)
    (hd : ∀ i, i < A → (d i).eval₂ (Int.castRingHom ℝ) x ≠ 0) :
    SignType.sign ((t.clearedRational A n d).eval₂ (Int.castRingHom ℝ) x) =
      SignType.sign (t.eval (fun i => (n i).eval₂ (Int.castRingHom ℝ) x / (d i).eval₂ (Int.castRingHom ℝ) x)) := by
  have h := RationalSubstitution.Indexed.sign_eval₂_cleared (Int.castRingHom ℝ) x A t.monomialCount t.degreeBound
    t.monomialCoefficient t.monomialExponent n d (fun r _ i _ => t.exponent_le_clearingWidth r i) hd
  rw [t.eval₂_indexed_source (fun i => (n i).eval₂ (Int.castRingHom ℝ) x / (d i).eval₂ (Int.castRingHom ℝ) x) A hA] at h
  exact h

theorem natDegree_clearedRational_le (t : Term) (A E : ℕ) (n d : ℕ → ℤ[X])
    (hn : ∀ i, i < A → (n i).natDegree ≤ E) (hd : ∀ i, i < A → (d i).natDegree ≤ E) :
    (t.clearedRational A n d).natDegree ≤ A * (2 * t.degreeBound) * E :=
  RationalSubstitution.Indexed.natDegree_cleared_le _ _ _ _ _ _ _ _
    (fun r _ i _ => t.exponent_le_clearingWidth r i) hn hd

theorem coeff_size_clearedRational_le (t : Term) (A b : ℕ) (n d : ℕ → ℤ[X])
    (hn : ∀ i, i < A → coefficientMass (n i) ≤ 2 ^ b)
    (hd : ∀ i, i < A → coefficientMass (d i) ≤ 2 ^ b) (k : ℕ) :
    ((t.clearedRational A n d).coeff k).natAbs.size ≤ 2 * t.toData.size + A * (2 * t.degreeBound) * b + 2 := by
  have h := RationalSubstitution.Indexed.coeff_size_cleared_le A t.monomialCount (2 * t.degreeBound)
    t.toData.size b t.monomialCoefficient t.monomialExponent n d
    (fun r _ i _ => t.exponent_le_clearingWidth r i) (fun r _ => t.monomialCoefficient_natAbs_le_pow_dataSize r) hn hd k
  have hc := t.monomialCount_size_le
  unfold clearedRational
  omega

end LeanCanny.ETR.Term

namespace LeanCanny.ETR.Formula
open LeanCanny.Algebra.RationalSubstitution

theorem satisfiable_iff_indexed_source (p : Formula) :
    p.Satisfiable ↔ ∃ env : ℕ → ℝ,
      (Indexed.source (Term.sumSquares p.equationSystem.terms).arity
        (Term.sumSquares p.equationSystem.terms).monomialCount
        (Term.sumSquares p.equationSystem.terms).monomialCoefficient
        (Term.sumSquares p.equationSystem.terms).monomialExponent).eval₂
          (Int.castRingHom ℝ) (fun i => env i.val) = 0 := by
  rw [p.satisfiable_iff_singleEquation]
  change (∃ env : ℕ → ℝ, (Term.sumSquares p.equationSystem.terms).eval env = 0) ↔ _
  simp only [Term.eval₂_indexed_source _ _ _ le_rfl]

end LeanCanny.ETR.Formula
