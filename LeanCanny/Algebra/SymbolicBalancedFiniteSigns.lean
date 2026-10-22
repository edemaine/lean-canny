/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicBalancedFiniteCoordinates
public import LeanCanny.Algebra.RationalSubstitution
public import LeanCanny.Algebra.RationalSubstitutionSignWith

/-! # Symbolic sign filtering of the original finite root product

The actual rational coordinate formulas clear each query with even powers
of its coordinate denominators. Below the internally computed leaf/pair
threshold, sign realizability on original root tuples is exactly sign
realizability at the single constructed primitive root.
-/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicBalancedFinite
open Polynomial SymbolicScaledSquarefree
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ → Polynomial Coefficient) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)

noncomputable def signQuery (q : MvPolynomial (Fin n) Coefficient) : Polynomial Coefficient :=
  RationalSubstitution.cleared q (fun i => (coordinate p n hp i).numerator)
    (fun i => (coordinate p n hp i).denominator)

theorem signQuery_eval (q : MvPolynomial (Fin n) Coefficient)
    (b : ℕ → ℕ) (hm : ∀ i < n, ∀ k, coefficientMass ((p i).coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (exponent p n hp b))
    (theta : ℝ) (ht : (parameter p n hp).eval₂ (scalarEvaluation beta) theta = 0) :
    SignType.sign ((signQuery p n hp q).eval₂ (scalarEvaluation beta) theta) =
      SignType.sign (q.eval₂ (scalarEvaluation beta) (decode p n hp beta theta)) := by
  rw [signQuery, RationalSubstitution.sign_eval₂_cleared (scalarEvaluation beta) theta q _ _
    (fun i => (coordinate_spec p n hp b hm beta hb he theta ht i).1)]
  congr 1
  apply congrArg (q.eval₂ (scalarEvaluation beta))
  funext i
  exact (coordinate_spec p n hp b hm beta hb he theta ht i).2

/-- Exact sign-pattern filtering, with all coordinates referring to the
original leaf polynomials. -/
theorem signs_realizable_iff {ι : Type*} (q : ι → MvPolynomial (Fin n) Coefficient)
    (sgn : ι → SignType)
    (b : ℕ → ℕ) (hm : ∀ i < n, ∀ k, coefficientMass ((p i).coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (exponent p n hp b)) :
    (∃ x : Fin n → ℝ, (∀ i, (p i.val).eval₂ (scalarEvaluation beta) (x i) = 0) ∧
      ∀ j, SignType.sign ((q j).eval₂ (scalarEvaluation beta) x) = sgn j) ↔
    ∃ theta : ℝ, (parameter p n hp).eval₂ (scalarEvaluation beta) theta = 0 ∧
      ∀ j, SignType.sign ((signQuery p n hp (q j)).eval₂ (scalarEvaluation beta) theta) = sgn j := by
  constructor
  · rintro ⟨x, hx, hsign⟩
    obtain ⟨ht, hdecode⟩ := encode_roots p n hp b hm beta hb he x hx
    refine ⟨encode p n hp x, ht, ?_⟩
    intro j
    rw [signQuery_eval p n hp (q j) b hm beta hb he _ ht, hdecode]
    exact hsign j
  · rintro ⟨theta, ht, hsign⟩
    refine ⟨decode p n hp beta theta, fun i => decode_root p n hp b hm beta hb he theta ht i, ?_⟩
    intro j
    rw [← signQuery_eval p n hp (q j) b hm beta hb he theta ht]
    exact hsign j

/-- Uniform supplied degree allowances can be streamed without recomputing
exact query degrees. -/
noncomputable def signQueryWith (D : Fin n → ℕ) (q : MvPolynomial (Fin n) Coefficient) : Polynomial Coefficient :=
  RationalSubstitution.clearedWith D q (fun i => (coordinate p n hp i).numerator)
    (fun i => (coordinate p n hp i).denominator)

theorem signQueryWith_eval (D : Fin n → ℕ) (q : MvPolynomial (Fin n) Coefficient)
    (hD : ∀ i, q.degreeOf i ≤ D i)
    (b : ℕ → ℕ) (hm : ∀ i < n, ∀ k, coefficientMass ((p i).coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (exponent p n hp b))
    (theta : ℝ) (ht : (parameter p n hp).eval₂ (scalarEvaluation beta) theta = 0) :
    SignType.sign ((signQueryWith p n hp D q).eval₂ (scalarEvaluation beta) theta) =
      SignType.sign (q.eval₂ (scalarEvaluation beta) (decode p n hp beta theta)) := by
  rw [signQueryWith, RationalSubstitution.sign_eval₂_clearedWith (scalarEvaluation beta) theta D q _ _ hD
    (fun i => (coordinate_spec p n hp b hm beta hb he theta ht i).1)]
  congr 1
  apply congrArg (q.eval₂ (scalarEvaluation beta))
  funext i
  exact (coordinate_spec p n hp b hm beta hb he theta ht i).2

theorem signsWith_realizable_iff {ι : Type*} (D : Fin n → ℕ)
    (q : ι → MvPolynomial (Fin n) Coefficient) (hD : ∀ j i, (q j).degreeOf i ≤ D i)
    (sgn : ι → SignType)
    (b : ℕ → ℕ) (hm : ∀ i < n, ∀ k, coefficientMass ((p i).coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (exponent p n hp b)) :
    (∃ x : Fin n → ℝ, (∀ i, (p i.val).eval₂ (scalarEvaluation beta) (x i) = 0) ∧
      ∀ j, SignType.sign ((q j).eval₂ (scalarEvaluation beta) x) = sgn j) ↔
    ∃ theta : ℝ, (parameter p n hp).eval₂ (scalarEvaluation beta) theta = 0 ∧
      ∀ j, SignType.sign ((signQueryWith p n hp D (q j)).eval₂ (scalarEvaluation beta) theta) = sgn j := by
  constructor
  · rintro ⟨x, hx, hsign⟩
    obtain ⟨ht, hdecode⟩ := encode_roots p n hp b hm beta hb he x hx
    refine ⟨encode p n hp x, ht, ?_⟩
    intro j
    rw [signQueryWith_eval p n hp D (q j) (hD j) b hm beta hb he _ ht, hdecode]
    exact hsign j
  · rintro ⟨theta, ht, hsign⟩
    refine ⟨decode p n hp beta theta, fun i => decode_root p n hp b hm beta hb he theta ht i, ?_⟩
    intro j
    rw [← signQueryWith_eval p n hp D (q j) (hD j) b hm beta hb he theta ht]
    exact hsign j

end LeanCanny.Algebra.SymbolicBalancedFinite
