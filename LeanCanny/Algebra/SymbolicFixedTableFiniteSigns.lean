/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableFiniteWith
public import LeanCanny.Algebra.RationalSubstitutionSignWith

/-! # Exact sign filtering with the actual integer-prepared symbolic table -/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicFixedTableFinite.Family
open Polynomial SymbolicScaledSquarefree
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def signQueryWith (F : Family) (D : Fin F.count → ℕ)
    (q : MvPolynomial (Fin F.count) Coefficient) : Polynomial Coefficient :=
  RationalSubstitution.clearedWith D q (fun i => (F.fixedCoordinate i).numerator)
    (fun i => (F.fixedCoordinate i).denominator)

theorem signQueryWith_eval (F : Family) (D : Fin F.count → ℕ)
    (q : MvPolynomial (Fin F.count) Coefficient) (hD : ∀ i, q.degreeOf i ≤ D i)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic F.exponent)
    (theta : ℝ) (ht : F.parameter.eval₂ (scalarEvaluation beta) theta = 0) :
    SignType.sign ((F.signQueryWith D q).eval₂ (scalarEvaluation beta) theta) =
      SignType.sign (q.eval₂ (scalarEvaluation beta) (F.decode beta theta)) := by
  rw [signQueryWith, RationalSubstitution.sign_eval₂_clearedWith (scalarEvaluation beta) theta D q _ _ hD
    (fun i => (F.fixedCoordinate_spec beta hb he theta ht i).1)]
  congr 1
  apply congrArg (q.eval₂ (scalarEvaluation beta))
  funext i
  exact (F.fixedCoordinate_spec beta hb he theta ht i).2

/-- Any acceptance predicate on the query signs, including combinations of
zero and nonpositive tests, transfers to the one prepared primitive root. -/
theorem predicate_realizable_iff (F : Family) {ι : Type*} (D : Fin F.count → ℕ)
    (q : ι → MvPolynomial (Fin F.count) Coefficient) (hD : ∀ j i, (q j).degreeOf i ≤ D i)
    (accept : (ι → SignType) → Prop)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic F.exponent) :
    (∃ x : Fin F.count → ℝ, (∀ i, (F.polynomial i.val).eval₂ (scalarEvaluation beta) (x i) = 0) ∧
      accept (fun j => SignType.sign ((q j).eval₂ (scalarEvaluation beta) x))) ↔
    ∃ theta : ℝ, F.parameter.eval₂ (scalarEvaluation beta) theta = 0 ∧
      accept (fun j => SignType.sign ((F.signQueryWith D (q j)).eval₂ (scalarEvaluation beta) theta)) := by
  constructor
  · rintro ⟨x, hx, haccept⟩
    obtain ⟨ht, hdecode⟩ := F.encode_roots beta hb he x hx
    refine ⟨F.encode x, ht, ?_⟩
    have hs : (fun j => SignType.sign ((F.signQueryWith D (q j)).eval₂ (scalarEvaluation beta) (F.encode x))) =
        (fun j => SignType.sign ((q j).eval₂ (scalarEvaluation beta) x)) := by
      funext j
      rw [F.signQueryWith_eval D (q j) (hD j) beta hb he _ ht, hdecode]
    rwa [hs]
  · rintro ⟨theta, ht, haccept⟩
    refine ⟨F.decode beta theta, F.decode_root beta hb he theta ht, ?_⟩
    have hs : (fun j => SignType.sign ((F.signQueryWith D (q j)).eval₂ (scalarEvaluation beta) theta)) =
        (fun j => SignType.sign ((q j).eval₂ (scalarEvaluation beta) (F.decode beta theta))) := by
      funext j
      exact F.signQueryWith_eval D (q j) (hD j) beta hb he theta ht
    rwa [hs] at haccept

end LeanCanny.Algebra.SymbolicFixedTableFinite.Family
