/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BivariateReaderCanonical
public import LeanCanny.Algebra.SymbolicScaledSquarefree

/-! # Native integer coefficients after zero-parameter specialization -/

@[expose] public section
namespace LeanCanny.Algebra.BivariateAtZeroBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def polynomial (p : List Bool → (ℤ[X])[X]) (c : List Bool) : ℤ[X] :=
  (p c).map Polynomial.constantCoeff

def query (q : List Bool) : List Bool := pair (pair (pairFst (pairFst q)) (pairSnd q))
  (pair [] (pairSnd (pairFst q)))
theorem query_FP : query ∈ FP := by polytime [query]

theorem evaluator {p : List Bool → (ℤ[X])[X]} (A : CertifiedPolynomial.BivariateReader p) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial p)) := by
  refine ((BivariateReaderCanonical.evaluator A).precompose query query_FP).congr (funext fun q => ?_)
  simp only [Function.comp_apply, query, SymbolicFixedTableEntryBits.coefficient,
    PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue,
    pairFst_pair, pairSnd_pair, polynomial, Polynomial.coeff_map]
  rfl

theorem real_eval (p : (ℤ[X])[X]) (x : ℝ) :
    (p.map Polynomial.constantCoeff).eval₂ (Int.castRingHom ℝ) x =
      p.eval₂ (SymbolicScaledSquarefree.scalarEvaluation 0) x := by
  have hphi : (Int.castRingHom ℝ).comp (Polynomial.constantCoeff : ℤ[X] →+* ℤ) =
      SymbolicScaledSquarefree.scalarEvaluation 0 := by
    apply RingHom.ext
    intro q
    change (q.coeff 0 : ℝ) = q.eval₂ (Int.castRingHom ℝ) 0
    rw [Polynomial.eval₂_at_zero]
    rfl
  rw [Polynomial.eval₂_map, hphi]

theorem map_real (p : (ℤ[X])[X]) :
    (p.map Polynomial.constantCoeff).map (Int.castRingHom ℝ) = p.map (SymbolicScaledSquarefree.scalarEvaluation 0) := by
  rw [Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro q
  change (q.coeff 0 : ℝ) = q.eval₂ (Int.castRingHom ℝ) 0
  rw [Polynomial.eval₂_at_zero]
  rfl

end LeanCanny.Algebra.BivariateAtZeroBits
