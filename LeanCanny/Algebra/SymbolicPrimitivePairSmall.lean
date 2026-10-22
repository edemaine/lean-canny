/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicPrimitivePairSpecialization
public import LeanCanny.Algebra.SymbolicPrimitivePairCoordinateBounds

/-! # A computed ordinary-specialization interval for symbolic primitive pairs -/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicPrimitivePair
open Polynomial SymbolicScaledSquarefree
open scoped Classical

theorem discriminant_ne_zero (p : SeparablePolynomial) : discriminant p.polynomial ≠ 0 := by
  have h := (separable_iff_discriminant _ p.separable.ne_zero).mp p.separable
  rw [← discriminant_map embedding _
    (natDegree_map_eq_of_injective embedding_injective _)
    (natDegree_map_eq_of_injective embedding_injective _)] at h
  exact fun hz => h (by rw [hz, map_zero])

private theorem eval_ne_zero_of_small (q : ℤ[X]) (hq : q ≠ 0) (b s : ℕ)
    (hm : coefficientMass q ≤ 2 ^ b) (hs : b < s)
    (beta : ℝ) (hb : 0 < beta) (hbs : beta ≤ InfinitesimalSign.dyadic s) :
    scalarEvaluation beta q ≠ 0 := by
  have he := InfinitesimalSign.integer_sign_eval_le_dyadic q b s hm hs beta hb hbs
  intro hz
  change SignType.sign (scalarEvaluation beta q) = _ at he
  rw [hz, sign_zero] at he
  exact (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hq) (sign_eq_zero_iff.mp he.symm)

theorem small_data (p : SeparablePolynomial) (b s : ℕ)
    (hm : ∀ k, coefficientMass (p.polynomial.coeff k) ≤ 2 ^ b)
    (hb : b < s) (hd : gcdMassExponent p.polynomial.natDegree b < s)
    (beta : ℝ) (hbeta : 0 < beta) (hbs : beta ≤ InfinitesimalSign.dyadic s) :
    (p.polynomial.map (scalarEvaluation beta)).natDegree = p.polynomial.natDegree ∧
      (p.polynomial.map (scalarEvaluation beta)).Separable := by
  have hlc := eval_ne_zero_of_small p.polynomial.leadingCoeff (leadingCoeff_ne_zero.mpr p.ne_zero)
    b s (hm p.polynomial.natDegree) hb beta hbeta hbs
  have hdisc := eval_ne_zero_of_small (discriminant p.polynomial) (discriminant_ne_zero p)
    _ s (discriminant_mass p.polynomial b hm) hd beta hbeta hbs
  have hdeg : (p.polynomial.map (scalarEvaluation beta)).natDegree = p.polynomial.natDegree :=
    natDegree_map_eq_iff.mpr (Or.inl hlc)
  refine ⟨hdeg, (separable_iff_discriminant _ ?_).mpr ?_⟩
  · intro hz
    have h := congrArg (fun q : ℝ[X] => q.coeff p.polynomial.natDegree) hz
    rw [coeff_map, coeff_natDegree, coeff_zero] at h
    exact hlc h
  · rw [← discriminant_map _ _ hdeg (by
      rw [← derivative_map, natDegree_derivative, natDegree_derivative, hdeg])]
    exact hdisc

noncomputable def smallExponent (p q : SeparablePolynomial) (bp bq : ℕ) : ℕ :=
  let m := p.polynomial.natDegree
  let n := q.polynomial.natDegree
  let B := resultantMassExponent m n (direction p q) bp bq
  bp + bq + gcdMassExponent m bp + gcdMassExponent n bq + B + gcdMassExponent (m * n) B + 1

theorem small_pair_data (p q : SeparablePolynomial) (bp bq : ℕ)
    (hp : ∀ k, coefficientMass (p.polynomial.coeff k) ≤ 2 ^ bp)
    (hq : ∀ k, coefficientMass (q.polynomial.coeff k) ≤ 2 ^ bq)
    (beta : ℝ) (hb : 0 < beta)
    (hbs : beta ≤ InfinitesimalSign.dyadic (smallExponent p q bp bq)) :
    (p.polynomial.map (scalarEvaluation beta)).natDegree = p.polynomial.natDegree ∧
      (q.polynomial.map (scalarEvaluation beta)).natDegree = q.polynomial.natDegree ∧
      (p.polynomial.map (scalarEvaluation beta)).Separable ∧
      (q.polynomial.map (scalarEvaluation beta)).Separable ∧
      ((parameter p q).map (scalarEvaluation beta)).Separable := by
  have hP := small_data p bp (smallExponent p q bp bq) hp
    (by unfold smallExponent; dsimp only; omega) (by unfold smallExponent; dsimp only; omega) beta hb hbs
  have hQ := small_data q bq (smallExponent p q bp bq) hq
    (by unfold smallExponent; dsimp only; omega) (by unfold smallExponent; dsimp only; omega) beta hb hbs
  let B := resultantMassExponent p.polynomial.natDegree q.polynomial.natDegree (direction p q) bp bq
  have hmass (k : ℕ) : coefficientMass ((combine p q).polynomial.coeff k) ≤ 2 ^ B :=
    (NestedMass.coeff_le _ k).trans (resultant_mass _ _ _ bp bq hp hq)
  have hH := small_data (combine p q) B (smallExponent p q bp bq) hmass
    (by unfold smallExponent; dsimp only; dsimp [B]; omega) (by
      change gcdMassExponent (parameter p q).natDegree B < _
      rw [parameter_natDegree]
      unfold smallExponent
      dsimp only
      dsimp [B]
      omega) beta hb hbs
  exact ⟨hP.1, hQ.1, hP.2, hQ.2, hH.2⟩

theorem small_decode_root (p q : SeparablePolynomial) (bp bq : ℕ)
    (hp : ∀ k, coefficientMass (p.polynomial.coeff k) ≤ 2 ^ bp)
    (hq : ∀ k, coefficientMass (q.polynomial.coeff k) ≤ 2 ^ bq)
    (beta : ℝ) (hb : 0 < beta)
    (hbs : beta ≤ InfinitesimalSign.dyadic (smallExponent p q bp bq)) (theta : ℝ)
    (ht : (parameter p q).eval₂ (scalarEvaluation beta) theta = 0) :
    p.polynomial.eval₂ (scalarEvaluation beta) (evaluatedCoordinates (scalarEvaluation beta) p q theta).1 = 0 ∧
      q.polynomial.eval₂ (scalarEvaluation beta) (evaluatedCoordinates (scalarEvaluation beta) p q theta).2 = 0 ∧
      shear (direction p q) (evaluatedCoordinates (scalarEvaluation beta) p q theta) = theta ∧
      (denominator p q).eval₂ (scalarEvaluation beta) theta ≠ 0 := by
  obtain ⟨hpd, hqd, hps, hqs, hhs⟩ := small_pair_data p q bp bq hp hq beta hb hbs
  exact specialized_decode_root _ p q theta hpd hqd hps hqs hhs ht

theorem small_encode_roots (p q : SeparablePolynomial) (bp bq : ℕ)
    (hp : ∀ k, coefficientMass (p.polynomial.coeff k) ≤ 2 ^ bp)
    (hq : ∀ k, coefficientMass (q.polynomial.coeff k) ≤ 2 ^ bq)
    (beta : ℝ) (hb : 0 < beta)
    (hbs : beta ≤ InfinitesimalSign.dyadic (smallExponent p q bp bq)) (a b : ℝ)
    (ha : p.polynomial.eval₂ (scalarEvaluation beta) a = 0)
    (hb' : q.polynomial.eval₂ (scalarEvaluation beta) b = 0) :
    (parameter p q).eval₂ (scalarEvaluation beta) (shear (direction p q) (a, b)) = 0 ∧
      evaluatedCoordinates (scalarEvaluation beta) p q (shear (direction p q) (a, b)) = (a, b) := by
  obtain ⟨hpd, hqd, hps, hqs, hhs⟩ := small_pair_data p q bp bq hp hq beta hb hbs
  exact specialized_encode_roots _ p q a b hpd hqd hps hqs hhs ha hb'

end LeanCanny.Algebra.SymbolicPrimitivePair
