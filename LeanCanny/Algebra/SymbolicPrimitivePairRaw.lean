/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicPrimitivePairSmall

/-! # Symbolic primitive recovery from arbitrary nonzero bivariate inputs

Squarefree preprocessing, separating direction, resultant and rational
coordinates are all constructed internally. One explicit small exponent covers
both leaf preprocessing and the pair operation.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicPrimitivePair
open Polynomial SymbolicScaledSquarefree
open scoped Classical

theorem dyadic_antitone {s t : ℕ} (h : s ≤ t) :
    InfinitesimalSign.dyadic t ≤ InfinitesimalSign.dyadic s := by
  unfold InfinitesimalSign.dyadic
  apply (inv_le_inv₀ (pow_pos (by norm_num : (0 : ℝ) < 2) t)
    (pow_pos (by norm_num : (0 : ℝ) < 2) s)).mpr
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h

noncomputable def rawExponent (p q : Polynomial Coefficient) (hp : p ≠ 0) (hq : q ≠ 0) (bp bq : ℕ) : ℕ :=
  smallExponent (SeparablePolynomial.of_nonzero p hp) (SeparablePolynomial.of_nonzero q hq)
    (massExponent p.natDegree bp) (massExponent q.natDegree bq) +
      SymbolicScaledSquarefree.smallExponent p.natDegree bp +
      SymbolicScaledSquarefree.smallExponent q.natDegree bq

theorem raw_small_decode_root (p q : Polynomial Coefficient) (hp : p ≠ 0) (hq : q ≠ 0) (bp bq : ℕ)
    (hbp : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ bp)
    (hbq : ∀ k, coefficientMass (q.coeff k) ≤ 2 ^ bq)
    (beta : ℝ) (hb : 0 < beta)
    (hbs : beta ≤ InfinitesimalSign.dyadic (rawExponent p q hp hq bp bq)) (theta : ℝ) :
    let P := SeparablePolynomial.of_nonzero p hp
    let Q := SeparablePolynomial.of_nonzero q hq
    (parameter P Q).eval₂ (scalarEvaluation beta) theta = 0 →
      p.eval₂ (scalarEvaluation beta) (evaluatedCoordinates (scalarEvaluation beta) P Q theta).1 = 0 ∧
        q.eval₂ (scalarEvaluation beta) (evaluatedCoordinates (scalarEvaluation beta) P Q theta).2 = 0 ∧
        shear (direction P Q) (evaluatedCoordinates (scalarEvaluation beta) P Q theta) = theta ∧
        (denominator P Q).eval₂ (scalarEvaluation beta) theta ≠ 0 := by
  dsimp only
  intro ht
  let P := SeparablePolynomial.of_nonzero p hp
  let Q := SeparablePolynomial.of_nonzero q hq
  have hpair : beta ≤ InfinitesimalSign.dyadic
      (smallExponent P Q (massExponent p.natDegree bp) (massExponent q.natDegree bq)) :=
    hbs.trans (dyadic_antitone (by unfold rawExponent; dsimp [P, Q]; omega))
  have hpleaf : beta ≤ InfinitesimalSign.dyadic (SymbolicScaledSquarefree.smallExponent p.natDegree bp) :=
    hbs.trans (dyadic_antitone (by unfold rawExponent; omega))
  have hqleaf : beta ≤ InfinitesimalSign.dyadic (SymbolicScaledSquarefree.smallExponent q.natDegree bq) :=
    hbs.trans (dyadic_antitone (by unfold rawExponent; omega))
  have hr := small_decode_root P Q (massExponent p.natDegree bp) (massExponent q.natDegree bq)
    (polynomial_coefficient_mass p bp hbp) (polynomial_coefficient_mass q bq hbq) beta hb hpair theta ht
  refine ⟨?_, ?_, hr.2.2⟩
  · exact (SymbolicScaledSquarefree.small_roots_iff p hp bp hbp beta hb hpleaf _).mp hr.1
  · exact (SymbolicScaledSquarefree.small_roots_iff q hq bq hbq beta hb hqleaf _).mp hr.2.1

theorem raw_small_encode_roots (p q : Polynomial Coefficient) (hp : p ≠ 0) (hq : q ≠ 0) (bp bq : ℕ)
    (hbp : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ bp)
    (hbq : ∀ k, coefficientMass (q.coeff k) ≤ 2 ^ bq)
    (beta : ℝ) (hb : 0 < beta)
    (hbs : beta ≤ InfinitesimalSign.dyadic (rawExponent p q hp hq bp bq)) (a b : ℝ)
    (ha : p.eval₂ (scalarEvaluation beta) a = 0) (hb' : q.eval₂ (scalarEvaluation beta) b = 0) :
    let P := SeparablePolynomial.of_nonzero p hp
    let Q := SeparablePolynomial.of_nonzero q hq
    (parameter P Q).eval₂ (scalarEvaluation beta) (shear (direction P Q) (a, b)) = 0 ∧
      evaluatedCoordinates (scalarEvaluation beta) P Q (shear (direction P Q) (a, b)) = (a, b) := by
  dsimp only
  let P := SeparablePolynomial.of_nonzero p hp
  let Q := SeparablePolynomial.of_nonzero q hq
  have hpair : beta ≤ InfinitesimalSign.dyadic
      (smallExponent P Q (massExponent p.natDegree bp) (massExponent q.natDegree bq)) :=
    hbs.trans (dyadic_antitone (by unfold rawExponent; dsimp [P, Q]; omega))
  have hpleaf : beta ≤ InfinitesimalSign.dyadic (SymbolicScaledSquarefree.smallExponent p.natDegree bp) :=
    hbs.trans (dyadic_antitone (by unfold rawExponent; omega))
  have hqleaf : beta ≤ InfinitesimalSign.dyadic (SymbolicScaledSquarefree.smallExponent q.natDegree bq) :=
    hbs.trans (dyadic_antitone (by unfold rawExponent; omega))
  apply small_encode_roots P Q (massExponent p.natDegree bp) (massExponent q.natDegree bq)
    (polynomial_coefficient_mass p bp hbp) (polynomial_coefficient_mass q bq hbq) beta hb hpair a b
  · exact (SymbolicScaledSquarefree.small_roots_iff p hp bp hbp beta hb hpleaf a).mpr ha
  · exact (SymbolicScaledSquarefree.small_roots_iff q hq bq hbq beta hb hqleaf b).mpr hb'

end LeanCanny.Algebra.SymbolicPrimitivePair
