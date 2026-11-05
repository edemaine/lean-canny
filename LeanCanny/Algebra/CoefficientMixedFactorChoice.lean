/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFactorQuery
public import LeanCanny.Algebra.IntegralMixedRelativeCutChoice
/-! # The actual clipped lower-choice probe is a causal queried cut -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientMixedFactorSpecialization
open IntegralMixedHistory IntegralMixedRelativeCuts IntegralMixedCausalRecordBits
open scoped Classical

private theorem min_mod (a k N : ℕ) (hN : 0 < N) :
    (min k (a % N)) % N = min k (a % N) :=
  Nat.mod_eq_of_lt ((min_le_right _ _).trans_lt (Nat.mod_lt _ hN))

/-- The native probe clips to the selected creating choice BEFORE parsing
its finite index. The modulo operation does not change this clipped value. -/
theorem queried_kind_atChoice {n B : ℕ} {P : SpatialSource n} (c : Cut P B)
    (Q : ℤ) (hQ : Q ≠ 0) (k : ℕ) :
    (queriedCut c (min k (choiceIndex (c.rule Q hQ) (c.kind Q hQ)))).kind Q hQ =
      atChoice (c.rule Q hQ) (c.kind Q hQ) k := by
  rcases c with ⟨r, h, hf, tag, j, a, d, hs, hb, current⟩
  cases tag <;> simp only [queriedCut, Cut.kind, choiceIndex, atChoice]
  · congr 1
    apply Fin.ext
    exact min_mod a k _ (Nat.succ_pos _)
  · congr 1
    apply Fin.ext
    apply min_mod
    unfold IntegralMixedCoordinateSquarefree.coordinateDegree PurePowerReductionBounds.dimension FixedWidthPolynomial.count
    exact pow_pos (Nat.two_pow_pos _) _
  · congr 1
    apply Fin.ext
    apply min_mod
    unfold IntegralMixedValueTrailing.ChoiceBound
    omega
  · congr 1
    apply Fin.ext
    exact min_mod a k _ (Nat.succ_pos _)

/-- Source-degree retargeting and actual current-Q insertion preserve the
native clipped choice, with its exact original coordinate and tag. -/
theorem native_retarget_atChoice {n S B m : ℕ} {P Q : SpatialSource n} {I : Type}
    (hd : P.degree = Q.degree) (x : State Q S B m I) (hm : m ≤ S) (c : Cut P B) (requested : ℕ) :
    nativeFactor x hm (c.rule 1 one_ne_zero) c.current
      (CoefficientMixedCutSourceDegree.kind hd (c.rule 1 one_ne_zero)
        (atChoice (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero) requested)) =
      IntegralMixedRelativeCuts.factor x hm
        ((CoefficientMixedCutSourceDegree.cut hd c).rule (commonDenominator x) (commonDenominator_ne_zero x))
        (atChoice ((CoefficientMixedCutSourceDegree.cut hd c).rule (commonDenominator x) (commonDenominator_ne_zero x))
          ((CoefficientMixedCutSourceDegree.cut hd c).kind (commonDenominator x) (commonDenominator_ne_zero x)) requested) := by
  cases P
  cases Q
  dsimp only at hd
  cases hd
  rcases c with ⟨r, h, hf, tag, j, a, d, hs, hb, current⟩
  cases current <;> cases tag <;> rfl

end LeanCanny.Algebra.CoefficientMixedFactorSpecialization
