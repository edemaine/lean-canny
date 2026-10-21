/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelPacket
public import LeanCanny.ETR.TubeRegularFiber
public import LeanCanny.ETR.TubeClearedSystem

/-! # Native parameter identities for a stored rational tube family

The packet fixes epsilon, delta, and the projection-critical direction, while
the alpha coordinate is the variable. The compiled substitution realizes
exactly this family over every characteristic-zero field, and commutes with
extensions of the reals. All denominators are automatically nonzero.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeProjectionEncoding
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term

noncomputable def rationalValue (c : List Bool) (i : ℕ) : ℚ := (integer c i : ℚ) / denominatorNat c i
noncomputable def epsilon (c : List Bool) : ℚ := rationalValue c (alphaIndex c + 1)
noncomputable def delta (c : List Bool) : ℚ := rationalValue c (alphaIndex c + 2)
noncomputable def direction (c : List Bool) : TubeSource.Coordinate (pairFst c) → ℚ :=
  fun i => rationalValue c (TubeProjectionEncoding.pointEquiv (TubeIndexed.arity (pairFst c)) i).val

noncomputable def parameters {K : Type*} [Field K] (c : List Bool) (t : K) :
    TubeMacaulay.Coefficients (TubeIndexed.arity (pairFst c)) →+* K :=
  TubeCleared.parameterMap (pairFst c) (numerator c) (denominator c) (Int.castRingHom K) t

attribute [local irreducible] integer denominatorNat rationalValue

theorem parameters_X {K : Type*} [Field K] [CharZero K] (c : List Bool) (t : K)
    (i : TubeParameter.Parameter (pairFst c)) :
    parameters c t (MvPolynomial.X i) =
      if (TubeParameter.parameterEquiv (pairFst c) i).val = alphaIndex c then t
      else (algebraMap ℚ K) (rationalValue c (TubeParameter.parameterEquiv (pairFst c) i).val) := by
  refine (MvPolynomial.eval₂Hom_X' _ _ i).trans ?_
  by_cases h : (TubeParameter.parameterEquiv (pairFst c) i).val = alphaIndex c
  · simp only [numerator, denominator, h, ite_true, Polynomial.eval₂_X, Polynomial.eval₂_one, div_one]
  · simp only [numerator, denominator, h, ite_false, Polynomial.eval₂_C]
    simp only [rationalValue, map_div₀, map_intCast, map_natCast, Int.coe_castRingHom]

theorem parameters_direction {K : Type*} [Field K] [CharZero K] (c : List Bool) (t : K) :
    TubeRegularFiber.direction (pairFst c) (parameters c t) = fun i => (algebraMap ℚ K) (direction c i) := by
  funext i
  have hlt := (TubeProjectionEncoding.pointEquiv (TubeIndexed.arity (pairFst c)) i).isLt
  have he : (TubeParameter.parameterEquiv (pairFst c) (.inl i)).val =
      (TubeProjectionEncoding.pointEquiv (TubeIndexed.arity (pairFst c)) i).val := rfl
  have hi : (TubeParameter.parameterEquiv (pairFst c) (.inl i)).val ≠ alphaIndex c := by
    intro hh
    exact hlt.ne (he.symm.trans hh)
  exact (parameters_X c t (.inl i)).trans (ite_eq_right hi)

theorem parameters_alpha {K : Type*} [Field K] [CharZero K] (c : List Bool) (t : K) :
    parameters c t (MvPolynomial.X (.inr none)) = t := by
  exact (parameters_X c t (.inr none)).trans (ite_eq_left (by
    change pointCount (TubeIndexed.arity (pairFst c)) + 0 = pointCount (TubeIndexed.arity (pairFst c))
    omega))

theorem parameters_epsilon {K : Type*} [Field K] [CharZero K] (c : List Bool) (t : K) :
    parameters c t (MvPolynomial.X (.inr (some false))) = (algebraMap ℚ K) (epsilon c) := by
  have hi : (TubeParameter.parameterEquiv (pairFst c) (.inr (some false))).val ≠ alphaIndex c := by
    change pointCount (TubeIndexed.arity (pairFst c)) + 1 ≠ pointCount (TubeIndexed.arity (pairFst c))
    omega
  exact (parameters_X c t (.inr (some false))).trans (ite_eq_right hi)

theorem parameters_delta {K : Type*} [Field K] [CharZero K] (c : List Bool) (t : K) :
    parameters c t (MvPolynomial.X (.inr (some true))) = (algebraMap ℚ K) (delta c) := by
  have hi : (TubeParameter.parameterEquiv (pairFst c) (.inr (some true))).val ≠ alphaIndex c := by
    change pointCount (TubeIndexed.arity (pairFst c)) + 2 ≠ pointCount (TubeIndexed.arity (pairFst c))
    omega
  exact (parameters_X c t (.inr (some true))).trans (ite_eq_right hi)

theorem parameters_coefficientMap {L : Type*} [Field L] [Algebra ℝ L] (c : List Bool) (alpha : ℝ) :
    TubeRegularFiber.coefficientMap (pairFst c) (parameters c (algebraMap ℝ L alpha)) =
      (algebraMap ℝ L).comp (TubePolynomial.coefficientMap (epsilon c : ℝ) (delta c : ℝ) alpha) := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℝ L).injective
  have hcast (q : ℚ) : algebraMap ℚ L q = (q : L) := by
    simpa only [Rat.cast_id] using (map_ratCast (algebraMap ℚ L) q)
  ext p
  · simp
  · refine (MvPolynomial.eval₂Hom_X' _ _ p).trans ?_
    cases p with
    | none =>
      simpa only [RingHom.comp_apply, TubePolynomial.coefficientMap, MvPolynomial.eval₂Hom_X',
        TubePolynomial.parameters] using parameters_alpha c (algebraMap ℝ L alpha)
    | some b =>
      cases b
      · simpa only [RingHom.comp_apply, TubePolynomial.coefficientMap, MvPolynomial.eval₂Hom_X',
          TubePolynomial.parameters, map_ratCast, hcast] using parameters_epsilon c (algebraMap ℝ L alpha)
      · simpa only [RingHom.comp_apply, TubePolynomial.coefficientMap, MvPolynomial.eval₂Hom_X',
          TubePolynomial.parameters, map_ratCast, hcast] using parameters_delta c (algebraMap ℝ L alpha)

end LeanCanny.ETR.TubeLevelPacket
