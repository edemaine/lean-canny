/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelCoordinates
public import LeanCanny.Algebra.RationalSubstitutionBounds
public import LeanCanny.Algebra.ScaledSignQueries
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # Integer univariate sign queries for decoded tube samples

The rational epsilon denominator is positive. Multiplying each constraint by
it gives an integer polynomial in compiled coordinates. Even coordinate
powers then clear the rational decoding denominators without changing signs
at parameter roots. Active constraints use the constant query one.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding MvPolynomial
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCleared.uniformDegree

noncomputable def sampleIndex (c : List Bool) (i : TubeSource.Coordinate (pairFst c)) :
    Fin (TubeParameter.spatialCount (pairFst c)) :=
  (TubeMacaulay.coordinateEquiv (TubeIndexed.arity (pairFst c)) (some i)).succ

noncomputable def samplePolynomial (c : List Bool) :
    MvPolynomial (Fin (TubeParameter.spatialCount (pairFst c))) ℤ :=
  rename (fun i => sampleIndex c (.inl i)) (CompactSource.polynomial (pairFst c))

noncomputable def zeroMarginConstraint (c : List Bool) :
    PerturbedSource.Index (pairFst c) → MvPolynomial (Fin (TubeParameter.spatialCount (pairFst c))) ℤ
  | .inl false => samplePolynomial c + X (sampleIndex c (.inr (.inl false)))
  | .inl true => -samplePolynomial c + X (sampleIndex c (.inr (.inl true)))
  | .inr (i, false) => X (sampleIndex c (.inl i)) + 1 + X (sampleIndex c (.inr (.inr (i, false))))
  | .inr (i, true) => 1 - X (sampleIndex c (.inl i)) + X (sampleIndex c (.inr (.inr (i, true))))

noncomputable def integerConstraint (c : List Bool) (i : PerturbedSource.Index (pairFst c)) :
    MvPolynomial (Fin (TubeParameter.spatialCount (pairFst c))) ℤ :=
  C ((epsilon c).den : ℤ) * zeroMarginConstraint c i -
    match i with
    | .inl _ => 0
    | .inr _ => C (epsilon c).num

theorem eval_zeroMarginConstraint (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ) (i : PerturbedSource.Index (pairFst c)) :
    (zeroMarginConstraint c i).eval₂ (Int.castRingHom ℝ) z =
      PolynomialPerturbation.parameterMap (CompactSource.polynomial (pairFst c)) 0
        (TubePolynomial.splitPoint (samplePoint c z)) i := by
  have hx (j : Fin (TubeParameter.spatialCount (pairFst c))) :
      eval₂ (Int.castRingHom ℝ) z (X j) = z j := eval₂_X _ _ _
  have hp : eval₂ (Int.castRingHom ℝ) z (samplePolynomial c) =
      (CompactSource.polynomial (pairFst c)).eval₂ (Int.castRingHom ℝ)
        (fun j => samplePoint c z (.inl j)) := by
    exact (eval₂_rename _ _ _ _).trans rfl
  rcases i with b | ⟨j, b⟩ <;> cases b <;>
    simp only [zeroMarginConstraint, eval₂_add, eval₂_sub, eval₂_neg, eval₂_one, hx, hp,
      PolynomialPerturbation.parameterMap, PolynomialPerturbation.value, TubePolynomial.splitPoint,
      sub_zero]
  all_goals rfl

theorem eval_integerConstraint (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ) (i : PerturbedSource.Index (pairFst c)) :
    (integerConstraint c i).eval₂ (Int.castRingHom ℝ) z =
      ((epsilon c).den : ℝ) * PolynomialPerturbation.parameterMap
        (CompactSource.polynomial (pairFst c)) (epsilon c : ℝ)
        (TubePolynomial.splitPoint (samplePoint c z)) i := by
  have hden : ((epsilon c).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.den_ne_zero _)
  have heps : ((epsilon c).den : ℝ) * (epsilon c : ℝ) = ((epsilon c).num : ℝ) := by
    rw [Rat.cast_def, mul_comm]
    exact div_mul_cancel₀ _ hden
  unfold integerConstraint
  simp only [eval₂_sub, eval₂_mul, eval₂_C, eval_zeroMarginConstraint]
  rcases i with b | ⟨j, b⟩ <;> cases b <;>
    simp only [eval₂_zero, eval₂_C, Int.coe_castRingHom, Int.cast_natCast,
      PolynomialPerturbation.parameterMap, PolynomialPerturbation.value, sub_zero]
  all_goals linear_combination heps

noncomputable def signQuery (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    {r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha)}
    (d : IntegerCoordinatePolynomials.IntegerData r) (i : PerturbedSource.Index (pairFst c)) : Polynomial ℤ :=
  if i ∈ activeSet (TubeIndexed.arity (pairFst c)) mask then 1 else
    RationalSubstitution.cleared (integerConstraint c i) d.numerator d.denominator

theorem signQuery_pos_iff (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    {r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha)}
    (d : IntegerCoordinatePolynomials.IntegerData r) (θ : ℝ)
    (hθ : Polynomial.aeval θ d.polynomial = 0) (i : PerturbedSource.Index (pairFst c)) :
    0 < Polynomial.aeval θ (signQuery c mask ell alpha d i) ↔
      i ∉ activeSet (TubeIndexed.arity (pairFst c)) mask →
        0 < PolynomialPerturbation.parameterMap (CompactSource.polynomial (pairFst c)) (epsilon c : ℝ)
          (TubePolynomial.splitPoint (samplePoint c (d.decode θ))) i := by
  by_cases hi : i ∈ activeSet (TubeIndexed.arity (pairFst c)) mask
  · simp [signQuery, hi]
  · rw [signQuery, ite_eq_right hi]
    have hd (j : Fin (TubeParameter.spatialCount (pairFst c))) :
        (d.denominator j).eval₂ (Int.castRingHom ℝ) θ ≠ 0 := d.denominator_ne_zero_at_root θ hθ j
    have he := RationalSubstitution.eval₂_cleared (Int.castRingHom ℝ) θ (integerConstraint c i)
      d.numerator d.denominator hd
    have hp := RationalSubstitution.denominator_eval₂_pos (Int.castRingHom ℝ) θ
      (integerConstraint c i) d.denominator hd
    change 0 < (RationalSubstitution.cleared _ _ _).eval₂ (Int.castRingHom ℝ) θ ↔ _
    rw [he]
    change 0 < _ * (integerConstraint c i).eval₂ (Int.castRingHom ℝ) (d.decode θ) ↔ _
    rw [mul_pos_iff_of_pos_left hp, eval_integerConstraint,
      mul_pos_iff_of_pos_left (by exact_mod_cast (epsilon c).den_pos)]
    simp only [hi, not_false_eq_true, true_implies]

noncomputable def indexedSignQuery (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    {r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha)}
    (d : IntegerCoordinatePolynomials.IntegerData r) (i : ℕ) : Polynomial ℤ :=
  if hi : i < constraintCount (TubeIndexed.arity (pairFst c)) then
    signQuery c mask ell alpha d ((constraintEquiv _).symm ⟨i, hi⟩) else 1

theorem indexedSignQuery_constraint (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    {r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha)}
    (d : IntegerCoordinatePolynomials.IntegerData r) (i : PerturbedSource.Index (pairFst c)) :
    indexedSignQuery c mask ell alpha d (constraintEquiv (TubeIndexed.arity (pairFst c)) i).val = signQuery c mask ell alpha d i := by
  unfold indexedSignQuery
  rw [dite_eq_left (constraintEquiv (TubeIndexed.arity (pairFst c)) i).isLt]
  exact congrArg (signQuery c mask ell alpha d)
    ((constraintEquiv (TubeIndexed.arity (pairFst c))).symm_apply_apply i)

theorem indexedSigns_iff (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    {r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha)}
    (d : IntegerCoordinatePolynomials.IntegerData r) (θ : ℝ)
    (hθ : Polynomial.aeval θ d.polynomial = 0) :
    (∀ i : Fin (constraintCount (TubeIndexed.arity (pairFst c))),
      SignType.sign (Polynomial.aeval θ (indexedSignQuery c mask ell alpha d i.val)) = .pos) ↔
        inactiveSigns c mask (d.decode θ) := by
  constructor
  · intro h i hi
    have hp := h (constraintEquiv (TubeIndexed.arity (pairFst c)) i)
    have he := indexedSignQuery_constraint c mask ell alpha d i
    have hp' := (congrArg (fun q : Polynomial ℤ => SignType.sign (Polynomial.aeval θ q)) he).symm.trans hp
    exact (signQuery_pos_iff c mask ell alpha d θ hθ i).mp
      (sign_eq_one_iff.mp hp') hi
  · intro h i
    let j := (constraintEquiv (TubeIndexed.arity (pairFst c))).symm i
    have he : indexedSignQuery c mask ell alpha d i.val = signQuery c mask ell alpha d j := by
      have he := indexedSignQuery_constraint c mask ell alpha d j
      simpa only [j, Equiv.apply_symm_apply] using he
    exact (congrArg (fun q : Polynomial ℤ => SignType.sign (Polynomial.aeval θ q)) he).trans
      (sign_eq_one_iff.mpr ((signQuery_pos_iff c mask ell alpha d θ hθ j).mpr (h j)))

noncomputable def sampleRootCount (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    {r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha)}
    (d : IntegerCoordinatePolynomials.IntegerData r) : ℕ :=
  RootSignQueries.signCount ((d.polynomial.map (algebraMap ℤ ℝ)).roots.toFinset)
    (fun i : Fin (constraintCount (TubeIndexed.arity (pairFst c))) =>
      (indexedSignQuery c mask ell alpha d i.val).map (algebraMap ℤ ℝ)) (fun _ => .pos)

theorem sampleRootCount_pos_iff (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    (hf : FiniteCompiledFibers.{0} c (alpha : ℝ))
    {r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha)}
    (d : IntegerCoordinatePolynomials.IntegerData r) :
    0 < sampleRootCount c mask ell alpha d ↔ ∃ z, CompiledSample c mask ell (alpha : ℝ) z := by
  have hn : d.polynomial.map (algebraMap ℤ ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (show Function.Injective (algebraMap ℤ ℝ) from Int.cast_injective)).mpr d.polynomial_ne_zero
  rw [sampleRootCount, RootSignQueries.root_signCount_pos _ hn]
  simp_rw [Polynomial.eval_map]
  change (∃ θ : ℝ, Polynomial.aeval θ d.polynomial = 0 ∧
    ∀ i : Fin (constraintCount (TubeIndexed.arity (pairFst c))),
      SignType.sign (Polynomial.aeval θ (indexedSignQuery c mask ell alpha d i.val)) = .pos) ↔ _
  rw [exists_compiledSample_iff_integer c mask ell alpha hf r d]
  exact exists_congr (fun θ => and_congr_right (fun hθ => indexedSigns_iff c mask ell alpha d θ hθ))

noncomputable def UniformSignCounts (bits : List Bool) (eps del : ℚ) : Prop :=
  ∃ c : List Bool, pairFst c = bits ∧ epsilon c = eps ∧ delta c = del ∧
    direction c (TubePolynomial.base _) = 1 ∧ ∃ mask : List Bool, ∃ a : ℝ, 0 < a ∧
      ∀ alpha : ℚ, 0 < alpha → (alpha : ℝ) < a →
        FiniteCompiledFibers.{0} c (alpha : ℝ) ∧ ∀ ell : ℕ → ℤ,
          ∃ r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha),
            ∃ d : IntegerCoordinatePolynomials.IntegerData r, 0 < sampleRootCount c mask ell alpha d

theorem uniform_signCounts_iff (bits : List Bool) (eps del : ℚ) :
    UniformSignCounts bits eps del ↔ UniformCoordinateSamples bits eps del := by
  constructor
  · rintro ⟨c, hc, he, hd, hb, mask, a, ha, hs⟩
    refine ⟨c, hc, he, hd, hb, mask, a, ha, ?_⟩
    intro alpha hp hl
    obtain ⟨hf, hr⟩ := hs alpha hp hl
    refine ⟨hf, ?_⟩
    intro ell
    obtain ⟨r, d, hc⟩ := hr ell
    exact ⟨r, d, (exists_compiledSample_iff_integer c mask ell alpha hf r d).mp
      ((sampleRootCount_pos_iff c mask ell alpha hf d).mp hc)⟩
  · rintro ⟨c, hc, he, hd, hb, mask, a, ha, hs⟩
    refine ⟨c, hc, he, hd, hb, mask, a, ha, ?_⟩
    intro alpha hp hl
    obtain ⟨hf, hr⟩ := hs alpha hp hl
    refine ⟨hf, ?_⟩
    intro ell
    obtain ⟨r, d, θ, hθ, hi⟩ := hr ell
    exact ⟨r, d, (sampleRootCount_pos_iff c mask ell alpha hf d).mpr
      ((exists_compiledSample_iff_integer c mask ell alpha hf r d).mpr ⟨θ, hθ, hi⟩)⟩

end LeanCanny.ETR.TubeLevelPacket

namespace LeanCanny.ETR.TubeLevelSamplingSource

/-- Exact ETR correctness via positive finite sign counts at rational tube levels.
Constructing bounded coordinate representations remains open. -/
theorem signCounts_correct (bits : List Bool) : bits ∈ ETR.language ↔
    ∃ eps : ℚ, 0 < eps ∧ ∀ del : ℚ, 0 < del → TubeLevelPacket.UniformSignCounts bits eps del := by
  simpa only [TubeLevelPacket.uniform_signCounts_iff] using coordinates_correct bits

end LeanCanny.ETR.TubeLevelSamplingSource
