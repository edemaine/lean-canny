/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelCoordinates
public import LeanCanny.Algebra.RationalSubstitutionWith
public import LeanCanny.Algebra.ScaledSignQueries
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # Integer univariate sign queries for decoded tube samples

The stored margin denominator is positive. Multiplying each constraint by
it gives an integer polynomial in compiled coordinates, using the raw packet
integers without rational normalization. Fixed even powers based on the source
size clear coordinate denominators and preserve signs at parameter roots.
Active constraints use the constant query one.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding MvPolynomial
open scoped Classical BigOperators
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

noncomputable def marginNumerator (c : List Bool) : ℤ := integer c (alphaIndex c + 1)
noncomputable def marginDenominator (c : List Bool) : ℕ := denominatorNat c (alphaIndex c + 1)

theorem marginDenominator_pos (c : List Bool) : 0 < marginDenominator c := by
  unfold marginDenominator denominatorNat
  omega

noncomputable def integerConstraint (c : List Bool) (i : PerturbedSource.Index (pairFst c)) :
    MvPolynomial (Fin (TubeParameter.spatialCount (pairFst c))) ℤ :=
  C (marginDenominator c : ℤ) * zeroMarginConstraint c i -
    match i with
    | .inl _ => 0
    | .inr _ => C (marginNumerator c)

theorem integerConstraint_coeff (c : List Bool) (i : PerturbedSource.Index (pairFst c))
    (e : Fin (TubeParameter.spatialCount (pairFst c)) →₀ ℕ) :
    (integerConstraint c i).coeff e = (marginDenominator c : ℤ) * (zeroMarginConstraint c i).coeff e -
      match i with
      | .inl _ => 0
      | .inr _ => marginNumerator c * (1 : MvPolynomial (Fin (TubeParameter.spatialCount (pairFst c))) ℤ).coeff e := by
  unfold integerConstraint
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, MvPolynomial.coeff_C_mul]
  cases i with
  | inl b => simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  | inr j =>
    have hc := MvPolynomial.coeff_C_mul e (marginNumerator c)
      (1 : MvPolynomial (Fin (TubeParameter.spatialCount (pairFst c))) ℤ)
    rw [mul_one] at hc
    exact congrArg (fun z => (marginDenominator c : ℤ) * (zeroMarginConstraint c (.inr j)).coeff e - z) hc

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
      (marginDenominator c : ℝ) * PolynomialPerturbation.parameterMap
        (CompactSource.polynomial (pairFst c)) (epsilon c : ℝ)
        (TubePolynomial.splitPoint (samplePoint c z)) i := by
  have hden : (marginDenominator c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (marginDenominator_pos c).ne'
  have heq : (epsilon c : ℝ) = (marginNumerator c : ℝ) / (marginDenominator c : ℝ) := by
    simp only [epsilon, rationalValue, marginNumerator, marginDenominator,
      Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  have heps : (marginDenominator c : ℝ) * (epsilon c : ℝ) = (marginNumerator c : ℝ) := by
    rw [heq, mul_comm]
    exact div_mul_cancel₀ _ hden
  unfold integerConstraint
  simp only [eval₂_sub, eval₂_mul, eval₂_C, eval_zeroMarginConstraint]
  rcases i with b | ⟨j, b⟩ <;> cases b <;>
    simp only [eval₂_zero, eval₂_C, Int.coe_castRingHom, Int.cast_natCast,
      PolynomialPerturbation.parameterMap, PolynomialPerturbation.value, sub_zero]
  all_goals linear_combination heps

theorem zeroMarginConstraint_degree (c : List Bool) (i : PerturbedSource.Index (pairFst c)) :
    (zeroMarginConstraint c i).totalDegree ≤ max (CompactSource.polynomial (pairFst c)).totalDegree 1 := by
  have hp : (samplePolynomial c).totalDegree ≤ (CompactSource.polynomial (pairFst c)).totalDegree :=
    totalDegree_rename_le _ _
  rcases i with b | ⟨j, b⟩ <;> cases b
  · exact (totalDegree_add _ _).trans (max_le_max hp (by simp))
  · exact (totalDegree_add _ _).trans (max_le_max (by simpa only [totalDegree_neg] using hp) (by simp))
  · apply (totalDegree_add _ _).trans
    apply max_le
    · exact (totalDegree_add _ _).trans (by simp)
    · simp
  · apply (totalDegree_add _ _).trans
    apply max_le
    · exact (totalDegree_sub _ _).trans (by simp)
    · simp

theorem integerConstraint_degree (c : List Bool) (i : PerturbedSource.Index (pairFst c)) :
    (integerConstraint c i).totalDegree ≤ TubeIndexed.degreeBound (pairFst c) := by
  have hp := CompactSource.degree_le_code (pairFst c)
  simp only [CompactSource.degreeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits] at hp
  have hz := zeroMarginConstraint_degree c i
  unfold integerConstraint
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    unfold TubeIndexed.degreeBound
    omega
  · cases i with
    | inl _ => exact (totalDegree_zero.le).trans (Nat.zero_le _)
    | inr _ => exact (totalDegree_C _).le.trans (Nat.zero_le _)

theorem integerConstraint_degreeOf (c : List Bool) (i : PerturbedSource.Index (pairFst c))
    (j : Fin (TubeParameter.spatialCount (pairFst c))) :
    (integerConstraint c i).degreeOf j ≤ TubeIndexed.degreeBound (pairFst c) :=
  (degreeOf_le_totalDegree _ _).trans (integerConstraint_degree c i)

noncomputable def signQuery (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    {r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha)}
    (d : IntegerCoordinatePolynomials.IntegerData r) (i : PerturbedSource.Index (pairFst c)) : Polynomial ℤ :=
  if i ∈ activeSet (TubeIndexed.arity (pairFst c)) mask then 1 else
    RationalSubstitution.clearedWith (fun _ => TubeIndexed.degreeBound (pairFst c))
      (integerConstraint c i) d.numerator d.denominator

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
    have he := RationalSubstitution.eval₂_clearedWith (Int.castRingHom ℝ) θ
      (fun _ => TubeIndexed.degreeBound (pairFst c)) (integerConstraint c i)
      d.numerator d.denominator (integerConstraint_degreeOf c i) hd
    have hp : 0 < ∏ j, (d.denominator j).eval₂ (Int.castRingHom ℝ) θ ^
        (2 * TubeIndexed.degreeBound (pairFst c)) := by
      apply Finset.prod_pos
      intro j _
      rw [pow_mul]
      exact pow_pos (sq_pos_of_ne_zero (hd j)) _
    change 0 < (RationalSubstitution.clearedWith _ _ _ _).eval₂ (Int.castRingHom ℝ) θ ↔ _
    rw [he]
    change 0 < _ * (integerConstraint c i).eval₂ (Int.castRingHom ℝ) (d.decode θ) ↔ _
    rw [mul_pos_iff_of_pos_left hp, eval_integerConstraint,
      mul_pos_iff_of_pos_left (by exact_mod_cast marginDenominator_pos c)]
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
