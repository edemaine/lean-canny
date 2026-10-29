/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleSource
public import LeanCanny.Algebra.FiniteLeafCoordinateCorrect

/-! # Native rational coordinates for complete flat sampling

The indexed flat equations feed the balanced primitive tree. Every tuple
of their roots has a separable common parameter, nonvanishing coordinate
denominators, and native numerator and denominator readers. Filtering by the
complete flat equations and regularity remains separate.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleCoordinates
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open Brackets
open FlatFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FiniteLeafCoordinateBits.coordinate

noncomputable def count (F : Inputs) (c : List Bool) : ℕ := FlatFullSourceSampleSource.count F (pairFst c)
noncomputable def degreeBound (F : Inputs) (c : List Bool) : ℕ :=
  FiniteSourceDegreePreparation.degreeBudget (FlatFullSourceSampleSource.degreeBound F) (pairFst c)
noncomputable def height (F : Inputs) (c : List Bool) : ℕ := FlatFullSourceSampleSource.massBound F (pairFst c)

theorem nonzero (F : Inputs) (c : List Bool) (i : ℕ) (_hi : i < count F c) :
    (FlatFullSourceSampleSource.family F).polynomial (pair c (BinaryNatCode.encode i)) ≠ 0 :=
  FlatFullSourceSampleSource.family_nonzero _ _

theorem degree_le (F : Inputs) (c : List Bool) (i : ℕ) (_hi : i < count F c) :
    ((FlatFullSourceSampleSource.family F).polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ degreeBound F c :=
  (FiniteSourceDegreePreparation.family_degree _ _ _ _ (FlatFullSourceSampleSource.source_mass F) c i).le

theorem height_le (F : Inputs) (c : List Bool) (i : ℕ) (_hi : i < count F c) :
    (FlatFullSourceSampleSource.family F).height (pair c (BinaryNatCode.encode i)) ≤ height F c := by
  rw [FlatFullSourceSampleSource.family, FiniteSourceDegreePreparation.family_height, pairFst_pair]
  exact le_rfl

theorem count_unary {F : Inputs} (h : F.Access) : UnaryFn (count F) :=
  (FlatFullSourceSampleSource.count_unary h).comp pairFst_mem_FP
theorem degreeBound_binary {F : Inputs} (h : F.Access) : BinaryFn (degreeBound F) :=
  (FiniteSourceDegreePreparation.degreeBudget_binary (FlatFullSourceSampleSource.degreeBound_binary h)).comp pairFst_mem_FP
theorem height_binary {F : Inputs} (h : F.Access) : BinaryFn (height F) :=
  (FlatFullSourceSampleSource.massBound_binary h).comp pairFst_mem_FP

noncomputable def rawCoordinate (F : Inputs) :=
  FiniteLeafCoordinateBits.coordinate (FlatFullSourceSampleSource.family F) (count F) (degreeBound F) (height F) (nonzero F)

noncomputable def prepareCoordinate (F : Inputs) (u : List Bool) : List Bool :=
  pair (FlatFullSourceSampleSource.prepare F (pairFst u)) (pairSnd u)

theorem prepareCoordinate_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (prepareCoordinate F) :=
  ((FlatFullSourceSampleSource.prepare_evaluator h).precompose pairFst pairFst_mem_FP).pairOutputs
    (SpaceFunction.ofFP _ pairSnd_mem_FP)

noncomputable def coordinate (F : Inputs) : List Bool → UnivariateRational.Coordinate :=
  rawCoordinate F ∘ prepareCoordinate F

noncomputable def baseHeight (F : Inputs) (c : List Bool) : ℕ :=
  FiniteAnnihilatorTree.sourceHeight
    (FiniteSourceDegreePreparation.degreeBudget (FlatFullSourceSampleSource.degreeBound F) c)
    (FlatFullSourceSampleSource.massBound F c) (FlatFullSourceSampleSource.count F c)

noncomputable def coordinateDegree (F : Inputs) (c : List Bool) : ℕ :=
  (baseHeight F c ^ 3) ^ (FlatFullSourceSampleSource.count F c).size
noncomputable def coordinateMass (F : Inputs) (c : List Bool) : ℕ :=
  (FlatFullSourceSampleSource.count F c).size * coordinateDegree F c * baseHeight F c ^ 10

theorem baseHeight_binary {F : Inputs} (h : F.Access) : BinaryFn (baseHeight F) :=
  FiniteAnnihilatorTree.sourceHeight_binary
    (FiniteSourceDegreePreparation.degreeBudget_binary (FlatFullSourceSampleSource.degreeBound_binary h))
    (FlatFullSourceSampleSource.massBound_binary h) (FlatFullSourceSampleSource.count_unary h)
theorem coordinateDegree_binary {F : Inputs} (h : F.Access) : BinaryFn (coordinateDegree F) :=
  ((baseHeight_binary h).powUnary (UnaryFn.const 3)).powUnary ((FlatFullSourceSampleSource.count_unary h).size)
theorem coordinateMass_binary {F : Inputs} (h : F.Access) : BinaryFn (coordinateMass F) :=
  ((BinaryFn.ofUnary (FlatFullSourceSampleSource.count_unary h).size).mul (coordinateDegree_binary h)).mul
    ((baseHeight_binary h).powUnary (UnaryFn.const 10))

theorem prepared_controls (F : Inputs) (u : List Bool) :
    FiniteLeafCoordinateBits.degreeControl (count F) (degreeBound F) (height F) (prepareCoordinate F u) =
        baseHeight F (pairFst u) ^ 3 ∧
      FiniteLeafCoordinateBits.massControl (count F) (degreeBound F) (height F) (prepareCoordinate F u) =
        baseHeight F (pairFst u) ^ 10 ∧
      FiniteLeafPathContext.depth (count F) (prepareCoordinate F u) = (FlatFullSourceSampleSource.count F (pairFst u)).size := by
  simp only [FiniteLeafCoordinateBits.degreeControl, FiniteLeafCoordinateBits.massControl,
    CanonicalPairBits.degreeBudget, CanonicalPairBits.massBudget, CanonicalNodeBits.heightBudget,
    FiniteLeafPathContext.leafContext, BalancedParameterContext.original_packet,
    FiniteLeafPathContext.depth, prepareCoordinate, pairFst_pair, count, degreeBound, height,
    FlatFullSourceSampleSource.prepare_source]
  exact ⟨rfl, rfl, trivial⟩

theorem coordinate_bounds (F : Inputs) (u : List Bool) :
    (coordinate F u).degree ≤ coordinateDegree F (pairFst u) ∧
      coefficientMass (coordinate F u).numerator ≤ 2 ^ coordinateMass F (pairFst u) ∧
      coefficientMass (coordinate F u).denominator ≤ 2 ^ coordinateMass F (pairFst u) := by
  have H := FiniteLeafCoordinateBits.coordinate_bounds (FlatFullSourceSampleSource.family F)
    (count F) (degreeBound F) (height F) (nonzero F) (degree_le F) (height_le F) (prepareCoordinate F u)
  rw [(prepared_controls F u).1, (prepared_controls F u).2.1, (prepared_controls F u).2.2] at H
  exact H

theorem raw_coefficient_evaluators {F : Inputs} (h : F.Access) :
    SpaceFunction (PrimitivePairBits.coefficient (fun u => (rawCoordinate F u).numerator)) ∧
      SpaceFunction (PrimitivePairBits.coefficient (fun u => (rawCoordinate F u).denominator)) :=
  FiniteLeafCoordinateBits.coefficientEvaluators (FlatFullSourceSampleSource.family F)
    (count F) (degreeBound F) (height F) (nonzero F) (degree_le F) (height_le F)
    (FlatFullSourceSampleSource.readers h) (count_unary h) (degreeBound_binary h) (height_binary h)

theorem coefficient_evaluators {F : Inputs} (h : F.Access) :
    SpaceFunction (PrimitivePairBits.coefficient (fun u => (coordinate F u).numerator)) ∧
      SpaceFunction (PrimitivePairBits.coefficient (fun u => (coordinate F u).denominator)) := by
  have E := raw_coefficient_evaluators h
  exact ⟨PrimitivePairBits.withContextEvaluator (fun u => (rawCoordinate F u).numerator)
      (prepareCoordinate F) (prepareCoordinate_evaluator h) E.1,
    PrimitivePairBits.withContextEvaluator (fun u => (rawCoordinate F u).denominator)
      (prepareCoordinate F) (prepareCoordinate_evaluator h) E.2⟩

noncomputable def rawParameter (F : Inputs) : List Bool → Polynomial ℤ :=
  FiniteAnnihilatorBits.finiteParameter (FlatFullSourceSampleSource.family F) (count F) (nonzero F)

noncomputable def parameter (F : Inputs) : List Bool → Polynomial ℤ :=
  rawParameter F ∘ FlatFullSourceSampleSource.prepare F

noncomputable def parameterDegree (F : Inputs) (c : List Bool) : ℕ :=
  FiniteSourceDegreePreparation.degreeBudget (FlatFullSourceSampleSource.degreeBound F) c ^
    FlatFullSourceSampleSource.count F c

theorem parameterDegree_binary {F : Inputs} (h : F.Access) : BinaryFn (parameterDegree F) :=
  (FiniteSourceDegreePreparation.degreeBudget_binary (FlatFullSourceSampleSource.degreeBound_binary h)).powUnary
    (FlatFullSourceSampleSource.count_unary h)

theorem parameter_ne_zero (F : Inputs) (c : List Bool) : parameter F c ≠ 0 :=
  (FiniteAnnihilatorTree.parameter
    (fun i => (FlatFullSourceSampleSource.family F).polynomial
      (pair (FlatFullSourceSampleSource.prepare F c) (BinaryNatCode.encode i)))
    (count F (FlatFullSourceSampleSource.prepare F c)) (nonzero F (FlatFullSourceSampleSource.prepare F c))).ne_zero

theorem parameter_bounds (F : Inputs) (c : List Bool) :
    (parameter F c).natDegree ≤ parameterDegree F c ∧
      coefficientMass (parameter F c) ≤ 2 ^ baseHeight F c := by
  let a := FlatFullSourceSampleSource.prepare F c
  let p := fun i => (FlatFullSourceSampleSource.family F).polynomial (pair a (BinaryNatCode.encode i))
  have hd := FiniteAnnihilatorTree.parameter_degree_le p (count F a) (nonzero F a) (degreeBound F a) (degree_le F a)
  have hb (i : ℕ) (hi : i < count F a) (k : ℕ) : ((p i).coeff k).natAbs ≤ 2 ^ height F a :=
    ((FlatFullSourceSampleSource.family F).coefficient_bound _ k).trans
      (Nat.pow_le_pow_right (by decide) (height_le F a i hi))
  have hm := FiniteAnnihilatorTree.parameter_mass_from_source p (count F a) (nonzero F a)
    (degreeBound F a) (height F a) (degree_le F a) hb
  constructor
  · simpa only [parameter, rawParameter, Function.comp_apply, FiniteAnnihilatorBits.finiteParameter,
      p, a, count, degreeBound, FlatFullSourceSampleSource.prepare_source, parameterDegree] using hd
  · simpa only [parameter, rawParameter, Function.comp_apply, FiniteAnnihilatorBits.finiteParameter,
      p, a, count, degreeBound, height, FlatFullSourceSampleSource.prepare_source, baseHeight] using hm

theorem parameter_coefficient_evaluator {F : Inputs} (h : F.Access) :
    SpaceFunction (PrimitivePairBits.coefficient (parameter F)) := by
  have R := FiniteAnnihilatorBits.coefficientEvaluator (FlatFullSourceSampleSource.family F)
    (FlatFullSourceSampleSource.readers h) (count F) (degreeBound F) (height F)
    (count_unary h) (degreeBound_binary h) (height_binary h) (nonzero F) (degree_le F) (height_le F)
  have R' : SpaceFunction (PrimitivePairBits.coefficient (rawParameter F)) := R.congr (funext fun _ => rfl)
  exact PrimitivePairBits.withContextEvaluator _ _ (FlatFullSourceSampleSource.prepare_evaluator h) R'

theorem parameter_degree_evaluator {F : Inputs} (h : F.Access) :
    SpaceFunction (fun u => BinaryNatCode.encode (parameter F u).natDegree) :=
  IntegerPolynomialBits.degreeEvaluator (parameter F) (parameter_coefficient_evaluator h)
    (parameterDegree F) (baseHeight F) (parameterDegree_binary h) (baseHeight_binary h)
    (fun u => (parameter_bounds F u).1) (fun u => (parameter_bounds F u).2)

/-- Every tuple satisfying the original coordinate equations is recovered by
one root of the native parameter polynomial, with every denominator nonzero. -/
theorem tuple_complete (F : Inputs) (c : List Bool) {K : Type*} [Field K] [CharZero K]
    (x : Fin (FlatFullSourceSampleSource.count F c) → K)
    (hx : ∀ i, (FlatFullSourceSampleSource.polynomial F (pair c (BinaryNatCode.encode i.val))).eval₂
      (Int.castRingHom K) (x i) = 0) :
    ∃ theta : K, (parameter F c).eval₂ (Int.castRingHom K) theta = 0 ∧
      ∀ i : Fin (FlatFullSourceSampleSource.count F c),
        (coordinate F (pair c (BinaryNatCode.encode i.val))).denominator.eval₂ (Int.castRingHom K) theta ≠ 0 ∧
        (coordinate F (pair c (BinaryNatCode.encode i.val))).eval theta = x i := by
  let a := FlatFullSourceSampleSource.prepare F c
  have hn : count F a = FlatFullSourceSampleSource.count F c := by
    simp only [count, a, FlatFullSourceSampleSource.prepare_source]
  let y : Fin (count F a) → K := fun j => x ⟨j.val, by rw [← hn]; exact j.isLt⟩
  have hy (j : Fin (count F a)) :
      ((FlatFullSourceSampleSource.family F).polynomial (pair a (BinaryNatCode.encode j.val))).eval₂
        (Int.castRingHom K) (y j) = 0 := by
    rw [FlatFullSourceSampleSource.prepared_polynomial F c j.val (by rw [← hn]; exact j.isLt)]
    exact hx ⟨j.val, by rw [← hn]; exact j.isLt⟩
  let theta := FiniteAnnihilatorTree.encode
    (fun j => (FlatFullSourceSampleSource.family F).polynomial (pair a (BinaryNatCode.encode j)))
    (count F a) (nonzero F a) y
  refine ⟨theta, FiniteAnnihilatorTree.encode_root _ _ _ y hy, ?_⟩
  intro i
  let j : Fin (count F a) := ⟨i.val, by rw [hn]; exact i.isLt⟩
  have H := FiniteLeafCoordinateBits.coordinate_at_solution (FlatFullSourceSampleSource.family F)
    (count F) (degreeBound F) (height F) (nonzero F) (degree_le F) (height_le F) a y hy j
  simpa only [coordinate, Function.comp_apply, prepareCoordinate, pairFst_pair, pairSnd_pair,
    rawCoordinate, a, j, y, theta] using H

theorem parameter_separable {K : Type*} [Field K] [CharZero K] (F : Inputs) (u : List Bool) :
    ((parameter F u).map (Int.castRingHom K)).Separable :=
  (FiniteAnnihilatorTree.parameter
    (fun i => (FlatFullSourceSampleSource.family F).polynomial
      (pair (FlatFullSourceSampleSource.prepare F u) (BinaryNatCode.encode i)))
    (count F (FlatFullSourceSampleSource.prepare F u))
    (nonzero F (FlatFullSourceSampleSource.prepare F u))).separable_in_field

/-- Every parameter root decodes to a tuple of coordinate-equation roots.
The complete flat equations and regularity still have to be checked. -/
theorem parameter_root_coordinates {K : Type*} [Field K] [CharZero K] (F : Inputs) (u : List Bool)
    (theta : K) (ht : (parameter F u).eval₂ (Int.castRingHom K) theta = 0)
    (i : Fin (FlatFullSourceSampleSource.count F u)) :
    (coordinate F (pair u (BinaryNatCode.encode i.val))).denominator.eval₂ (Int.castRingHom K) theta ≠ 0 ∧
      (FlatFullSourceSampleSource.polynomial F (pair u (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom K)
        ((coordinate F (pair u (BinaryNatCode.encode i.val))).eval theta) = 0 := by
  let a := FlatFullSourceSampleSource.prepare F u
  have hn : count F a = FlatFullSourceSampleSource.count F u := by
    simp only [count, a, FlatFullSourceSampleSource.prepare_source]
  let j : Fin (count F a) := ⟨i.val, by rw [hn]; exact i.isLt⟩
  have H := FiniteLeafCoordinateBits.finite_decode_spec (FlatFullSourceSampleSource.family F)
    (count F) (degreeBound F) (height F) (nonzero F) (degree_le F) (height_le F) a j theta ht
  have R := FiniteLeafCoordinateBits.original_root (FlatFullSourceSampleSource.family F)
    (count F) (degreeBound F) (height F) (nonzero F) (degree_le F) (height_le F) a j theta ht
  rw [FlatFullSourceSampleSource.prepared_polynomial F u j.val (by rw [← hn]; exact j.isLt)] at R
  constructor
  · simpa only [coordinate, Function.comp_apply, prepareCoordinate, pairFst_pair, pairSnd_pair,
      rawCoordinate, a, j] using H.1
  · simpa only [coordinate, Function.comp_apply, prepareCoordinate, pairFst_pair, pairSnd_pair,
      rawCoordinate, a, j] using R

/-- Distinct roots cannot encode the same complete flat tuple. -/
theorem parameter_roots_ext {K : Type*} [Field K] [CharZero K] (F : Inputs) (u : List Bool)
    (theta theta' : K) (ht : (parameter F u).eval₂ (Int.castRingHom K) theta = 0)
    (ht' : (parameter F u).eval₂ (Int.castRingHom K) theta' = 0)
    (he : ∀ i : Fin (FlatFullSourceSampleSource.count F u),
      (coordinate F (pair u (BinaryNatCode.encode i.val))).eval theta =
        (coordinate F (pair u (BinaryNatCode.encode i.val))).eval theta') : theta = theta' := by
  let a := FlatFullSourceSampleSource.prepare F u
  let p := fun j => (FlatFullSourceSampleSource.family F).polynomial (pair a (BinaryNatCode.encode j))
  have hn : count F a = FlatFullSourceSampleSource.count F u := by
    simp only [count, a, FlatFullSourceSampleSource.prepare_source]
  have hd : FiniteAnnihilatorTree.decode p (count F a) (nonzero F a) theta =
      FiniteAnnihilatorTree.decode p (count F a) (nonzero F a) theta' := by
    funext j
    let i : Fin (FlatFullSourceSampleSource.count F u) := ⟨j.val, by rw [← hn]; exact j.isLt⟩
    have H := FiniteLeafCoordinateBits.finite_decode_spec (FlatFullSourceSampleSource.family F)
      (count F) (degreeBound F) (height F) (nonzero F) (degree_le F) (height_le F) a j theta ht
    have H' := FiniteLeafCoordinateBits.finite_decode_spec (FlatFullSourceSampleSource.family F)
      (count F) (degreeBound F) (height F) (nonzero F) (degree_le F) (height_le F) a j theta' ht'
    have hi := he i
    have hi' : (rawCoordinate F (pair a (BinaryNatCode.encode j.val))).eval theta =
        (rawCoordinate F (pair a (BinaryNatCode.encode j.val))).eval theta' := by
      simpa only [coordinate, Function.comp_apply, prepareCoordinate, pairFst_pair, pairSnd_pair, a, i] using hi
    exact H.2.symm.trans (hi'.trans H'.2)
  have H := congrArg (FiniteAnnihilatorTree.encode p (count F a) (nonzero F a)) hd
  simpa only [FiniteAnnihilatorTree.encode_decode p (count F a) (nonzero F a) theta ht,
    FiniteAnnihilatorTree.encode_decode p (count F a) (nonzero F a) theta' ht'] using H

theorem regular_root_complete (F : Inputs) (u : List Bool)
    (z : Fin (FlatFullSourceSampleSource.count F u) → ℝ)
    (hz : ∀ i, (FlatFullSourcePositive.system F u i).eval₂ (Int.castRingHom ℝ) z = 0)
    (hr : (fderiv ℝ (fun y => fun i => (FlatFullSourcePositive.system F u i).eval₂ (Int.castRingHom ℝ) y) z).IsInvertible) :
    ∃ theta : ℝ, (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0 ∧
      ∀ i : Fin (FlatFullSourceSampleSource.count F u),
        (coordinate F (pair u (BinaryNatCode.encode i.val))).denominator.eval₂ (Int.castRingHom ℝ) theta ≠ 0 ∧
        (coordinate F (pair u (BinaryNatCode.encode i.val))).eval theta = z i := by
  apply tuple_complete F u z
  intro i
  rw [FlatFullSourceSampleSource.polynomial_packet]
  exact FlatFullSourcePositiveCoordinate.eval_regular_root F u z hz hr i

end LeanCanny.Encoding.FlatFullSourceSampleCoordinates
