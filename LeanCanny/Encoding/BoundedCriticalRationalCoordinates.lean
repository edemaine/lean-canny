/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalLeafSource
public import LeanCanny.Algebra.FiniteLeafCoordinateCorrect

/-! # Native rational coordinates for critical coordinate-root tuples

The prepared coordinate annihilators feed the existing balanced primitive
tree. Every tuple of their roots has a common parameter, with nonvanishing
coordinate denominators and native numerator and denominator readers. The
tuple may be filtered later by the original critical equations.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalRationalCoordinates
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FiniteLeafCoordinateBits.coordinate

noncomputable def count (P : Readers) (c : List Bool) : ℕ := BoundedCriticalLeafSource.count P (pairFst c)
noncomputable def degreeBound (P : Readers) (c : List Bool) : ℕ :=
  FiniteSourceDegreePreparation.degreeBudget (BoundedCriticalLeafSource.degreeBound P) (pairFst c)
noncomputable def height (P : Readers) (c : List Bool) : ℕ := BoundedCriticalLeafSource.massBound P (pairFst c)

theorem nonzero (P : Readers) (c : List Bool) (i : ℕ) (_hi : i < count P c) :
    (BoundedCriticalLeafSource.family P).polynomial (pair c (BinaryNatCode.encode i)) ≠ 0 :=
  BoundedCriticalLeafSource.family_nonzero _ _

theorem degree_le (P : Readers) (c : List Bool) (i : ℕ) (_hi : i < count P c) :
    ((BoundedCriticalLeafSource.family P).polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ degreeBound P c :=
  (FiniteSourceDegreePreparation.family_degree _ _ _ _ (BoundedCriticalLeafSource.source_mass P) c i).le

theorem height_le (P : Readers) (c : List Bool) (i : ℕ) (_hi : i < count P c) :
    (BoundedCriticalLeafSource.family P).height (pair c (BinaryNatCode.encode i)) ≤ height P c := by
  rw [BoundedCriticalLeafSource.family, FiniteSourceDegreePreparation.family_height, pairFst_pair]
  exact le_rfl

theorem count_unary {P : Readers} (h : P.PolyTime) : UnaryFn (count P) :=
  (BoundedCriticalLeafSource.count_unary h).comp pairFst_mem_FP
theorem degreeBound_binary {P : Readers} (h : P.PolyTime) : BinaryFn (degreeBound P) :=
  (FiniteSourceDegreePreparation.degreeBudget_binary (BoundedCriticalLeafSource.degreeBound_binary h)).comp pairFst_mem_FP
theorem height_binary {P : Readers} (h : P.PolyTime) : BinaryFn (height P) :=
  (BoundedCriticalLeafSource.massBound_binary h).comp pairFst_mem_FP

noncomputable def rawCoordinate (P : Readers) :=
  FiniteLeafCoordinateBits.coordinate (BoundedCriticalLeafSource.family P) (count P) (degreeBound P) (height P) (nonzero P)

noncomputable def prepareCoordinate (P : Readers) (u : List Bool) : List Bool :=
  pair (BoundedCriticalLeafSource.prepare P (pairFst u)) (pairSnd u)

theorem prepareCoordinate_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (prepareCoordinate P) :=
  ((BoundedCriticalLeafSource.prepare_evaluator h ha).precompose pairFst pairFst_mem_FP).pairOutputs
    (SpaceFunction.ofFP _ pairSnd_mem_FP)

noncomputable def coordinate (P : Readers) : List Bool → UnivariateRational.Coordinate :=
  rawCoordinate P ∘ prepareCoordinate P

noncomputable def baseHeight (P : Readers) (c : List Bool) : ℕ :=
  FiniteAnnihilatorTree.sourceHeight
    (FiniteSourceDegreePreparation.degreeBudget (BoundedCriticalLeafSource.degreeBound P) c)
    (BoundedCriticalLeafSource.massBound P c) (BoundedCriticalLeafSource.count P c)

noncomputable def coordinateDegree (P : Readers) (c : List Bool) : ℕ :=
  (baseHeight P c ^ 3) ^ (BoundedCriticalLeafSource.count P c).size
noncomputable def coordinateMass (P : Readers) (c : List Bool) : ℕ :=
  (BoundedCriticalLeafSource.count P c).size * coordinateDegree P c * baseHeight P c ^ 10

theorem baseHeight_binary {P : Readers} (h : P.PolyTime) : BinaryFn (baseHeight P) :=
  FiniteAnnihilatorTree.sourceHeight_binary
    (FiniteSourceDegreePreparation.degreeBudget_binary (BoundedCriticalLeafSource.degreeBound_binary h))
    (BoundedCriticalLeafSource.massBound_binary h) (BoundedCriticalLeafSource.count_unary h)
theorem coordinateDegree_binary {P : Readers} (h : P.PolyTime) : BinaryFn (coordinateDegree P) :=
  ((baseHeight_binary h).powUnary (UnaryFn.const 3)).powUnary ((BoundedCriticalLeafSource.count_unary h).size)
theorem coordinateMass_binary {P : Readers} (h : P.PolyTime) : BinaryFn (coordinateMass P) :=
  ((BinaryFn.ofUnary (BoundedCriticalLeafSource.count_unary h).size).mul (coordinateDegree_binary h)).mul
    ((baseHeight_binary h).powUnary (UnaryFn.const 10))

theorem prepared_controls (P : Readers) (u : List Bool) :
    FiniteLeafCoordinateBits.degreeControl (count P) (degreeBound P) (height P) (prepareCoordinate P u) =
        baseHeight P (pairFst u) ^ 3 ∧
      FiniteLeafCoordinateBits.massControl (count P) (degreeBound P) (height P) (prepareCoordinate P u) =
        baseHeight P (pairFst u) ^ 10 ∧
      FiniteLeafPathContext.depth (count P) (prepareCoordinate P u) = (BoundedCriticalLeafSource.count P (pairFst u)).size := by
  simp only [FiniteLeafCoordinateBits.degreeControl, FiniteLeafCoordinateBits.massControl,
    CanonicalPairBits.degreeBudget, CanonicalPairBits.massBudget, CanonicalNodeBits.heightBudget,
    FiniteLeafPathContext.leafContext, BalancedParameterContext.original_packet,
    FiniteLeafPathContext.depth, prepareCoordinate, pairFst_pair, count, degreeBound, height,
    BoundedCriticalLeafSource.prepare_source]
  exact ⟨rfl, rfl, trivial⟩

theorem coordinate_bounds (P : Readers) (u : List Bool) :
    (coordinate P u).degree ≤ coordinateDegree P (pairFst u) ∧
      coefficientMass (coordinate P u).numerator ≤ 2 ^ coordinateMass P (pairFst u) ∧
      coefficientMass (coordinate P u).denominator ≤ 2 ^ coordinateMass P (pairFst u) := by
  have H := FiniteLeafCoordinateBits.coordinate_bounds (BoundedCriticalLeafSource.family P)
    (count P) (degreeBound P) (height P) (nonzero P) (degree_le P) (height_le P) (prepareCoordinate P u)
  rw [(prepared_controls P u).1, (prepared_controls P u).2.1, (prepared_controls P u).2.2] at H
  exact H

theorem raw_coefficient_evaluators {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (PrimitivePairBits.coefficient (fun u => (rawCoordinate P u).numerator)) ∧
      SpaceFunction (PrimitivePairBits.coefficient (fun u => (rawCoordinate P u).denominator)) :=
  FiniteLeafCoordinateBits.coefficientEvaluators (BoundedCriticalLeafSource.family P)
    (count P) (degreeBound P) (height P) (nonzero P) (degree_le P) (height_le P)
    (BoundedCriticalLeafSource.readers h ha) (count_unary h) (degreeBound_binary h) (height_binary h)

theorem coefficient_evaluators {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (PrimitivePairBits.coefficient (fun u => (coordinate P u).numerator)) ∧
      SpaceFunction (PrimitivePairBits.coefficient (fun u => (coordinate P u).denominator)) := by
  have E := raw_coefficient_evaluators h ha
  exact ⟨PrimitivePairBits.withContextEvaluator (fun u => (rawCoordinate P u).numerator)
      (prepareCoordinate P) (prepareCoordinate_evaluator h ha) E.1,
    PrimitivePairBits.withContextEvaluator (fun u => (rawCoordinate P u).denominator)
      (prepareCoordinate P) (prepareCoordinate_evaluator h ha) E.2⟩

noncomputable def rawParameter (P : Readers) : List Bool → Polynomial ℤ :=
  FiniteAnnihilatorBits.finiteParameter (BoundedCriticalLeafSource.family P) (count P) (nonzero P)

noncomputable def parameter (P : Readers) : List Bool → Polynomial ℤ :=
  rawParameter P ∘ BoundedCriticalLeafSource.prepare P

noncomputable def parameterDegree (P : Readers) (c : List Bool) : ℕ :=
  FiniteSourceDegreePreparation.degreeBudget (BoundedCriticalLeafSource.degreeBound P) c ^
    BoundedCriticalLeafSource.count P c

theorem parameterDegree_binary {P : Readers} (h : P.PolyTime) : BinaryFn (parameterDegree P) :=
  (FiniteSourceDegreePreparation.degreeBudget_binary (BoundedCriticalLeafSource.degreeBound_binary h)).powUnary
    (BoundedCriticalLeafSource.count_unary h)

theorem parameter_ne_zero (P : Readers) (c : List Bool) : parameter P c ≠ 0 :=
  (FiniteAnnihilatorTree.parameter
    (fun i => (BoundedCriticalLeafSource.family P).polynomial
      (pair (BoundedCriticalLeafSource.prepare P c) (BinaryNatCode.encode i)))
    (count P (BoundedCriticalLeafSource.prepare P c)) (nonzero P (BoundedCriticalLeafSource.prepare P c))).ne_zero

theorem parameter_bounds (P : Readers) (c : List Bool) :
    (parameter P c).natDegree ≤ parameterDegree P c ∧
      coefficientMass (parameter P c) ≤ 2 ^ baseHeight P c := by
  let a := BoundedCriticalLeafSource.prepare P c
  let p := fun i => (BoundedCriticalLeafSource.family P).polynomial (pair a (BinaryNatCode.encode i))
  have hd := FiniteAnnihilatorTree.parameter_degree_le p (count P a) (nonzero P a) (degreeBound P a) (degree_le P a)
  have hb (i : ℕ) (hi : i < count P a) (k : ℕ) : ((p i).coeff k).natAbs ≤ 2 ^ height P a :=
    ((BoundedCriticalLeafSource.family P).coefficient_bound _ k).trans
      (Nat.pow_le_pow_right (by decide) (height_le P a i hi))
  have hm := FiniteAnnihilatorTree.parameter_mass_from_source p (count P a) (nonzero P a)
    (degreeBound P a) (height P a) (degree_le P a) hb
  constructor
  · simpa only [parameter, rawParameter, Function.comp_apply, FiniteAnnihilatorBits.finiteParameter,
      p, a, count, degreeBound, BoundedCriticalLeafSource.prepare_source, parameterDegree] using hd
  · simpa only [parameter, rawParameter, Function.comp_apply, FiniteAnnihilatorBits.finiteParameter,
      p, a, count, degreeBound, height, BoundedCriticalLeafSource.prepare_source, baseHeight] using hm

theorem parameter_coefficient_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (PrimitivePairBits.coefficient (parameter P)) := by
  have R := FiniteAnnihilatorBits.coefficientEvaluator (BoundedCriticalLeafSource.family P)
    (BoundedCriticalLeafSource.readers h ha) (count P) (degreeBound P) (height P)
    (count_unary h) (degreeBound_binary h) (height_binary h) (nonzero P) (degree_le P) (height_le P)
  have R' : SpaceFunction (PrimitivePairBits.coefficient (rawParameter P)) := R.congr (funext fun _ => rfl)
  exact PrimitivePairBits.withContextEvaluator _ _ (BoundedCriticalLeafSource.prepare_evaluator h ha) R'

/-- Every tuple satisfying the original coordinate equations is recovered by
one root of the native parameter polynomial, with every denominator nonzero. -/
theorem tuple_complete (P : Readers) (c : List Bool) {K : Type*} [Field K] [CharZero K]
    (x : Fin (BoundedCriticalLeafSource.count P c) → K)
    (hx : ∀ i, (BoundedCriticalCoordinate.polynomial P (pair c (BinaryNatCode.encode i.val))).eval₂
      (Int.castRingHom K) (x i) = 0) :
    ∃ theta : K, (parameter P c).eval₂ (Int.castRingHom K) theta = 0 ∧
      ∀ i : Fin (BoundedCriticalLeafSource.count P c),
        (coordinate P (pair c (BinaryNatCode.encode i.val))).denominator.eval₂ (Int.castRingHom K) theta ≠ 0 ∧
        (coordinate P (pair c (BinaryNatCode.encode i.val))).eval theta = x i := by
  let a := BoundedCriticalLeafSource.prepare P c
  have hn : count P a = BoundedCriticalLeafSource.count P c := by
    simp only [count, a, BoundedCriticalLeafSource.prepare_source]
  let y : Fin (count P a) → K := fun j => x ⟨j.val, by rw [← hn]; exact j.isLt⟩
  have hy (j : Fin (count P a)) :
      ((BoundedCriticalLeafSource.family P).polynomial (pair a (BinaryNatCode.encode j.val))).eval₂
        (Int.castRingHom K) (y j) = 0 := by
    rw [BoundedCriticalLeafSource.prepared_polynomial P c j.val (by rw [← hn]; exact j.isLt)]
    exact hx ⟨j.val, by rw [← hn]; exact j.isLt⟩
  let theta := FiniteAnnihilatorTree.encode
    (fun j => (BoundedCriticalLeafSource.family P).polynomial (pair a (BinaryNatCode.encode j)))
    (count P a) (nonzero P a) y
  refine ⟨theta, FiniteAnnihilatorTree.encode_root _ _ _ y hy, ?_⟩
  intro i
  let j : Fin (count P a) := ⟨i.val, by rw [hn]; exact i.isLt⟩
  have H := FiniteLeafCoordinateBits.coordinate_at_solution (BoundedCriticalLeafSource.family P)
    (count P) (degreeBound P) (height P) (nonzero P) (degree_le P) (height_le P) a y hy j
  simpa only [coordinate, Function.comp_apply, prepareCoordinate, pairFst_pair, pairSnd_pair,
    rawCoordinate, a, j, y, theta] using H

theorem sample_complete (P : Readers) (c : List Bool) (x : BoundedFullComplexSamples.Samples P c) :
    ∃ theta : ℂ, (parameter P c).eval₂ (Int.castRingHom ℂ) theta = 0 ∧
      ∀ i : Fin (P.dim c + 4),
        (coordinate P (pair c (BinaryNatCode.encode i.val))).denominator.eval₂ (Int.castRingHom ℂ) theta ≠ 0 ∧
        (coordinate P (pair c (BinaryNatCode.encode i.val))).eval theta = x.val i :=
  tuple_complete P c x.val (fun i => BoundedCriticalCoordinate.eval_coordinate P c i x)

theorem real_sample_complete (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    ∃ theta : ℝ, (parameter P c).eval₂ (Int.castRingHom ℝ) theta = 0 ∧
      ∀ i : Fin (P.dim c + 4),
        (coordinate P (pair c (BinaryNatCode.encode i.val))).denominator.eval₂ (Int.castRingHom ℝ) theta ≠ 0 ∧
        (coordinate P (pair c (BinaryNatCode.encode i.val))).eval theta = x.val i :=
  tuple_complete P c x.val (fun i => BoundedCriticalCoordinate.eval_real_coordinate P c i x)

end LeanCanny.Encoding.BoundedCriticalRationalCoordinates
