/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompletePolynomialTest
public import LeanCanny.Encoding.SquareSampleIndexedSign
public import LeanCanny.Algebra.CoordinateReaders

/-! # Indexed polynomial signs at complete square-system vertices

The source and its vertex label stay fixed while extra fields select a
multivariate test. Rational coordinates, primitive parameters, and the grid
sampler retain the original context. Original-equation validity includes
singular roots and rejects invalid labels.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteIndexedPolynomialTest
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open SquareSampleInput (Inputs)
open SquareSampleCoordinates (coordinateDegree coordinateMass)
open SquareSampleReaders (numerator denominator)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

structure Test (F : Inputs) where
  polynomial : (c d : List Bool) → MvPolynomial (Fin (F.count c)) ℤ
  degree : List Bool → ℕ
  mass : List Bool → ℕ
  polynomial_degree : ∀ z, (polynomial (pairFst z) (pairSnd z)).totalDegree ≤ degree z
  polynomial_mass : ∀ z, MvMass.mass (polynomial (pairFst z) (pairSnd z)) ≤ 2 ^ mass z

def width {F : Inputs} (T : Test F) (z : List Bool) : ℕ := (T.degree z).size

noncomputable def family {F : Inputs} (T : Test F) : FixedWidthRationalSubstitutionBits.Family where
  arity z := F.count (pairFst z)
  width := width T
  source z := T.polynomial (pairFst z) (pairSnd z)
  numerator z := numerator F (pairFst z)
  denominator z := denominator F (pairFst z)
  degree_fit z i := (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt
    ((T.polynomial_degree z).trans_lt (Nat.lt_size_self _))

noncomputable def coefficient {F : Inputs} (T : Test F) (q : List Bool) : List Bool :=
  residueBits (((family T).coefficient (RationalSubstitution.IntegerBits.context q)
    (Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree q))) : ZMod (RationalSubstitution.IntegerBits.mValue q))

structure Test.Access {F : Inputs} (T : Test F) : Prop where
  degree : BinaryFn T.degree
  mass : BinaryFn T.mass
  coefficient : SpaceFunction (coefficient T)

theorem width_unary {F : Inputs} {T : Test F} (A : T.Access) : UnaryFn (width T) :=
  (UnaryFn.length A.degree.bits_mem_FP).of_eq (fun z => BinaryNatCode.length_encode (T.degree z))

theorem coefficient_packet {F : Inputs} (T : Test F) (z : List Bool) (k m : ℕ) (hm : 0 < m) :
    coefficient T (pair (pair z (BinaryNatCode.encode k)) (BinaryNatCode.encode (m - 1))) =
      residueBits (((family T).coefficient z k) : ZMod m) := by
  unfold coefficient
  exact congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m))
    (by simp only [RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
    (by simp only [RationalSubstitution.IntegerBits.mValue, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)

noncomputable def access {F : Inputs} (h : F.Access) {T : Test F} (A : T.Access) :
    FixedWidthRationalSubstitutionBits.Access (family T) where
  arity := h.count.comp pairFst_mem_FP
  width := width_unary A
  coefficient := coefficient T
  evaluator := A.coefficient
  coefficient_eq z k _ m hm := coefficient_packet T z k m hm
  coordinates := (SquareSampleReaders.readers h).precompose pairFst pairFst_mem_FP

noncomputable def test {F : Inputs} (T : Test F) : SquareSampleTestMoments.Test where
  polynomial := (family T).polynomial
  degree := (family T).degree (coordinateDegree F ∘ pairFst)
  mass := (family T).mass T.mass (coordinateMass F ∘ pairFst)
  polynomial_degree := (family T).polynomial_degree (coordinateDegree F ∘ pairFst)
    (fun z i _ => (SquareSampleReaders.coordinate_bounds F (pairFst z) i).1)
    (fun z i _ => (SquareSampleReaders.coordinate_bounds F (pairFst z) i).2.1)
  polynomial_mass := (family T).polynomial_mass T.mass (coordinateMass F ∘ pairFst)
    (fun z _ _ => (MvMass.coeff_le _ _).trans (T.polynomial_mass z))
    (fun z i _ => (SquareSampleReaders.coordinate_bounds F (pairFst z) i).2.2.1)
    (fun z i _ => (SquareSampleReaders.coordinate_bounds F (pairFst z) i).2.2.2)

noncomputable def testAccess {F : Inputs} (h : F.Access) {T : Test F} (A : T.Access) : (test T).Access :=
  SquareSampleTestMoments.Test.Access.ofPrimitive
    ((access h A).degree_binary ((SquareSampleCoordinates.coordinateDegree_binary h).comp pairFst_mem_FP))
    ((access h A).mass_binary A.mass ((SquareSampleCoordinates.coordinateMass_binary h).comp pairFst_mem_FP))
    (access h A).polynomialEvaluator

theorem sign (F : Inputs) (T : Test F) (z : List Bool) (theta : ℝ)
    (ht : (SquareSampleCoordinates.parameter F (pairFst z)).eval₂ (Int.castRingHom ℝ) theta = 0) :
    SquareSampleTestMoments.sign (test T) z theta =
      SignType.sign ((T.polynomial (pairFst z) (pairSnd z)).eval₂ (Int.castRingHom ℝ)
        (SquareSampleParameters.decode F (pairFst z) theta)) := by
  unfold SquareSampleTestMoments.sign
  rw [Polynomial.eval_map]
  exact (family T).sign z theta (fun i => SquareSampleReaders.denominator_ne_zero F (pairFst z) theta ht i)

def query (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (BinaryNat.normalize (pairSnd (pairFst q)))) (pairSnd q)
theorem query_FP : query ∈ FP := by polytime [query]

noncomputable def value (F : Inputs) (T : Test F) : List Bool → List Bool :=
  SquareSampleIndexedSign.atOrdinal (SquareSampleGrid.input F) (test T) ∘ query

theorem evaluator {F : Inputs} (h : F.Access) {T : Test F} (A : T.Access) : SpaceFunction (value F T) :=
  (SquareSampleIndexedSign.ordinal_evaluator (SquareSampleGrid.access h) (testAccess h A)).precompose query query_FP

theorem packet (F : Inputs) (T : Test F) (c w d : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F c w) : value F T (pair (pair c w) d) = InfinitesimalSign.encode
      (SignType.sign ((T.polynomial c d).eval₂ (Int.castRingHom ℝ)
        (SquareSampleCompleteVertices.candidate F c w hw).val)) := by
  have hg := Classical.choose hw
  have H := SquareSampleIndexedSign.ordinal_packet (SquareSampleGrid.input F) (test T) c d ⟨Nat.fromBitsLE w, hg.2⟩
  have ht := (SquareSampleQueries.mem_roots (SquareSampleGrid.input F) c
    (SquareSampleCompleteVertices.theta F c w hg).val).mp (SquareSampleCompleteVertices.theta F c w hg).property
  rw [SquareSampleGrid.parameter_eq] at ht
  have hq : query (pair (pair c w) d) = pair (pair c (BinaryNatCode.encode (Nat.fromBitsLE w))) d := by
    simp only [query, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]
  rw [value, Function.comp_apply, hq, H,
    sign F T (pair c d) _ (by simpa only [pairFst_pair, SquareSampleCompleteVertices.theta] using ht.1)]
  simp only [pairSnd_pair]
  refine (congrArg (fun v : List Bool => InfinitesimalSign.encode (SignType.sign
    ((T.polynomial v d).eval₂ (Int.castRingHom ℝ) (SquareSampleParameters.decode F v
      (SquareSampleHashEnumeration.root (SquareSampleGrid.input F) c ⟨Nat.fromBitsLE w, hg.2⟩).val))))
    (pairFst_pair c d)).trans ?_
  rfl

noncomputable def language (F : Inputs) (T : Test F) (s : SignType) : Language :=
  {q | SquareSampleCompleteVertices.Valid F (pairFst (pairFst q)) (pairSnd (pairFst q)) ∧ value F T q = InfinitesimalSign.encode s}

theorem decider {F : Inputs} (h : F.Access) {T : Test F} (A : T.Access) (s : SignType) : SpaceDecider (language F T s) := by
  have V := ((SquareSampleCompleteVertices.decider h).precompose pairFst pairFst_mem_FP).flagEvaluator
  apply (V.pairOutputs (evaluator h A)).decider
    (fun q => decide (pairFst q = [true] ∧ pairSnd q = InfinitesimalSign.encode s))
    ((Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).and
      (Brackets.stringEq_fppred pairSnd_mem_FP (constFn_mem_FP _))).flag_mem_FP
  intro q
  simp only [language, SquareSampleCompleteVertices.language, Set.mem_ofPred_eq, Set.mem_preimage,
    pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) {T : Test F} (A : T.Access) (s : SignType) :
    language F T s ∈ PSPACE := (decider h A s).mem_PSPACE

end LeanCanny.Encoding.SquareSampleCompleteIndexedPolynomialTest
