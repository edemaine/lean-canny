/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleVertices

/-! # Native multivariate polynomial signs at regular square-system samples

Fixed even denominator powers turn an implicit multivariate test into a
univariate test at the same primitive parameter. Its sign equals the sign
at the decoded system root. Native test coefficients and binary budgets
suffice; no values or signs at sample roots are supplied.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSamplePolynomialTest
open LeanCanny.Algebra LeanCanny.Computation MatrixPower Brackets
open SquareSampleInput (Inputs)
open SquareSampleSource (count)
open SquareSampleCoordinates (parameter coordinateDegree coordinateMass)
open SquareSampleReaders (numerator denominator)
open SquareSampleParameters (decode)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Test (F : Inputs) where
  polynomial : (u : List Bool) → MvPolynomial (Fin (count F u)) ℤ
  degree : List Bool → ℕ
  mass : List Bool → ℕ
  polynomial_degree : ∀ u, (polynomial u).totalDegree ≤ degree u
  polynomial_mass : ∀ u, MvMass.mass (polynomial u) ≤ 2 ^ mass u

def width {F : Inputs} (T : Test F) (u : List Bool) : ℕ := (T.degree u).size

noncomputable def family {F : Inputs} (T : Test F) : FixedWidthRationalSubstitutionBits.Family where
  arity := count F
  width := width T
  source := T.polynomial
  numerator := numerator F
  denominator := denominator F
  degree_fit u i := (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt
    ((T.polynomial_degree u).trans_lt (Nat.lt_size_self _))

noncomputable def coefficient {F : Inputs} (T : Test F) (q : List Bool) : List Bool :=
  residueBits (((family T).coefficient (RationalSubstitution.IntegerBits.context q)
    (Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree q)) : ℤ) :
      ZMod (RationalSubstitution.IntegerBits.mValue q))

structure Test.Access {F : Inputs} (T : Test F) : Prop where
  degree : BinaryFn T.degree
  mass : BinaryFn T.mass
  coefficient : SpaceFunction (coefficient T)

theorem width_unary {F : Inputs} {T : Test F} (A : T.Access) : UnaryFn (width T) :=
  (UnaryFn.length A.degree.bits_mem_FP).of_eq (fun u => BinaryNatCode.length_encode (T.degree u))

theorem coefficient_packet {F : Inputs} (T : Test F) (u : List Bool) (r m : ℕ) (hm : 0 < m) :
    coefficient T (pair (pair u (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      residueBits (((family T).coefficient u r : ℤ) : ZMod m) := by
  unfold coefficient
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
    (by simp only [RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
    (by simp only [RationalSubstitution.IntegerBits.mValue, pairSnd_pair, BinaryNatCode.encode,
      Nat.fromBitsLE_bits]; omega)

noncomputable def access {F : Inputs} (h : F.Access) {T : Test F} (A : T.Access) :
    FixedWidthRationalSubstitutionBits.Access (family T) where
  arity := h.count
  width := width_unary A
  coefficient := coefficient T
  evaluator := A.coefficient
  coefficient_eq u r _ m hm := coefficient_packet T u r m hm
  coordinates := SquareSampleReaders.readers h

noncomputable def test {F : Inputs} (T : Test F) : SquareSampleTestMoments.Test where
  polynomial := (family T).polynomial
  degree := (family T).degree (coordinateDegree F)
  mass := (family T).mass T.mass (coordinateMass F)
  polynomial_degree := (family T).polynomial_degree (coordinateDegree F)
    (fun c i _ => (SquareSampleReaders.coordinate_bounds F c i).1)
    (fun c i _ => (SquareSampleReaders.coordinate_bounds F c i).2.1)
  polynomial_mass := (family T).polynomial_mass T.mass (coordinateMass F)
    (fun c _ _ => (MvMass.coeff_le _ _).trans (T.polynomial_mass c))
    (fun c i _ => (SquareSampleReaders.coordinate_bounds F c i).2.2.1)
    (fun c i _ => (SquareSampleReaders.coordinate_bounds F c i).2.2.2)

noncomputable def test_access {F : Inputs} (h : F.Access) {T : Test F} (A : T.Access) : (test T).Access :=
  SquareSampleTestMoments.Test.Access.ofPrimitive
    ((access h A).degree_binary (SquareSampleCoordinates.coordinateDegree_binary h))
    ((access h A).mass_binary A.mass (SquareSampleCoordinates.coordinateMass_binary h))
    (access h A).polynomialEvaluator

theorem sign (F : Inputs) (T : Test F) (u : List Bool) (theta : ℝ)
    (ht : (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0) :
    SquareSampleTestMoments.sign (test T) u theta =
      SignType.sign ((T.polynomial u).eval₂ (Int.castRingHom ℝ) (decode F u theta)) := by
  unfold SquareSampleTestMoments.sign
  rw [Polynomial.eval_map]
  exact (family T).sign u theta (fun i => SquareSampleReaders.denominator_ne_zero F u theta ht i)

noncomputable def value (F : Inputs) (T : Test F) : List Bool → List Bool :=
  SquareSampleVertices.signValue F (test T)

theorem evaluator {F : Inputs} (h : F.Access) {T : Test F} (A : T.Access) : SpaceFunction (value F T) :=
  SquareSampleVertices.sign_evaluator h (test_access h A)

theorem packet (F : Inputs) (T : Test F) (u w : List Bool) (hw : SquareSampleVertices.Valid F u w) :
    value F T (pair u w) = InfinitesimalSign.encode
      (SignType.sign ((T.polynomial u).eval₂ (Int.castRingHom ℝ)
        (SquareSampleVertices.sample F u w hw).val.val)) := by
  rw [value, SquareSampleVertices.sign_packet F (test T) u w hw]
  let x := SquareSampleHashEnumeration.root F u ⟨Nat.fromBitsLE w, hw.2⟩
  have hx := (SquareSampleQueries.mem_roots F u x.val).mp x.property
  rw [sign F T u x.val hx.1]
  rfl

noncomputable def rowTest (F : Inputs) (row : (u : List Bool) → Fin (count F u)) : Test F where
  polynomial u := F.system u (row u)
  degree := F.degree
  mass := F.mass
  polynomial_degree u := F.system_degree u (row u)
  polynomial_mass u := F.system_mass u (row u)

theorem rowTest_access {F : Inputs} (h : F.Access) (row : (u : List Bool) → Fin (count F u))
    (hr : UnaryFn (fun u => (row u).val)) : (rowTest F row).Access := by
  have E := SquareSampleInput.row_evaluator h RationalSubstitution.IntegerBits.context_mem_FP
    ((SquareSampleSource.width_unary h).comp RationalSubstitution.IntegerBits.context_mem_FP)
    (fun q => row (RationalSubstitution.IntegerBits.context q))
    (hr.comp RationalSubstitution.IntegerBits.context_mem_FP)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
  refine ⟨h.degree, h.mass, E.congr (funext fun q => ?_)⟩
  rw [FixedWidthPolynomial.nativeExponent_refl]
  rfl

theorem row_value (F : Inputs) (row : (u : List Bool) → Fin (count F u))
    (u w : List Bool) (hw : SquareSampleVertices.Valid F u w) :
    value F (rowTest F row) (pair u w) = InfinitesimalSign.encode 0 := by
  rw [packet F (rowTest F row) u w hw]
  have hz := (SquareSampleVertices.sample F u w hw).val.property (row u)
  change InfinitesimalSign.encode (SignType.sign ((F.system u (row u)).eval₂
    (Int.castRingHom ℝ) (SquareSampleVertices.sample F u w hw).val.val)) = _
  rw [hz, sign_zero]


noncomputable def language (F : Inputs) (T : Test F) (s : SignType) : Language :=
  {q | SquareSampleVertices.Valid F (pairFst q) (pairSnd q) ∧ value F T q = InfinitesimalSign.encode s}

noncomputable def accept (F : Inputs) (s : SignType) (z : List Bool) : Bool := decide
  ((pairSnd (pairFst z)).length = SquareSampleVertices.width F (pairFst (pairFst z)) ∧
    Nat.fromBitsLE (pairSnd (pairFst z)) < Nat.fromBitsLE (pairFst (pairSnd z)) ∧
      pairSnd (pairSnd z) = InfinitesimalSign.encode s)

theorem accept_FP {F : Inputs} (h : F.Access) (s : SignType) : (fun z => [accept F s z]) ∈ FP := by
  have hw := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hu := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hN := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hS := stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
    (constFn_mem_FP (InfinitesimalSign.encode s))
  exact ((FPPred.eq (UnaryFn.length hw) ((SquareSampleVertices.width_unary h).comp hu)).and
    (((BinaryFn.fromBits hw).lt hN).and hS)).flag_mem_FP

theorem decider {F : Inputs} (h : F.Access) {T : Test F} (A : T.Access) (s : SignType) :
    SpaceDecider (language F T s) := by
  have N := (SquareSampleRegularCount.evaluator h).precompose pairFst pairFst_mem_FP
  apply (N.pairOutputs (evaluator h A)).withInput.decider (accept F s) (accept_FP h s)
  intro q
  simp only [language, SquareSampleVertices.Valid, Set.mem_ofPred_eq, accept, Function.comp_apply,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]
  exact and_assoc

theorem mem_PSPACE {F : Inputs} (h : F.Access) {T : Test F} (A : T.Access) (s : SignType) :
    language F T s ∈ PSPACE := (decider h A s).mem_PSPACE

theorem language_packet (F : Inputs) (T : Test F) (s : SignType) (u w : List Bool)
    (hw : SquareSampleVertices.Valid F u w) :
    pair u w ∈ language F T s ↔
      SignType.sign ((T.polynomial u).eval₂ (Int.castRingHom ℝ)
        (SquareSampleVertices.sample F u w hw).val.val) = s := by
  change _ ∧ value F T (pair u w) = _ ↔ _
  rw [packet F T u w hw]
  have hv : SquareSampleVertices.Valid F (pairFst (pair u w)) (pairSnd (pair u w)) := by
    simpa only [pairFst_pair, pairSnd_pair] using hw
  rw [and_iff_right hv, SquareSampleTestSign.encode_eq_iff]

theorem language_invalid (F : Inputs) (T : Test F) (s : SignType) (q : List Bool)
    (hq : ¬ SquareSampleVertices.Valid F (pairFst q) (pairSnd q)) : q ∉ language F T s :=
  fun H => hq H.1


end LeanCanny.Encoding.SquareSamplePolynomialTest
