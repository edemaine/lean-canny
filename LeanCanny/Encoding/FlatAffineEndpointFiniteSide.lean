/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteMidpoint
public import LeanCanny.Encoding.SquareSampleCompleteIndexedPolynomialTest
public import LeanCanny.Algebra.FrozenRetainedComparisonSpace
public import LeanCanny.Geometry.EndpointMidpoint
public import LeanCanny.Computation.SpaceFunctionBinaryQuantifiers

/-! # Native coordinate side tests at jointly labeled endpoint tuples -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteSide
open LeanCanny.Algebra LeanCanny.Computation MatrixPower Polynomial
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def originalCount (F : Inputs) (s : List Bool) : ℕ := count F (pairFst (pairFst s))
theorem originalCount_unary {F : Inputs} (h : F.Access) : UnaryFn (originalCount F) :=
  (FlatAffineFullSourcePositive.count_unary h).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)

def coordinate (F : Inputs) (s d : List Bool) : Fin (originalCount F s) :=
  ⟨min (Nat.fromBitsLE d) (originalCount F s - 1), by
    have := FlatAffineFullSourcePositive.count_pos F (pairFst (pairFst s))
    dsimp only [originalCount]
    omega⟩

theorem coordinate_unary {F : Inputs} (h : F.Access) :
    UnaryFn (fun z => (coordinate F (pairFst z) (pairSnd z)).val) :=
  UnaryFn.fromBitsLE_min pairSnd_mem_FP (((originalCount_unary h).comp pairFst_mem_FP).sub (UnaryFn.const 1))

theorem coordinate_encode (F : Inputs) (s : List Bool) (i : Fin (originalCount F s)) :
    coordinate F s (BinaryNatCode.encode i.val) = i := by
  apply Fin.ext
  simp only [coordinate, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact Nat.min_eq_left (by have := i.isLt; omega)

noncomputable def polynomial (comparison : Bool) (F : Inputs) (s : List Bool) (i : Fin (originalCount F s)) :
    MvPolynomial (Fin (FlatAffineEndpointFiniteFrame.arity F s)) ℤ :=
  if comparison then FrozenRetainedComparisonBits.polynomial i else FrozenRetainedMidpointBits.polynomial i

noncomputable def test (comparison : Bool) (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) :
    SquareSampleCompleteIndexedPolynomialTest.Test (FlatAffineEndpointFiniteSample.input F cone height) where
  polynomial s d := polynomial comparison F s (coordinate F s d)
  degree _ := 1
  mass _ := 2
  polynomial_degree z := by
    cases comparison
    · exact FrozenRetainedMidpointBits.degree_le _
    · exact FrozenRetainedComparisonBits.degree_le _
  polynomial_mass z := by
    cases comparison
    · exact FrozenRetainedMidpointBits.mass_le _
    · exact (FrozenRetainedComparisonBits.mass_le _).trans (by decide)

theorem testAccess {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (comparison : Bool) : (test comparison F cone height).Access := by
  have hc := RationalSubstitution.IntegerBits.context_mem_FP
  have hN := (originalCount_unary h).comp (mem_FP_comp hc pairFst_mem_FP)
  have hi := (coordinate_unary h).comp hc
  have E : SpaceFunction (FixedWidthRowBits.value
      (fun q => 1 * (3 * originalCount F (pairFst (RationalSubstitution.IntegerBits.context q)) + 1) + 1)
      (fun _ => (1 : ℕ).size)
      (fun q => polynomial comparison F (pairFst (RationalSubstitution.IntegerBits.context q))
        (coordinate F (pairFst (RationalSubstitution.IntegerBits.context q)) (pairSnd (RationalSubstitution.IntegerBits.context q))))
      RationalSubstitution.IntegerBits.selectedDegree pairSnd) := by
    cases comparison
    · exact FrozenRetainedMidpointBits.evaluator hN (UnaryFn.const (1 : ℕ).size) _ hi
        RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
    · exact FrozenRetainedComparisonBits.evaluator hN (UnaryFn.const (1 : ℕ).size) _ hi
        RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
  refine ⟨BinaryFn.const 1, BinaryFn.const 2, E.congr (funext fun q => ?_)⟩
  dsimp only [FixedWidthRowBits.value]
  rw [FixedWidthPolynomial.nativeExponent_refl]
  rfl

noncomputable def value (comparison : Bool) (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : List Bool → List Bool :=
  SquareSampleCompleteIndexedPolynomialTest.value (FlatAffineEndpointFiniteSample.input F cone height) (test comparison F cone height)

theorem evaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (comparison : Bool) :
    SpaceFunction (value comparison F cone height) :=
  SquareSampleCompleteIndexedPolynomialTest.evaluator (FlatAffineEndpointFiniteSample.sampleAccess h cone height hh)
    (testAccess h cone height comparison)

theorem tuple_packet (comparison : Bool) (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (a t : ℝ) (current left right : Fin (originalCount F s) → ℝ)
    (he : (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
      Geometry.FlatAffineEndpointFiniteLift.point F s a t current left right) (i : Fin (originalCount F s)) :
    value comparison F cone height (pair (pair s w) (BinaryNatCode.encode i.val)) =
      InfinitesimalSign.encode (SignType.sign (if comparison then left i - right i else 2 * current i - left i - right i)) := by
  rw [value, SquareSampleCompleteIndexedPolynomialTest.packet _ _ s w _ hw]
  change InfinitesimalSign.encode (SignType.sign ((polynomial comparison F s
    (coordinate F s (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom ℝ)
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val)) = _
  rw [coordinate_encode, he]
  cases comparison
  · exact congrArg (fun z : ℝ => InfinitesimalSign.encode (SignType.sign z))
      (Geometry.FlatAffineEndpointFiniteLift.midpoint_eval F s i a t current left right)
  · exact congrArg (fun z : ℝ => InfinitesimalSign.encode (SignType.sign z))
      (FrozenRetainedComparisonBits.eval_point i a t current left right)

def accept (z : List Bool) : Bool := decide
  ((pairFst z = InfinitesimalSign.encode .neg → pairSnd z = InfinitesimalSign.encode .neg) ∧
    (pairFst z = InfinitesimalSign.encode .pos → pairSnd z = InfinitesimalSign.encode .pos))

theorem accept_FP : (fun z => [accept z]) ∈ FP := by
  have N := (Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP (InfinitesimalSign.encode .neg))).not.or
    (Brackets.stringEq_fppred pairSnd_mem_FP (constFn_mem_FP (InfinitesimalSign.encode .neg)))
  have P := (Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP (InfinitesimalSign.encode .pos))).not.or
    (Brackets.stringEq_fppred pairSnd_mem_FP (constFn_mem_FP (InfinitesimalSign.encode .pos)))
  refine mem_FP_of_eq (N.and P).flag_mem_FP (fun z => ?_)
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [accept, decide_eq_true_eq]
  tauto

attribute [local irreducible] value test

noncomputable def check (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : List Bool :=
  [accept (pair (value true F cone height q) (value false F cone height q))]

theorem checkEvaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (check F cone height) :=
  ((evaluator h cone height hh true).pairOutputs (evaluator h cone height hh false)).postcompose _ accept_FP

noncomputable def passes (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : Prop :=
  ∀ k < originalCount F (pairFst q), check F cone height (pair q (BinaryNatCode.encode k)) = [true]

theorem scanEvaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (fun q => [decide (passes F cone height q)]) := by
  have E := (checkEvaluator h cone height hh).forall_binary (BinaryFn.ofUnary ((originalCount_unary h).comp pairFst_mem_FP))
  exact E.congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [passes, decide_eq_true_eq])

theorem tuple_side (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (a t : ℝ) (current left right : Fin (originalCount F s) → ℝ)
    (he : (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
      Geometry.FlatAffineEndpointFiniteLift.point F s a t current left right) :
    passes F cone height (pair s w) ↔ Geometry.EndpointMidpoint.Side left right current := by
  have H (i : Fin (originalCount F s)) : check F cone height (pair (pair s w) (BinaryNatCode.encode i.val)) = [true] ↔
      (left i < right i → current i < (left i + right i) / 2) ∧
        (right i < left i → (left i + right i) / 2 < current i) := by
    simp only [check, accept, pairFst_pair, pairSnd_pair,
      tuple_packet true F cone height s w hw a t current left right he i,
      tuple_packet false F cone height s w hw a t current left right he i,
      Bool.false_eq_true, ite_false, ite_true, List.cons.injEq, and_true, decide_eq_true_eq, SquareSampleTestSign.encode_eq_iff]
    change ((SignType.sign (left i - right i) = -1 → SignType.sign (2 * current i - left i - right i) = -1) ∧
      (SignType.sign (left i - right i) = 1 → SignType.sign (2 * current i - left i - right i) = 1)) ↔ _
    rw [sign_eq_neg_one_iff, sign_eq_neg_one_iff, sign_eq_one_iff, sign_eq_one_iff]
    constructor <;> rintro ⟨hL, hR⟩ <;> constructor
    · intro hxy; have := hL (by linarith); linarith
    · intro hyx; have := hR (by linarith); linarith
    · intro hxy; have := hL (by linarith); linarith
    · intro hyx; have := hR (by linarith); linarith
  constructor
  · intro hp i
    exact (H i).mp (hp i.val (by simpa only [pairFst_pair] using i.isLt))
  · intro hp k hk
    have hk' : k < originalCount F s := by simpa only [pairFst_pair] using hk
    exact (H ⟨k, hk'⟩).mpr (hp ⟨k, hk'⟩)

end LeanCanny.Encoding.FlatAffineEndpointFiniteSide
