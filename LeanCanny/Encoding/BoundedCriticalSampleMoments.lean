/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleThom
public import LeanCanny.Algebra.FilteredSignMoments

/-! # Native sparse moments on actual full critical samples

The source equations filter the native common-parameter roots before selected
derivative-sign moments are summed. Extraneous coordinate tuples contribute
nothing. Feature counts are unary FP; derivative orders remain binary.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameter
  BoundedCriticalRationalCoordinates.parameterDegree BoundedCriticalRationalCoordinates.baseHeight
  BoundedCriticalFilters.polynomial PrimitivePairBits.coefficient

noncomputable def family (P : Readers) (features : List Bool → ℕ)
    (orders : List Bool → List Bool) : SignPatternBits.Family :=
  { BoundedCriticalSampleCount.family P with
    polynomial := fun c i => BoundedCriticalSampleThom.polynomial P c
      (Nat.fromBitsLE (orders (pair c (BinaryNatCode.encode i))))
    count := fun c => BinaryNatCode.encode (features c)
    degree := fun c => BinaryNatCode.encode (BoundedCriticalRationalCoordinates.parameterDegree P c)
    mass := fun c => BinaryNatCode.encode (BoundedCriticalSampleThom.massExponent P c)
    polynomial_degree := fun c _ _ => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      exact BoundedCriticalSampleThom.degree P c _
    polynomial_mass := fun c _ _ => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      exact BoundedCriticalSampleThom.mass_bound P c _ }

theorem controls {P : Readers} {features : List Bool → ℕ}
    (h : P.PolyTime) (hc : UnaryFn features) (orders : List Bool → List Bool) :
    SignPatternBits.ControlsPolyTime (family P features orders) := by
  refine ⟨bits_mem_FP hc, ?_, (BoundedCriticalSampleCount.controls h).rootDegree,
    (BoundedCriticalRationalCoordinates.parameterDegree_binary h).bits_mem_FP,
    (BoundedCriticalSampleCount.controls h).rootMass, (BoundedCriticalSampleThom.massExponent_binary h).bits_mem_FP⟩
  simpa only [family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hc

def query (orders : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (BoundedCriticalSampleThom.original q)
    (pair (BinaryNatCode.encode (Nat.fromBitsLE (orders
      (pair (BoundedCriticalSampleThom.original q) (BoundedCriticalSampleThom.order q)))))
      (BoundedCriticalSampleThom.index q))) (pairSnd q)

theorem query_FP {orders : List Bool → List Bool} (ho : orders ∈ FP) : query orders ∈ FP := by
  have hi := mem_FP_comp (mem_FP_pair BoundedCriticalSampleThom.original_FP BoundedCriticalSampleThom.order_FP) ho
  have hn := (BinaryFn.fromBits hi).bits_mem_FP
  exact mem_FP_pair (mem_FP_pair BoundedCriticalSampleThom.original_FP
    (mem_FP_pair hn BoundedCriticalSampleThom.index_FP)) pairSnd_mem_FP

noncomputable def access (P : Readers) (features : List Bool → ℕ)
    (orders : List Bool → List Bool) : SignPatternBits.Access (family P features orders) where
  rootCoefficient := (BoundedCriticalSampleCount.access P).rootCoefficient
  polynomialCoefficient := BoundedCriticalSampleThom.value P ∘ query orders
  pattern _ := []
  root_eq := (BoundedCriticalSampleCount.access P).root_eq
  polynomial_eq c i _ k m hm := by
    simp only [Function.comp_apply, query, BoundedCriticalSampleThom.original, BoundedCriticalSampleThom.order,
      BoundedCriticalSampleThom.index, pairFst_pair, pairSnd_pair]
    generalize hw : BinaryNatCode.encode (m - 1) = w
    have he : Nat.fromBitsLE w + 1 = m := by
      rw [← hw]
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      omega
    subst m
    exact BoundedCriticalSampleThom.value_packet P c _ k w
  pattern_eq _ _ := rfl

theorem acceptedRoots_eq (P : Readers) (c : List Bool) :
    SignPatternBits.acceptedRoots (BoundedCriticalSampleCount.family P) c =
      BoundedCriticalSampleLabels.rootSet P c := by
  ext theta
  rw [BoundedCriticalSampleLabels.mem_rootSet, BoundedCriticalFilters.valid_iff_filters]
  simp only [SignPatternBits.acceptedRoots, BoundedCriticalSampleCount.family, Finset.mem_filter,
    Multiset.mem_toFinset, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hm : algebraMap ℤ ℝ = Int.castRingHom ℝ := RingHom.ext_int _ _
  rw [hm, Polynomial.mem_roots (BoundedCriticalSampleLabels.mapped_ne_zero P c)]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_map, sign_eq_zero_iff, Fin.forall_iff]

noncomputable def moment (P : Readers) (features : List Bool → ℕ)
    (orders : List Bool → List Bool) (q : List Bool) : ℤ :=
  FilteredSignMomentBits.moment (BoundedCriticalSampleCount.family P) (family P features orders) q

theorem moment_eq_sum (P : Readers) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (q : List Bool) :
    moment P features orders q = ∑ x ∈ BoundedCriticalSampleLabels.rootSet P (pairFst q),
      ∏ i ∈ Finset.range (features (pairFst q)),
        (SignType.sign ((BoundedCriticalSampleThom.polynomial P (pairFst q)
          (Nat.fromBitsLE (orders (pair (pairFst q) (BinaryNatCode.encode i))))).eval₂
            (Int.castRingHom ℝ) x) : ℤ) ^
          (Ternary.exponent (features (pairFst q)) (Nat.fromBitsLE (pairSnd q)) i).val := by
  simp only [moment, FilteredSignMomentBits.moment, acceptedRoots_eq, family,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Polynomial.eval_map, algebraMap_int_eq]

theorem moment_bound (P : Readers) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (q : List Bool) :
    (moment P features orders q).natAbs ≤ 2 ^ BoundedFullCriticalSamples.labelWidth P (pairFst q) := by
  have H := FilteredSignMomentBits.moment_abs_le_count
    (BoundedCriticalSampleCount.family P) (family P features orders) q
  rw [BoundedCriticalSampleCount.rootCount_eq_count] at H
  exact H.trans (BoundedFullCriticalSamples.finite_samples P (pairFst q)).2

attribute [local irreducible] BoundedCriticalSampleThom.value query

theorem evaluator {P : Readers} {features : List Bool → ℕ} {orders : List Bool → List Bool}
    (h : P.PolyTime) (hc : UnaryFn features) (ho : orders ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P features orders q)) := by
  have H := BoundedCriticalRationalCoordinates.parameter_coefficient_evaluator h ha
  have Q := (BoundedCriticalFilterCoefficients.evaluator h ha).precompose
    BoundedCriticalSampleCount.filterQuery BoundedCriticalSampleCount.filterQuery_FP
  have T := (BoundedCriticalSampleThom.evaluator h ha).precompose (query orders) (query_FP ho)
  exact FilteredSignMomentBits.evaluator (BoundedCriticalSampleCount.access P) (access P features orders)
    (BoundedCriticalSampleCount.controls h) (controls h hc orders) (constFn_mem_FP []) H Q T

end LeanCanny.Encoding.BoundedCriticalSampleMoments
