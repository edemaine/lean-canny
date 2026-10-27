/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleTermCoordinates
public import LeanCanny.Encoding.BoundedCriticalSampleIndexedSign

/-! # Native arithmetic-term signs at actual sample descriptors

Even denominator powers clear an encoded term on the computed rational
coordinates. Native modular coefficient readers and source-derived bounds
instantiate indexed sign probes in the unchanged actual-sample frame.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleTermTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open RationalSubstitutionBits BoundedCriticalSampleTestMoments Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleTermCoordinates.numerator
  BoundedCriticalSampleTermCoordinates.denominator BoundedCriticalRationalCoordinates.coordinateDegree
  BoundedCriticalRationalCoordinates.coordinateMass PrimitivePairBits.coefficient

noncomputable def source (read : List Bool → List Bool) : Source := Source.ofTerm read
noncomputable def size (read : List Bool → List Bool) (u : List Bool) : ℕ := (TermView.term (read u)).toData.size

theorem size_unary (read : List Bool → List Bool) (hr : read ∈ FP) : UnaryFn (size read) :=
  (UnaryFn.length (mem_FP_comp hr TermView.normalize_mem_FP)).of_eq (fun u => by
    simp only [Function.comp_apply, size, TermView.normalize_eq_term, Data.length_toBits])

theorem arity_eq (read : List Bool → List Bool) (u : List Bool) :
    Nat.fromBitsLE ((source read).arity u) = size read u := by
  simp only [source, Source.ofTerm, size, TermView.normalize_eq_term, Data.length_toBits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem exponent_bound (read : List Bool → List Bool) (u : List Bool) (r i : ℕ) :
    ((source read).syntax u).monomialExponent r i ≤ 2 * size read u :=
  (((source read).syntax u).monomialExponent_le r i).trans
    ((((source read).syntax u).degreeBound_le_dataSize).trans (Nat.le_mul_of_pos_left _ (by decide)))

noncomputable def polynomial (P : Readers) (read : List Bool → List Bool) : List Bool → ℤ[X] :=
  (BoundedCriticalSampleTermCoordinates.coordinates P (source read)).family.polynomial

noncomputable def degree (P : Readers) (read : List Bool → List Bool) (u : List Bool) : ℕ :=
  size read u * (2 * size read u) * BoundedCriticalRationalCoordinates.coordinateDegree P (pairFst u)
noncomputable def mass (P : Readers) (read : List Bool → List Bool) (u : List Bool) : ℕ :=
  2 * size read u + size read u * (2 * size read u) * BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u) + 1

theorem polynomial_degree (P : Readers) (read : List Bool → List Bool) (u : List Bool) :
    (polynomial P read u).natDegree ≤ degree P read u := by
  change (RationalSubstitution.Indexed.cleared (Nat.fromBitsLE ((source read).arity u))
    ((source read).syntax u).monomialCount (2 * size read u)
    ((source read).syntax u).monomialCoefficient ((source read).syntax u).monomialExponent
    (BoundedCriticalSampleTermCoordinates.numerator P u) (BoundedCriticalSampleTermCoordinates.denominator P u)).natDegree ≤ _
  rw [arity_eq]
  exact RationalSubstitution.Indexed.natDegree_cleared_le _ _ _ _ _ _ _ _
    (fun r _ i _ => exponent_bound read u r i)
    (fun i _ => BoundedCriticalSampleTermCoordinates.numerator_degree P u i)
    (fun i _ => BoundedCriticalSampleTermCoordinates.denominator_degree P u i)

theorem polynomial_mass (P : Readers) (read : List Bool → List Bool) (u : List Bool) :
    coefficientMass (polynomial P read u) ≤ 2 ^ mass P read u := by
  have H := RationalSubstitution.Indexed.coefficientMass_cleared_le_pow
    (size read u) ((source read).syntax u).monomialCount (2 * size read u) (size read u)
    (BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u))
    ((source read).syntax u).monomialCoefficient ((source read).syntax u).monomialExponent
    (BoundedCriticalSampleTermCoordinates.numerator P u) (BoundedCriticalSampleTermCoordinates.denominator P u)
    (fun r _ i _ => exponent_bound read u r i)
    (fun r _ => ((source read).syntax u).monomialCoefficient_natAbs_le_pow_dataSize r)
    (fun i _ => BoundedCriticalSampleTermCoordinates.numerator_mass P u i)
    (fun i _ => BoundedCriticalSampleTermCoordinates.denominator_mass P u i)
  change coefficientMass (RationalSubstitution.Indexed.cleared (Nat.fromBitsLE ((source read).arity u))
    ((source read).syntax u).monomialCount (2 * size read u)
    ((source read).syntax u).monomialCoefficient ((source read).syntax u).monomialExponent
    (BoundedCriticalSampleTermCoordinates.numerator P u) (BoundedCriticalSampleTermCoordinates.denominator P u)) ≤ _
  rw [arity_eq]
  apply H.trans (Nat.pow_le_pow_right (by decide) ?_)
  have hc := ((source read).syntax u).monomialCount_size_le
  change _ ≤ size read u + 1 at hc
  unfold mass
  omega

noncomputable def test (P : Readers) (read : List Bool → List Bool) : Test where
  polynomial := polynomial P read
  degree := degree P read
  mass := mass P read
  polynomial_degree := polynomial_degree P read
  polynomial_mass := polynomial_mass P read

theorem degree_binary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) :
    BinaryFn (degree P read) := by
  have hs := BinaryFn.ofUnary (size_unary read hr)
  exact (hs.mul ((BinaryFn.const 2).mul hs)).mul
    ((BoundedCriticalRationalCoordinates.coordinateDegree_binary h).comp pairFst_mem_FP)

theorem mass_binary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) :
    BinaryFn (mass P read) := by
  have hs := BinaryFn.ofUnary (size_unary read hr)
  exact (((BinaryFn.const 2).mul hs).add ((hs.mul ((BinaryFn.const 2).mul hs)).mul
    ((BoundedCriticalRationalCoordinates.coordinateMass_binary h).comp pairFst_mem_FP))).add (BinaryFn.const 1)

noncomputable def access {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : (test P read).Access := by
  have E := (BoundedCriticalSampleTermCoordinates.coordinates P (source read)).evaluator
    (Source.ofTerm_polyTime hr) (BoundedCriticalSampleTermCoordinates.numerator_evaluator h ha)
      (BoundedCriticalSampleTermCoordinates.denominator_evaluator h ha)
  apply Test.Access.ofPrimitive (degree_binary h read hr) (mass_binary h read hr)
  exact E.congr (funext fun q => by
    simp only [RationalSubstitution.IntegerBits.Family.value, PrimitivePairBits.coefficient, test, polynomial])

theorem sign_sample (P : Readers) (read : List Bool → List Bool) (c d : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) :
    sign (test P read) (pair c d) (BoundedCriticalSampleLabels.parameter P c x).val =
      SignType.sign ((TermView.term (read (pair c d))).eval (Formula.extend x.val)) := by
  rw [sign, Polynomial.eval_map]
  change SignType.sign ((RationalSubstitution.Indexed.cleared
    (Nat.fromBitsLE ((source read).arity (pair c d))) ((source read).syntax (pair c d)).monomialCount
    (2 * size read (pair c d)) ((source read).syntax (pair c d)).monomialCoefficient
    ((source read).syntax (pair c d)).monomialExponent (BoundedCriticalSampleTermCoordinates.numerator P (pair c d))
    (BoundedCriticalSampleTermCoordinates.denominator P (pair c d))).eval₂ (Int.castRingHom ℝ)
      (BoundedCriticalSampleLabels.parameter P c x).val) = _
  rw [RationalSubstitution.Indexed.sign_eval₂_cleared _ _ _ _ _ _ _ _ _
    (fun r _ i _ => exponent_bound read (pair c d) r i)
    (fun i _ => BoundedCriticalSampleTermCoordinates.denominator_nonzero P c d x i)]
  have H := ((source read).syntax (pair c d)).eval₂_indexed_source
    (fun i => (BoundedCriticalSampleTermCoordinates.numerator P (pair c d) i).eval₂ (Int.castRingHom ℝ)
      (BoundedCriticalSampleLabels.parameter P c x).val /
        (BoundedCriticalSampleTermCoordinates.denominator P (pair c d) i).eval₂ (Int.castRingHom ℝ)
          (BoundedCriticalSampleLabels.parameter P c x).val) _ ((source read).scope (pair c d))
  refine (congrArg SignType.sign H).trans ?_
  congr 1
  apply Term.eval_congr
  intro i _
  exact BoundedCriticalSampleTermCoordinates.coordinate_eval P c d x i

theorem value_sample (P : Readers) (read : List Bool → List Bool) (c d : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) :
    BoundedCriticalSampleIndexedSign.value P (test P read)
      (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d) =
        InfinitesimalSign.encode (SignType.sign ((TermView.term (read (pair c d))).eval (Formula.extend x.val))) := by
  rw [BoundedCriticalSampleIndexedSign.value_sample, sign_sample]

end LeanCanny.Encoding.BoundedCriticalSampleTermTest
