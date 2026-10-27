/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalFilterBounds
public import LeanCanny.Algebra.SignPatternCountSpace

/-! # Native counting of the actual complete real critical samples

The zero sign pattern enforces every cleared source equation at a root of
the computed common parameter. The filtered-root bijection proves that the
native count is the number of actual samples, rather than coordinate tuples.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleCount
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameter BoundedCriticalFilters.polynomial
  BoundedCriticalRationalCoordinates.parameterDegree BoundedCriticalRationalCoordinates.baseHeight
  BoundedCriticalFilterBounds.degree BoundedCriticalFilterBounds.mass

noncomputable def family (P : Readers) : SignPatternBits.Family where
  root := BoundedCriticalRationalCoordinates.parameter P
  polynomial c i := BoundedCriticalFilters.polynomial P (pair c (BinaryNatCode.encode i))
  pattern _ _ := 0
  count c := BinaryNatCode.encode (P.dim c + 4)
  rootDegree c := BinaryNatCode.encode (BoundedCriticalRationalCoordinates.parameterDegree P c + 1)
  degree c := BinaryNatCode.encode (BoundedCriticalFilterBounds.degree P c)
  rootMass c := BinaryNatCode.encode (BoundedCriticalRationalCoordinates.baseHeight P c)
  mass c := BinaryNatCode.encode (BoundedCriticalFilterBounds.mass P c)
  rootDegree_pos c := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega
  root_degree c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (BoundedCriticalRationalCoordinates.parameter_bounds P c).1.trans (Nat.le_succ _)
  root_mass c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (BoundedCriticalRationalCoordinates.parameter_bounds P c).2
  polynomial_degree c i _ := by
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, pairFst_pair] using
      BoundedCriticalFilterBounds.polynomial_degree P (pair c (BinaryNatCode.encode i))
  polynomial_mass c i _ := by
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, pairFst_pair] using
      BoundedCriticalFilterBounds.polynomial_mass P (pair c (BinaryNatCode.encode i))

theorem controls {P : Readers} (h : P.PolyTime) : SignPatternBits.ControlsPolyTime (family P) := by
  constructor
  · exact (BinaryFn.ofUnary (h.dim.add (UnaryFn.const 4))).bits_mem_FP
  · simpa only [family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using h.dim.add (UnaryFn.const 4)
  · exact ((BoundedCriticalRationalCoordinates.parameterDegree_binary h).add (BinaryFn.const 1)).bits_mem_FP
  · exact (BoundedCriticalFilterBounds.degree_binary h).bits_mem_FP
  · exact (BoundedCriticalRationalCoordinates.baseHeight_binary h).bits_mem_FP
  · exact (BoundedCriticalFilterBounds.mass_binary h).bits_mem_FP

def filterQuery (q : List Bool) : List Bool :=
  pair (pair (pair (RationalSubstitution.IntegerBits.context q)
    (pairFst (RationalSubstitution.IntegerBits.selectedDegree q)))
      (pairSnd (RationalSubstitution.IntegerBits.selectedDegree q))) (pairSnd q)

theorem filterQuery_FP : filterQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP
    (mem_FP_comp RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairFst_mem_FP))
      (mem_FP_comp RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def access (P : Readers) : SignPatternBits.Access (family P) where
  rootCoefficient := PrimitivePairBits.coefficient (BoundedCriticalRationalCoordinates.parameter P)
  polynomialCoefficient := PrimitivePairBits.coefficient (BoundedCriticalFilters.polynomial P) ∘ filterQuery
  pattern _ := InfinitesimalSign.encode 0
  root_eq c k m hm := by
    simp only [PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.coefficientResidue,
      IntegerTarskiSeedBits.integerResidue]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
      (by simp only [RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
      (by simp only [RationalSubstitution.IntegerBits.mValue, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
  polynomial_eq c i _ k m hm := by
    simp only [Function.comp_apply, PrimitivePairBits.coefficient,
      RationalSubstitution.IntegerBits.coefficientResidue, IntegerTarskiSeedBits.integerResidue]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
      (by simp only [filterQuery, RationalSubstitution.IntegerBits.context,
        RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
      (by simp only [filterQuery, RationalSubstitution.IntegerBits.mValue,
        pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
  pattern_eq _ _ := rfl

noncomputable def count (P : Readers) (c : List Bool) : ℕ := Nat.card (BoundedFullCriticalSamples.Samples P c)

theorem rootCount_eq_count (P : Readers) (c : List Bool) : SignPatternBits.rootCount (family P) c = count P c := by
  let p := (BoundedCriticalRationalCoordinates.parameter P c).map (algebraMap ℤ ℝ)
  let Z := p.roots.toFinset.filter (fun theta => ∀ i : Fin (P.dim c + 4),
    SignType.sign (((BoundedCriticalFilters.polynomial P (pair c (BinaryNatCode.encode i.val))).map
      (algebraMap ℤ ℝ)).eval theta) = 0)
  have hp : p ≠ 0 := (Polynomial.map_ne_zero_iff (show Function.Injective (algebraMap ℤ ℝ) from Int.cast_injective)).mpr
    (BoundedCriticalRationalCoordinates.parameter_ne_zero P c)
  have hm : algebraMap ℤ ℝ = Int.castRingHom ℝ := RingHom.ext_int _ _
  have hz (theta : ℝ) : theta ∈ Z ↔ BoundedCriticalFilters.Valid P c theta := by
    rw [BoundedCriticalFilters.valid_iff_filters]
    simp only [Z, Finset.mem_filter, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hp]
    simp only [Polynomial.IsRoot.def, p, Polynomial.eval_map, hm, sign_eq_zero_iff]
  calc
    SignPatternBits.rootCount (family P) c = Z.card := by
      simp only [SignPatternBits.rootCount, RootSignQueries.signCount, family]
      rw [show Nat.fromBitsLE (BinaryNatCode.encode (P.dim c + 4)) = P.dim c + 4 from Nat.fromBitsLE_bits _]
    _ = Nat.card {theta : ℝ // theta ∈ Z} := by simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card (BoundedCriticalFilters.Roots P c ℝ) := Nat.card_congr (Equiv.subtypeEquivRight hz)
    _ = count P c := Nat.card_congr (BoundedCriticalFilters.realEquiv P c)

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => BinaryNatCode.encode (count P c)) := by
  have E := SignPatternBits.rootCountEvaluator (access P) (controls h)
    (constFn_mem_FP (InfinitesimalSign.encode 0))
    (BoundedCriticalRationalCoordinates.parameter_coefficient_evaluator h ha)
    ((BoundedCriticalFilterCoefficients.evaluator h ha).precompose filterQuery filterQuery_FP)
  exact E.congr (funext fun c => congrArg BinaryNatCode.encode (rootCount_eq_count P c))

end LeanCanny.Encoding.BoundedCriticalSampleCount
