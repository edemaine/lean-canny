/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildFilters
public import LeanCanny.Algebra.SignPatternCountSpace

/-! # Native counting of child parameter roots satisfying the joint equations

The native zero-sign pattern imposes every joint row on a child parameter
root. The count includes precisely these finite coordinate-root candidates;
Jacobian and actual-parent filtering are still required for child samples.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildEquationCount
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open MatrixPower
open BoundedFullSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildCoordinates.parameter BoundedFullSampleChildFilters.polynomial
  BoundedFullSampleChildCoordinates.parameterDegree BoundedFullSampleChildCoordinates.baseHeight
  BoundedFullSampleChildFilters.degree BoundedFullSampleChildFilters.mass

noncomputable def family (F : Inputs) : SignPatternBits.Family where
  root := BoundedFullSampleChildCoordinates.parameter F
  polynomial c i := BoundedFullSampleChildFilters.polynomial F (pair c (BinaryNatCode.encode i))
  pattern _ _ := 0
  count c := BinaryNatCode.encode (BoundedFullSampleChildSource.count F c)
  rootDegree c := BinaryNatCode.encode (BoundedFullSampleChildCoordinates.parameterDegree F c + 1)
  degree c := BinaryNatCode.encode (BoundedFullSampleChildFilters.degree F c)
  rootMass c := BinaryNatCode.encode (BoundedFullSampleChildCoordinates.baseHeight F c)
  mass c := BinaryNatCode.encode (BoundedFullSampleChildFilters.mass F c)
  rootDegree_pos c := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega
  root_degree c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (BoundedFullSampleChildCoordinates.parameter_bounds F c).1.trans (Nat.le_succ _)
  root_mass c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (BoundedFullSampleChildCoordinates.parameter_bounds F c).2
  polynomial_degree c i _ := by
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, pairFst_pair] using
      BoundedFullSampleChildFilters.polynomial_degree F (pair c (BinaryNatCode.encode i))
  polynomial_mass c i _ := by
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, pairFst_pair] using
      BoundedFullSampleChildFilters.polynomial_mass F (pair c (BinaryNatCode.encode i))

theorem controls {F : Inputs} (h : F.PolyTime) : SignPatternBits.ControlsPolyTime (family F) := by
  constructor
  · exact (BinaryFn.ofUnary (BoundedFullSampleChildSource.count_unary h)).bits_mem_FP
  · simpa only [family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using BoundedFullSampleChildSource.count_unary h
  · exact ((BoundedFullSampleChildCoordinates.parameterDegree_binary h).add (BinaryFn.const 1)).bits_mem_FP
  · exact (BoundedFullSampleChildFilters.degree_binary h).bits_mem_FP
  · exact (BoundedFullSampleChildCoordinates.baseHeight_binary h).bits_mem_FP
  · exact (BoundedFullSampleChildFilters.mass_binary h).bits_mem_FP

def filterQuery : List Bool → List Bool := BoundedFullSampleChildReaders.query

theorem filterQuery_FP : filterQuery ∈ FP := BoundedFullSampleChildReaders.query_FP

noncomputable def access (F : Inputs) : SignPatternBits.Access (family F) where
  rootCoefficient := PrimitivePairBits.coefficient (BoundedFullSampleChildCoordinates.parameter F)
  polynomialCoefficient := PrimitivePairBits.coefficient (BoundedFullSampleChildFilters.polynomial F) ∘ filterQuery
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
      (by simp only [filterQuery, BoundedFullSampleChildReaders.query, RationalSubstitution.IntegerBits.context,
        RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
      (by simp only [filterQuery, BoundedFullSampleChildReaders.query, RationalSubstitution.IntegerBits.mValue,
        pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
  pattern_eq _ _ := rfl

noncomputable def count (F : Inputs) (c : List Bool) : ℕ := Nat.card (BoundedFullSampleChildFilters.Roots F c)

theorem rootCount_eq_count (F : Inputs) (c : List Bool) : SignPatternBits.rootCount (family F) c = count F c := by
  let p := (BoundedFullSampleChildCoordinates.parameter F c).map (algebraMap ℤ ℝ)
  let Z := p.roots.toFinset.filter (fun theta => ∀ i : Fin (BoundedFullSampleChildSource.count F c),
    SignType.sign (((BoundedFullSampleChildFilters.polynomial F (pair c (BinaryNatCode.encode i.val))).map
      (algebraMap ℤ ℝ)).eval theta) = 0)
  have hp : p ≠ 0 := (Polynomial.map_ne_zero_iff (show Function.Injective (algebraMap ℤ ℝ) from Int.cast_injective)).mpr
    (BoundedFullSampleChildCoordinates.parameter_ne_zero F c)
  have hm : algebraMap ℤ ℝ = Int.castRingHom ℝ := RingHom.ext_int _ _
  have hz (theta : ℝ) : theta ∈ Z ↔ BoundedFullSampleChildFilters.Valid F c theta := by
    rw [BoundedFullSampleChildFilters.valid_iff_filters]
    simp only [Z, Finset.mem_filter, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hp]
    simp only [Polynomial.IsRoot.def, p, Polynomial.eval_map, hm, sign_eq_zero_iff]
  calc
    SignPatternBits.rootCount (family F) c = Z.card := by
      simp only [SignPatternBits.rootCount, RootSignQueries.signCount, family]
      rw [show Nat.fromBitsLE (BinaryNatCode.encode (BoundedFullSampleChildSource.count F c)) = BoundedFullSampleChildSource.count F c from Nat.fromBitsLE_bits _]
    _ = Nat.card {theta : ℝ // theta ∈ Z} := by simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card (BoundedFullSampleChildFilters.Roots F c) := Nat.card_congr (Equiv.subtypeEquivRight hz)
    _ = count F c := rfl

theorem evaluator {F : Inputs} (h : F.PolyTime) :
    SpaceFunction (fun c => BinaryNatCode.encode (count F c)) := by
  have E := SignPatternBits.rootCountEvaluator (access F) (controls h)
    (constFn_mem_FP (InfinitesimalSign.encode 0))
    (BoundedFullSampleChildCoordinates.parameter_coefficient_evaluator h)
    ((BoundedFullSampleChildFilters.evaluator h).precompose filterQuery filterQuery_FP)
  exact E.congr (funext fun c => congrArg BinaryNatCode.encode (rootCount_eq_count F c))

def language (F : Inputs) : Language := {u | Nonempty (BoundedFullSampleChildFilters.Roots F u)}

theorem language_eq_realizable (F : Inputs) : language F = SignPatternBits.realizableLanguage (family F) := by
  ext u
  have hm : algebraMap ℤ ℝ = Int.castRingHom ℝ := RingHom.ext_int _ _
  change Nonempty (BoundedFullSampleChildFilters.Roots F u) ↔
    ∃ theta : ℝ, (((family F).root u).map (algebraMap ℤ ℝ)).eval theta = 0 ∧
      ∀ i : Fin (Nat.fromBitsLE ((family F).count u)),
        SignType.sign ((((family F).polynomial u i.val).map (algebraMap ℤ ℝ)).eval theta) = (family F).pattern u i.val
  rw [show Nat.fromBitsLE ((family F).count u) = BoundedFullSampleChildSource.count F u from Nat.fromBitsLE_bits _]
  simp only [family, Polynomial.eval_map, hm, sign_eq_zero_iff]
  constructor
  · rintro ⟨theta⟩
    exact ⟨theta.val, (BoundedFullSampleChildFilters.valid_iff_filters F u theta.val).mp theta.property⟩
  · rintro ⟨theta, ht, hz⟩
    exact ⟨⟨theta, (BoundedFullSampleChildFilters.valid_iff_filters F u theta).mpr ⟨ht, hz⟩⟩⟩

theorem language_mem_PSPACE {F : Inputs} (h : F.PolyTime) : language F ∈ PSPACE := by
  rw [language_eq_realizable]
  exact SignPatternBits.realizableLanguage_mem_PSPACE (access F) (controls h)
    (constFn_mem_FP (InfinitesimalSign.encode 0))
    (BoundedFullSampleChildCoordinates.parameter_coefficient_evaluator h)
    ((BoundedFullSampleChildFilters.evaluator h).precompose filterQuery filterQuery_FP)
    (BoundedFullSampleChildCoordinates.parameter_ne_zero F)

end LeanCanny.Encoding.BoundedFullSampleChildEquationCount
