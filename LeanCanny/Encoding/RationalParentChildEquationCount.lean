/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildFilters
public import LeanCanny.Algebra.SignPatternCountSpace

/-! # Native counting of child parameter roots satisfying the joint equations

The native zero-sign pattern imposes every joint row on a child parameter
root. The count includes precisely these finite coordinate-root candidates;
Jacobian and actual-parent filtering are still required for child samples.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildEquationCount
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open MatrixPower
open RationalParentChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildCoordinates.parameter RationalParentChildFilters.polynomial
  RationalParentChildCoordinates.parameterDegree RationalParentChildCoordinates.baseHeight
  RationalParentChildFilters.degree RationalParentChildFilters.mass

noncomputable def family (F : Inputs) : SignPatternBits.Family where
  root := RationalParentChildCoordinates.parameter F
  polynomial c i := RationalParentChildFilters.polynomial F (pair c (BinaryNatCode.encode i))
  pattern _ _ := 0
  count c := BinaryNatCode.encode (RationalParentChildSource.count F c)
  rootDegree c := BinaryNatCode.encode (RationalParentChildCoordinates.parameterDegree F c + 1)
  degree c := BinaryNatCode.encode (RationalParentChildFilters.degree F c)
  rootMass c := BinaryNatCode.encode (RationalParentChildCoordinates.baseHeight F c)
  mass c := BinaryNatCode.encode (RationalParentChildFilters.mass F c)
  rootDegree_pos c := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega
  root_degree c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (RationalParentChildCoordinates.parameter_bounds F c).1.trans (Nat.le_succ _)
  root_mass c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (RationalParentChildCoordinates.parameter_bounds F c).2
  polynomial_degree c i _ := by
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, pairFst_pair] using
      RationalParentChildFilters.polynomial_degree F (pair c (BinaryNatCode.encode i))
  polynomial_mass c i _ := by
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, pairFst_pair] using
      RationalParentChildFilters.polynomial_mass F (pair c (BinaryNatCode.encode i))

theorem controls {F : Inputs} (h : F.Access) : SignPatternBits.ControlsPolyTime (family F) := by
  constructor
  · exact (BinaryFn.ofUnary (RationalParentChildSource.count_unary h)).bits_mem_FP
  · simpa only [family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using RationalParentChildSource.count_unary h
  · exact ((RationalParentChildCoordinates.parameterDegree_binary h).add (BinaryFn.const 1)).bits_mem_FP
  · exact (RationalParentChildFilters.degree_binary h).bits_mem_FP
  · exact (RationalParentChildCoordinates.baseHeight_binary h).bits_mem_FP
  · exact (RationalParentChildFilters.mass_binary h).bits_mem_FP

def filterQuery : List Bool → List Bool := RationalParentChildReaders.query

theorem filterQuery_FP : filterQuery ∈ FP := RationalParentChildReaders.query_FP

noncomputable def access (F : Inputs) : SignPatternBits.Access (family F) where
  rootCoefficient := PrimitivePairBits.coefficient (RationalParentChildCoordinates.parameter F)
  polynomialCoefficient := PrimitivePairBits.coefficient (RationalParentChildFilters.polynomial F) ∘ filterQuery
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
      (by simp only [filterQuery, RationalParentChildReaders.query, RationalSubstitution.IntegerBits.context,
        RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
      (by simp only [filterQuery, RationalParentChildReaders.query, RationalSubstitution.IntegerBits.mValue,
        pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
  pattern_eq _ _ := rfl

noncomputable def count (F : Inputs) (c : List Bool) : ℕ := Nat.card (RationalParentChildFilters.Roots F c)

theorem rootCount_eq_count (F : Inputs) (c : List Bool) : SignPatternBits.rootCount (family F) c = count F c := by
  let p := (RationalParentChildCoordinates.parameter F c).map (algebraMap ℤ ℝ)
  let Z := p.roots.toFinset.filter (fun theta => ∀ i : Fin (RationalParentChildSource.count F c),
    SignType.sign (((RationalParentChildFilters.polynomial F (pair c (BinaryNatCode.encode i.val))).map
      (algebraMap ℤ ℝ)).eval theta) = 0)
  have hp : p ≠ 0 := (Polynomial.map_ne_zero_iff (show Function.Injective (algebraMap ℤ ℝ) from Int.cast_injective)).mpr
    (RationalParentChildCoordinates.parameter_ne_zero F c)
  have hm : algebraMap ℤ ℝ = Int.castRingHom ℝ := RingHom.ext_int _ _
  have hz (theta : ℝ) : theta ∈ Z ↔ RationalParentChildFilters.Valid F c theta := by
    rw [RationalParentChildFilters.valid_iff_filters]
    simp only [Z, Finset.mem_filter, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hp]
    simp only [Polynomial.IsRoot.def, p, Polynomial.eval_map, hm, sign_eq_zero_iff]
  calc
    SignPatternBits.rootCount (family F) c = Z.card := by
      simp only [SignPatternBits.rootCount, RootSignQueries.signCount, family]
      rw [show Nat.fromBitsLE (BinaryNatCode.encode (RationalParentChildSource.count F c)) = RationalParentChildSource.count F c from Nat.fromBitsLE_bits _]
    _ = Nat.card {theta : ℝ // theta ∈ Z} := by simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card (RationalParentChildFilters.Roots F c) := Nat.card_congr (Equiv.subtypeEquivRight hz)
    _ = count F c := rfl

theorem evaluator {F : Inputs} (h : F.Access) :
    SpaceFunction (fun c => BinaryNatCode.encode (count F c)) := by
  have E := SignPatternBits.rootCountEvaluator (access F) (controls h)
    (constFn_mem_FP (InfinitesimalSign.encode 0))
    (RationalParentChildCoordinates.parameter_coefficient_evaluator h)
    ((RationalParentChildFilters.evaluator h).precompose filterQuery filterQuery_FP)
  exact E.congr (funext fun c => congrArg BinaryNatCode.encode (rootCount_eq_count F c))

def language (F : Inputs) : Language := {u | Nonempty (RationalParentChildFilters.Roots F u)}

theorem language_eq_realizable (F : Inputs) : language F = SignPatternBits.realizableLanguage (family F) := by
  ext u
  have hm : algebraMap ℤ ℝ = Int.castRingHom ℝ := RingHom.ext_int _ _
  change Nonempty (RationalParentChildFilters.Roots F u) ↔
    ∃ theta : ℝ, (((family F).root u).map (algebraMap ℤ ℝ)).eval theta = 0 ∧
      ∀ i : Fin (Nat.fromBitsLE ((family F).count u)),
        SignType.sign ((((family F).polynomial u i.val).map (algebraMap ℤ ℝ)).eval theta) = (family F).pattern u i.val
  rw [show Nat.fromBitsLE ((family F).count u) = RationalParentChildSource.count F u from Nat.fromBitsLE_bits _]
  simp only [family, Polynomial.eval_map, hm, sign_eq_zero_iff]
  constructor
  · rintro ⟨theta⟩
    exact ⟨theta.val, (RationalParentChildFilters.valid_iff_filters F u theta.val).mp theta.property⟩
  · rintro ⟨theta, ht, hz⟩
    exact ⟨⟨theta, (RationalParentChildFilters.valid_iff_filters F u theta).mpr ⟨ht, hz⟩⟩⟩

theorem language_mem_PSPACE {F : Inputs} (h : F.Access) : language F ∈ PSPACE := by
  rw [language_eq_realizable]
  exact SignPatternBits.realizableLanguage_mem_PSPACE (access F) (controls h)
    (constFn_mem_FP (InfinitesimalSign.encode 0))
    (RationalParentChildCoordinates.parameter_coefficient_evaluator h)
    ((RationalParentChildFilters.evaluator h).precompose filterQuery filterQuery_FP)
    (RationalParentChildCoordinates.parameter_ne_zero F)

end LeanCanny.Encoding.RationalParentChildEquationCount
