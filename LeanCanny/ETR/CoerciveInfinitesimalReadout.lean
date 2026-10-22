/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveInfinitesimalSemantics
public import LeanCanny.Computation.PSPACEBoolean
public import LeanCanny.ETR.PSPACEClosure

/-! # Composing the concrete coercive coefficient readers with native PSPACE

The two readers must compute the actual prepared parameter and cleared query
coefficients, with native space certificates. This interface isolates that
remaining construction; it does not assert that the readers already exist.
-/

@[expose] public section
namespace LeanCanny.ETR.CoerciveInfinitesimalFamily
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open CoerciveSymbolicSampling
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det Macaulay.fullMatrix

structure Readers where
  root : DyadicPolynomialBits.Access rootFamily
  coefficient : List Bool → List Bool
  coefficient_eq : ∀ c i j k m, 0 < m → coefficient
    (pair (pair c (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode j) (BinaryNatCode.encode k))))
      (BinaryNatCode.encode (m - 1))) =
      DyadicBits.integerResidue (((clearedQuery c (queryIndex c i)).coeff j).coeff k) m
  root_space : SpaceFunction root.coefficient
  coefficient_space : SpaceFunction coefficient

noncomputable def Readers.access (R : Readers) (left right : Bool) :
    DyadicSignPatternBits.Access (signFamily left right) where
  root := R.root
  coefficient := R.coefficient
  coefficient_eq := R.coefficient_eq
  pattern := patternReader left right
  pattern_eq c i := by
    simp only [patternReader, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl

theorem Readers.pattern_language_mem_PSPACE (R : Readers) (left right : Bool) :
    InfinitesimalRootBits.eventualRealizableLanguage (signFamily left right) ∈ PSPACE :=
  InfinitesimalRootBits.eventualRealizableLanguage_mem_PSPACE (R.access left right) (controls left right)
    (patternReader_mem_FP left right) R.root_space R.coefficient_space root_ne_zero

/-- All semantic reductions and final native PSPACE decisions are discharged.
The hypotheses are exactly the actual two coefficient programs and their
correctness and native space proofs. -/
theorem etr_mem_PSPACE_of_readers (R : Readers) : ETR.language ∈ PSPACE := by
  let L (left right : Bool) := InfinitesimalRootBits.eventualRealizableLanguage (signFamily left right)
  have h (left right : Bool) : L left right ∈ PSPACE := R.pattern_language_mem_PSPACE left right
  have he : ETR.language = (L false false ∪ L false true) ∪ (L true false ∪ L true true) := by
    ext bits
    rw [correct_patterns]
    constructor
    · rintro ⟨left, right, hm⟩
      cases left <;> cases right
      · exact Or.inl (Or.inl hm)
      · exact Or.inl (Or.inr hm)
      · exact Or.inr (Or.inl hm)
      · exact Or.inr (Or.inr hm)
    · rintro ((hm | hm) | (hm | hm))
      · exact ⟨false, false, hm⟩
      · exact ⟨false, true, hm⟩
      · exact ⟨true, false, hm⟩
      · exact ⟨true, true, hm⟩
  rw [he]
  exact mem_PSPACE_union (mem_PSPACE_union (h false false) (h false true))
    (mem_PSPACE_union (h true false) (h true true))

theorem existsReal_subset_PSPACE_of_readers (R : Readers) : ExistsReal ⊆ PSPACE :=
  existsReal_subset_PSPACE_of_etr (etr_mem_PSPACE_of_readers R)

end LeanCanny.ETR.CoerciveInfinitesimalFamily
