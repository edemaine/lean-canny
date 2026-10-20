/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.TranscendentalDerivation

/-! # Coordinate derivations for algebraically independent families

Extend an independent family to a transcendence basis. Its coordinate
derivations extend to the field, taking the selected generator to one and
all other original generators to zero.
-/

@[expose] public section

namespace LeanCanny.Algebra.CoordinateDerivation
open MvPolynomial
open scoped IntermediateField.algebraAdjoinAdjoin

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [DecidableEq ι] {v : ι → L}

theorem onAdjoin_apply (hv : AlgebraicIndependent K v) (j i : ι) :
    TranscendentalDerivation.onAdjoin hv j (hv.aevalEquiv (X i)) = if i = j then 1 else 0 := by
  classical
  change MvPolynomial.aeval v (pderiv j (hv.repr (hv.aevalEquiv (X i)))) = _
  simp [AlgebraicIndependent.repr, pderiv_X, Pi.single_apply]

theorem exists_of_basis [CharZero K] (hv : IsTranscendenceBasis K v) (j : ι) :
    ∃ δ : Derivation K L L, ∀ i, δ (v i) = if i = j then 1 else 0 := by
  classical
  let A := Algebra.adjoin K (Set.range v)
  let B := IntermediateField.adjoin K (Set.range v)
  let : CharZero B := charZero_of_injective_algebraMap (algebraMap K B).injective
  let : Algebra.IsAlgebraic B L := hv.isAlgebraic_field
  let : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  let : Algebra.FormallyEtale B L := Algebra.FormallyEtale.of_isSeparable B L
  let : Algebra.FormallyEtale A L := Algebra.FormallyEtale.comp A B L
  refine ⟨EtaleDerivation.extend (TranscendentalDerivation.onAdjoin hv.1 j), ?_⟩
  intro i
  have h := EtaleDerivation.extend_algebraMap (TranscendentalDerivation.onAdjoin hv.1 j) (hv.1.aevalEquiv (X i))
  simpa only [AlgebraicIndependent.algebraMap_aevalEquiv, MvPolynomial.aeval_X, onAdjoin_apply] using h

theorem exists_of_independent [CharZero K] (hv : AlgebraicIndependent K v) (j : ι) :
    ∃ δ : Derivation K L L, ∀ i, δ (v i) = if i = j then 1 else 0 := by
  classical
  have hi : AlgebraicIndepOn K id (Set.range v) := hv.to_subtype_range
  obtain ⟨s, hs, hb⟩ := exists_isTranscendenceBasis_superset hi
  let j' : s := ⟨v j, hs (Set.mem_range_self j)⟩
  obtain ⟨δ, hδ⟩ := exists_of_basis hb j'
  refine ⟨δ, ?_⟩
  intro i
  have heq : (⟨v i, hs (Set.mem_range_self i)⟩ : s) = j' ↔ i = j := by
    simp only [j', Subtype.mk.injEq, hv.injective.eq_iff]
  simpa only [heq] using hδ ⟨v i, hs (Set.mem_range_self i)⟩

end LeanCanny.Algebra.CoordinateDerivation
