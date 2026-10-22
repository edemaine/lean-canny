/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeZeroQuery
public import LeanCanny.Geometry.TubeCoefficientFormula
public import LeanCanny.Algebra.EmbeddedMonomialCoefficient

/-! # Exponent patterns for the dense tube terms

Point exponents give the source query. Other coordinates must be zero, except
for the single shift coordinate in a cross term. The native monomial pattern
is equivalent to a bounded test in the explicit coordinate encoding.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDense
open LeanCanny.Encoding
open Geometry TubeEncoding
open Algebra.RationalSubstitution.Indexed

noncomputable def shiftVector (n : ℕ) : Option Bool → Coordinate n →₀ ℕ
  | none => 0
  | some b => Finsupp.single (.inl (.inr (.inl b))) 1

def expected (n : ℕ) : Option Bool → ℕ → ℕ
  | none, _ => 0
  | some b, i => if i = n + (if b then 1 else 0) then 1 else 0

theorem shiftVector_point (n : ℕ) (s : Option Bool) (i : Fin n) :
    shiftVector n s (TubePolynomial.spatialEmbedding i) = 0 := by
  cases s <;> simp [shiftVector, TubePolynomial.spatialEmbedding]

theorem shiftVector_apply (n : ℕ) (s : Option Bool) (j : Coordinate n) :
    shiftVector n s j = expected n s (coordinateEquiv n j).val := by
  cases s with
  | none => rfl
  | some b =>
    have hb : (coordinateEquiv n (.inl (.inr (.inl b)))).val = n + (if b then 1 else 0) := by
      cases b <;> simp
    have he : (coordinateEquiv n j).val = n + (if b then 1 else 0) ↔ j = .inl (.inr (.inl b)) := by
      constructor
      · intro h
        apply (coordinateEquiv n).injective
        apply Fin.ext
        exact h.trans hb.symm
      · intro h
        rw [h]
        exact hb
    simp only [shiftVector, expected, Finsupp.single_apply, he, eq_comm]

theorem spatial_range_iff (n : ℕ) (j : Coordinate n) :
    j ∈ Set.range (TubePolynomial.spatialEmbedding (ι := Fin n)) ↔ (coordinateEquiv n j).val < n := by
  rcases j with (i | q) | p
  · constructor
    · intro _
      exact i.isLt
    · intro _
      exact ⟨i, rfl⟩
  · constructor
    · rintro ⟨i, h⟩
      cases h
    · intro h
      rw [index_shift] at h
      omega
  · constructor
    · rintro ⟨i, h⟩
      cases h
    · intro h
      change n + constraintCount n + (parameterEquiv p).val < n at h
      omega

def Pattern (n W : List Bool → ℕ) (target : List Bool → List Bool) (s : Option Bool) (c : List Bool) : Prop :=
  ∀ i < dimension (n c), n c ≤ i → FixedWidthQuery.coordinate W target c i = expected (n c) s i

theorem pattern_iff (n W : List Bool → ℕ) (target : List Bool → List Bool) (s : Option Bool) (c : List Bool) :
    ((TubeZeroQuery.exponent n W target c).comapDomain TubePolynomial.spatialEmbedding
      TubePolynomial.spatialEmbedding_injective.injOn).mapDomain TubePolynomial.spatialEmbedding + shiftVector (n c) s =
        TubeZeroQuery.exponent n W target c ↔ Pattern n W target s c := by
  rw [Algebra.EmbeddedCoefficient.embedding_pattern_iff _ TubePolynomial.spatialEmbedding_injective _ _ (shiftVector_point (n c) s)]
  constructor
  · intro h i hi hn
    let j := (coordinateEquiv (n c)).symm ⟨i, hi⟩
    have hj : j ∉ Set.range TubePolynomial.spatialEmbedding := by
      rw [spatial_range_iff]
      simp only [j, Equiv.apply_symm_apply]
      omega
    have he := h j hj
    simpa only [TubeZeroQuery.exponent, Finsupp.coe_equivFunOnFinite_symm, shiftVector_apply, j, Equiv.apply_symm_apply] using he
  · intro h j hj
    have hn : n c ≤ (coordinateEquiv (n c) j).val := by
      rw [spatial_range_iff] at hj
      omega
    simpa only [TubeZeroQuery.exponent, Finsupp.coe_equivFunOnFinite_symm, shiftVector_apply] using
      h (coordinateEquiv (n c) j).val (coordinateEquiv (n c) j).isLt hn

theorem point_exponent (n W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) :
    (TubeZeroQuery.exponent n W target c).comapDomain TubePolynomial.spatialEmbedding
      TubePolynomial.spatialEmbedding_injective.injOn = exponentVector (n c) (FixedWidthQuery.entry n W target c) := by
  ext i
  simp only [Finsupp.comapDomain_apply, TubeZeroQuery.exponent, Finsupp.coe_equivFunOnFinite_symm,
    TubePolynomial.spatialEmbedding, index_point, exponentVector, FixedWidthQuery.entry, i.isLt, ite_true]

end LeanCanny.ETR.TubeDense
