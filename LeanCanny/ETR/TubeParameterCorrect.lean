/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeParameterSubstitution
public import LeanCanny.Algebra.RationalSubstitutionSign

/-! # Native correctness of regular-system parameter specialization

The streamed source is exactly the selected spatial coefficient polynomial.
Clearing parameter denominators therefore computes that coefficient after
rational substitution, up to the stated common positive even-power scale.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeParameter
open LeanCanny.Encoding LeanCanny.Algebra
open Algebra.RationalSubstitution
open scoped Classical BigOperators

attribute [local irreducible] RationalSubstitutionBits.compiledTerm nativePolynomial spatialPolynomial flatPolynomial

noncomputable def spatialExponent (source : List Bool → List Bool) (c : List Bool) : Spatial (source (pairFst c)) →₀ ℕ :=
  FixedWidthPolynomial.nativeExponent (spatialEquiv (source (pairFst c))) (TubeIndexed.blockWidth (source (pairFst c)))
    (Nat.fromBitsLE (pairSnd c))

theorem coefficient_formula (source active row : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    coefficient source active row c r =
      if PartialCoefficient.leftExponent (FixedWidthPolynomial.nativeExponent (fullEquiv (source (pairFst c)))
        (TubeIndexed.blockWidth (source (pairFst c))) r) = spatialExponent source c
      then (flatPolynomial source active row (pairFst c)).coeff
        (FixedWidthPolynomial.nativeExponent (fullEquiv (source (pairFst c))) (TubeIndexed.blockWidth (source (pairFst c))) r)
      else 0 := by
  have h := PartialCoefficientBits.matches_context (spatialSize source) (blockWidth source) c
    (fullEquiv (source (pairFst c))) (spatialEquiv (source (pairFst c))) (full_left (source (pairFst c))) r
  change PartialCoefficientBits.Matches (spatialSize source) (blockWidth source) (pair c (BinaryNatCode.encode r)) ↔
    PartialCoefficient.leftExponent (FixedWidthPolynomial.nativeExponent (fullEquiv (source (pairFst c)))
      (TubeIndexed.blockWidth (source (pairFst c))) r) = spatialExponent source c at h
  unfold coefficient
  by_cases hm : PartialCoefficientBits.Matches (spatialSize source) (blockWidth source) (pair c (BinaryNatCode.encode r))
  · rw [ite_eq_left hm, ite_eq_left (h.mp hm)]
    exact (flat_coefficient source active row (pairFst c) r).symm
  · rw [ite_eq_right hm, ite_eq_right (fun he => hm (h.mpr he))]

theorem source_eq (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool) :
    Indexed.source ((family source active row n d).arity c) ((family source active row n d).terms c)
      ((family source active row n d).coefficient c) ((family source active row n d).exponent c) =
      MvPolynomial.rename (parameterEquiv (source (pairFst c)))
        ((spatialPolynomial source active row (pairFst c)).coeff (spatialExponent source c)) := by
  simp only [family, indexedSource, IntegerBits.IndexedSource.withCoordinates, IntegerBits.IndexedSource.projected, Function.comp_apply]
  have hc := funext (coefficient_formula source active row c)
  rw [hc]
  have h := PartialCoefficient.slice_source_eq _ _ _ _ (fullEquiv (source (pairFst c)))
    (spatialEquiv (source (pairFst c))) (parameterEquiv (source (pairFst c))) (full_right (source (pairFst c)))
    _ (flat_support_fits source active row (pairFst c)) (Nat.fromBitsLE (pairSnd c))
  unfold flatPolynomial at h ⊢
  have hs := h.trans (congrArg (MvPolynomial.rename (parameterEquiv (source (pairFst c))))
    (PartialCoefficient.slice_flatten (spatialPolynomial source active row (pairFst c)) (spatialExponent source c)))
  refine Eq.trans ?_ hs
  apply congrArg (fun a : ℕ → ℤ => Indexed.source (parameterCount (source (pairFst c)))
    (FixedWidthPolynomial.count (nativeCount (source (pairFst c))) (TubeIndexed.blockWidth (source (pairFst c)))) a
    (fun r i => FixedWidthPolynomial.entry (TubeIndexed.blockWidth (source (pairFst c))) r (spatialCount (source (pairFst c)) + i)))
  funext r
  dsimp only [spatialExponent]
  split_ifs with hp
  · exact ite_eq_left hp
  · exact ite_eq_right hp

theorem polynomial_eq (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool) :
    (family source active row n d).polynomial c = clearedWith
      (fun _ => 2 ^ (TubeIndexed.blockWidth (source (pairFst c)) - 1))
      (MvPolynomial.rename (parameterEquiv (source (pairFst c)))
        ((spatialPolynomial source active row (pairFst c)).coeff (spatialExponent source c)))
      (fun i : Fin (parameterCount (source (pairFst c))) => n c i.val)
      (fun i : Fin (parameterCount (source (pairFst c))) => d c i.val) := by
  let F := family source active row n d
  let H := 2 ^ (TubeIndexed.blockWidth (source (pairFst c)) - 1)
  have hw : F.width c = 2 * H := TubeIndexed.clearingWidth_eq (source (pairFst c))
  change Indexed.cleared (F.arity c) (F.terms c) (F.width c) (F.coefficient c) (F.exponent c) (n c) (d c) = _
  rw [hw]
  exact (Indexed.cleared_eq_clearedWith_source (F.arity c) (F.terms c) H (F.coefficient c) (F.exponent c) (n c) (d c)).trans
    (congrArg (fun p : MvPolynomial (Fin (F.arity c)) ℤ => clearedWith (fun _ => H) p
      (fun i => n c i.val) (fun i => d c i.val)) (source_eq source active row n d c))


theorem eval_coefficient {K : Type*} [Field K] (φ : ℤ →+* K) (x : K)
    (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool)
    (hd : ∀ i, i < parameterCount (source (pairFst c)) → (d c i).eval₂ φ x ≠ 0) :
    ((family source active row n d).polynomial c).eval₂ φ x =
      (∏ i ∈ Finset.range (parameterCount (source (pairFst c))),
        (d c i).eval₂ φ x ^ (2 ^ TubeIndexed.blockWidth (source (pairFst c)))) *
      ((spatialPolynomial source active row (pairFst c)).map
        (MvPolynomial.eval₂Hom φ (fun i => (n c (parameterEquiv (source (pairFst c)) i).val).eval₂ φ x /
          (d c (parameterEquiv (source (pairFst c)) i).val).eval₂ φ x))).coeff (spatialExponent source c) := by
  let F := family source active row n d
  have h := Indexed.eval₂_cleared φ x (F.arity c) (F.terms c) (F.width c) (F.coefficient c) (F.exponent c)
    (n c) (d c) (F.exponent_le c) hd
  change (Indexed.cleared (F.arity c) (F.terms c) (F.width c) (F.coefficient c) (F.exponent c) (n c) (d c)).eval₂ φ x = _
  rw [h]
  congr 1
  rw [source_eq, MvPolynomial.coeff_map]
  exact MvPolynomial.eval₂_rename φ (parameterEquiv (source (pairFst c))) _ _


theorem sign_substitution (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, 0 < x → x < δ →
      (∀ i, i < parameterCount (source (pairFst c)) → (d c i).eval₂ (Int.castRingHom ℝ) x ≠ 0) →
      SignType.sign (((spatialPolynomial source active row (pairFst c)).map
        (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (fun i =>
          (n c (parameterEquiv (source (pairFst c)) i).val).eval₂ (Int.castRingHom ℝ) x /
          (d c (parameterEquiv (source (pairFst c)) i).val).eval₂ (Int.castRingHom ℝ) x))).coeff (spatialExponent source c)) =
        SignType.sign ((family source active row n d).polynomial c).trailingCoeff := by
  let F := family source active row n d
  obtain ⟨δ, hδ, hsign⟩ := IntegerBits.Family.sign_substitution F c
    (2 ^ (TubeIndexed.blockWidth (source (pairFst c)) - 1)) (TubeIndexed.clearingWidth_eq (source (pairFst c)))
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxd hden
  have he : (Indexed.source (F.arity c) (F.terms c) (F.coefficient c) (F.exponent c)).eval₂ (Int.castRingHom ℝ)
      (fun i => (n c i.val).eval₂ (Int.castRingHom ℝ) x / (d c i.val).eval₂ (Int.castRingHom ℝ) x) =
      ((spatialPolynomial source active row (pairFst c)).map
        (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (fun i =>
          (n c (parameterEquiv (source (pairFst c)) i).val).eval₂ (Int.castRingHom ℝ) x /
          (d c (parameterEquiv (source (pairFst c)) i).val).eval₂ (Int.castRingHom ℝ) x))).coeff (spatialExponent source c) := by
    rw [source_eq, MvPolynomial.coeff_map]
    exact MvPolynomial.eval₂_rename (Int.castRingHom ℝ) (parameterEquiv (source (pairFst c))) _ _
  exact (congrArg SignType.sign he).symm.trans (hsign x hx hxd hden)

end LeanCanny.ETR.TubeParameter
