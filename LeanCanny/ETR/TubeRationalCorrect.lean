/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRationalSubstitution
public import LeanCanny.Algebra.RationalSubstitutionSign

/-! # Native correctness of rational substitution into tube systems

The substituted family is exactly denominator clearing of the actual integer
tube or projection row in its finite layout. Its trailing coefficient gives
the original rational evaluation's sign for sufficiently small positive values
at which every coordinate denominator is nonzero.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRational
open LeanCanny.Encoding
open Geometry TubeEncoding TubeProjectionEncoding
open Algebra.RationalSubstitution

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubePolynomial.integerPolynomial
  TubePolynomial.integerProjection TubeProjection.decodedRow

noncomputable def nativeRow (source row : List Bool → List Bool) (c : List Bool) : TubeSource.ProjectionIndex (source c) :=
  TubeProjection.decodedRow (TubeIndexed.compiled source) row c

theorem tube_source_eq (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool) :
    Indexed.source ((family false source active row n d).arity c) ((family false source active row n d).terms c)
      ((family false source active row n d).coefficient c) ((family false source active row n d).exponent c) =
        MvPolynomial.rename (coordinateEquiv (TubeIndexed.arity (source c)))
          (TubeSource.integerPolynomial (source c) (activeSet (TubeIndexed.arity (source c)) (active c))) := by
  exact TubeIndexed.tube_source_eq (source c) _

theorem projection_source_eq (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool) :
    Indexed.source ((family true source active row n d).arity c) ((family true source active row n d).terms c)
      ((family true source active row n d).coefficient c) ((family true source active row n d).exponent c) =
        MvPolynomial.rename (variableEquiv (TubeIndexed.arity (source c)))
          (TubeSource.integerProjection (source c) (activeSet (TubeIndexed.arity (source c)) (active c))
            (nativeRow source row c)) := by
  exact TubeIndexed.projection_source_eq (source c) _ _

attribute [local irreducible] nativeRow

theorem tube_polynomial_eq (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool) :
    (family false source active row n d).polynomial c = clearedWith
      (fun _ => 2 ^ (TubeIndexed.blockWidth (source c) - 1))
      (MvPolynomial.rename (coordinateEquiv (TubeIndexed.arity (source c)))
        (TubeSource.integerPolynomial (source c) (activeSet (TubeIndexed.arity (source c)) (active c))))
      (fun i : Fin (TubeIndexed.tubeDimension (source c)) => n c i.val)
      (fun i : Fin (TubeIndexed.tubeDimension (source c)) => d c i.val) := by
  let F := family false source active row n d
  let H := 2 ^ (TubeIndexed.blockWidth (source c) - 1)
  have hw : F.width c = 2 * H := TubeIndexed.clearingWidth_eq (source c)
  change Indexed.cleared (F.arity c) (F.terms c) (F.width c) (F.coefficient c) (F.exponent c) (n c) (d c) = _
  rw [hw]
  exact (Indexed.cleared_eq_clearedWith_source (F.arity c) (F.terms c) H (F.coefficient c) (F.exponent c) (n c) (d c)).trans
    (congrArg (fun p : MvPolynomial (Fin (F.arity c)) ℤ => clearedWith (fun _ => H) p
      (fun i => n c i.val) (fun i => d c i.val)) (tube_source_eq source active row n d c))

theorem projection_polynomial_eq (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool) :
    (family true source active row n d).polynomial c = clearedWith
      (fun _ => 2 ^ (TubeIndexed.blockWidth (source c) - 1))
      (MvPolynomial.rename (variableEquiv (TubeIndexed.arity (source c)))
        (TubeSource.integerProjection (source c) (activeSet (TubeIndexed.arity (source c)) (active c))
          (nativeRow source row c)))
      (fun i : Fin (TubeIndexed.projectionDimension (source c)) => n c i.val)
      (fun i : Fin (TubeIndexed.projectionDimension (source c)) => d c i.val) := by
  let F := family true source active row n d
  let H := 2 ^ (TubeIndexed.blockWidth (source c) - 1)
  have hw : F.width c = 2 * H := TubeIndexed.clearingWidth_eq (source c)
  change Indexed.cleared (F.arity c) (F.terms c) (F.width c) (F.coefficient c) (F.exponent c) (n c) (d c) = _
  rw [hw]
  exact (Indexed.cleared_eq_clearedWith_source (F.arity c) (F.terms c) H (F.coefficient c) (F.exponent c) (n c) (d c)).trans
    (congrArg (fun p : MvPolynomial (Fin (F.arity c)) ℤ => clearedWith (fun _ => H) p
      (fun i => n c i.val) (fun i => d c i.val)) (projection_source_eq source active row n d c))

theorem tube_sign_substitution (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, 0 < x → x < δ →
      (∀ i, i < TubeIndexed.tubeDimension (source c) → (d c i).eval₂ (Int.castRingHom ℝ) x ≠ 0) →
      SignType.sign ((TubeSource.integerPolynomial (source c) (activeSet (TubeIndexed.arity (source c)) (active c))).eval₂
        (Int.castRingHom ℝ) (fun j => (n c (coordinateEquiv (TubeIndexed.arity (source c)) j).val).eval₂ (Int.castRingHom ℝ) x /
          (d c (coordinateEquiv (TubeIndexed.arity (source c)) j).val).eval₂ (Int.castRingHom ℝ) x)) =
        SignType.sign ((family false source active row n d).polynomial c).trailingCoeff := by
  let F := family false source active row n d
  obtain ⟨δ, hδ, hsign⟩ := IntegerBits.Family.sign_substitution F c
    (2 ^ (TubeIndexed.blockWidth (source c) - 1)) (TubeIndexed.clearingWidth_eq (source c))
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxd hden
  let v : Fin (F.arity c) → ℝ := fun i => (n c i.val).eval₂ (Int.castRingHom ℝ) x / (d c i.val).eval₂ (Int.castRingHom ℝ) x
  have he := congrArg (fun p : MvPolynomial (Fin (F.arity c)) ℤ => p.eval₂ (Int.castRingHom ℝ) v)
    (tube_source_eq source active row n d c)
  have hr := MvPolynomial.eval₂_rename (Int.castRingHom ℝ) (coordinateEquiv (TubeIndexed.arity (source c))) v
    (TubeSource.integerPolynomial (source c) (activeSet (TubeIndexed.arity (source c)) (active c)))
  exact (congrArg SignType.sign (he.trans hr)).symm.trans (hsign x hx hxd hden)

theorem projection_sign_substitution (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (c : List Bool) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, 0 < x → x < δ →
      (∀ i, i < TubeIndexed.projectionDimension (source c) → (d c i).eval₂ (Int.castRingHom ℝ) x ≠ 0) →
      SignType.sign ((TubeSource.integerProjection (source c) (activeSet (TubeIndexed.arity (source c)) (active c))
        (nativeRow source row c)).eval₂
          (Int.castRingHom ℝ) (fun j => (n c (variableEquiv (TubeIndexed.arity (source c)) j).val).eval₂ (Int.castRingHom ℝ) x /
            (d c (variableEquiv (TubeIndexed.arity (source c)) j).val).eval₂ (Int.castRingHom ℝ) x)) =
        SignType.sign ((family true source active row n d).polynomial c).trailingCoeff := by
  let F := family true source active row n d
  obtain ⟨δ, hδ, hsign⟩ := IntegerBits.Family.sign_substitution F c
    (2 ^ (TubeIndexed.blockWidth (source c) - 1)) (TubeIndexed.clearingWidth_eq (source c))
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxd hden
  let v : Fin (F.arity c) → ℝ := fun i => (n c i.val).eval₂ (Int.castRingHom ℝ) x / (d c i.val).eval₂ (Int.castRingHom ℝ) x
  have he := congrArg (fun p : MvPolynomial (Fin (F.arity c)) ℤ => p.eval₂ (Int.castRingHom ℝ) v)
    (projection_source_eq source active row n d c)
  have hr := MvPolynomial.eval₂_rename (Int.castRingHom ℝ) (variableEquiv (TubeIndexed.arity (source c))) v
    (TubeSource.integerProjection (source c) (activeSet (TubeIndexed.arity (source c)) (active c))
      (nativeRow source row c))
  exact (congrArg SignType.sign (he.trans hr)).symm.trans (hsign x hx hxd hden)

end LeanCanny.ETR.TubeRational
