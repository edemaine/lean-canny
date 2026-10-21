/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRegularHomogenization
public import LeanCanny.ETR.TubeMacaulaySystem

/-! # Homogeneous Macaulay inputs for the regular critical system

The spatial block now contains the reciprocal as well as the original point.
All regular equations are homogenized to the proved common degree allowance;
one linear projection equation makes the system square. Parameters remain
coefficients. This is the regular source construction, not an eliminant proof.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRegularMacaulay
open LeanCanny.Encoding
open Geometry TubeEncoding TubeProjectionEncoding
open LeanCanny.Algebra
open scoped BigOperators

noncomputable def image (n : ℕ) : Option (Option (TubeProjectionEncoding.Variable n)) →
    MvPolynomial (Option (Option (Point n))) (TubeMacaulay.Coefficients n)
  | none => MvPolynomial.X none
  | some i => MvPolynomial.rename some (TubeMacaulay.image n i)

theorem image_homogeneous (n : ℕ) (i : Option (Option (TubeProjectionEncoding.Variable n))) :
    (image n i).IsHomogeneous (WeightedHomogenization.weights (TubeRegularHomogenization.pointWeight n) i) := by
  cases i with
  | none => exact MvPolynomial.isHomogeneous_X (R := TubeMacaulay.Coefficients n) none
  | some i =>
    change (MvPolynomial.rename some (TubeMacaulay.image n i)).IsHomogeneous (TubeRegularHomogenization.pointWeight n i)
    rw [TubeRegularHomogenization.pointWeight_eq]
    exact (TubeMacaulay.image_homogeneous n i).rename_isHomogeneous

noncomputable def spatial (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (j : TubeRegularSource.Index bits) : MvPolynomial (Option (Option (TubeSource.Coordinate bits)))
      (TubeMacaulay.Coefficients (CompactSource.term bits).arity) :=
  (TubeRegularHomogenization.polynomial bits s j).eval₂
    (MvPolynomial.C.comp (Int.castRingHom (TubeMacaulay.Coefficients (CompactSource.term bits).arity)))
    (image (CompactSource.term bits).arity)

theorem spatial_homogeneous (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) (j : TubeRegularSource.Index bits) :
    (spatial bits s j).IsHomogeneous (TubeIndexed.degreeBound bits) :=
  HomogeneousSubstitution.homogeneous_eval₂ _ _ _ (TubeRegularHomogenization.homogeneous bits s j) _ _ (image_homogeneous _)

theorem spatial_eval_chart {R : Type*} [CommRing R] (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (j : TubeRegularSource.Index bits) (φ : TubeMacaulay.Coefficients (CompactSource.term bits).arity →+* R)
    (z : Option (TubeSource.Coordinate bits) → R) :
    (spatial bits s j).eval₂ φ (fun i => i.elim 1 z) =
      (TubeRegularSource.polynomial bits s j).eval₂ (Int.castRingHom R)
        (fun i => i.elim (z none) (TubeMacaulay.values _ φ (fun k => z (some k)))) := by
  let e := MvPolynomial.eval₂Hom φ (fun i : Option (Option (TubeSource.Coordinate bits)) => i.elim 1 z)
  have hc : e.comp (MvPolynomial.C.comp (Int.castRingHom (TubeMacaulay.Coefficients (CompactSource.term bits).arity))) =
      Int.castRingHom R := by ext a; simp [e]
  have hx : (fun i => e (image (CompactSource.term bits).arity i)) =
      (fun i : TubeRegularHomogenization.Native bits => i.elim 1
        (fun k => k.elim (z none) (TubeMacaulay.values _ φ (fun j => z (some j))))) := by
    funext i
    rcases i with _ | (_ | ((i | i) | p)) <;> simp [e, image, TubeMacaulay.image, TubeMacaulay.values]
  change e ((TubeRegularHomogenization.polynomial bits s j).eval₂ _ _) = _
  rw [MvPolynomial.eval₂_comp_left, hc]
  change (TubeRegularHomogenization.polynomial bits s j).eval₂ (Int.castRingHom R)
    (fun i => e (image (CompactSource.term bits).arity i)) = _
  rw [hx, TubeRegularHomogenization.eval_chart]

def splitVariables (n : ℕ) : Option (Option (TubeProjectionEncoding.Variable n)) ≃
    Sum (Option (Option (Point n))) (Sum (Point n) TubePolynomial.Parameter) where
  toFun
    | none => .inl none
    | some none => .inl (some none)
    | some (some (.inl (.inl i))) => .inl (some (some i))
    | some (some (.inl (.inr i))) => .inr (.inl i)
    | some (some (.inr p)) => .inr (.inr p)
  invFun
    | .inl none => none
    | .inl (some none) => some none
    | .inl (some (some i)) => some (some (.inl (.inl i)))
    | .inr (.inl i) => some (some (.inl (.inr i)))
    | .inr (.inr p) => some (some (.inr p))
  left_inv := by rintro (_ | (_ | ((i | i) | p))) <;> rfl
  right_inv := by rintro ((_ | (_ | i)) | (i | p)) <;> rfl

theorem flatten_substitution (n : ℕ) (p : MvPolynomial (Option (Option (TubeProjectionEncoding.Variable n))) ℤ) :
    NestedPolynomial.flatten (p.eval₂ (MvPolynomial.C.comp (Int.castRingHom (TubeMacaulay.Coefficients n))) (image n)) =
      MvPolynomial.rename (splitVariables n) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂_C, RingHom.comp_apply, NestedPolynomial.flatten_C]
    simp
  | add p q hp hq => simp only [map_add, MvPolynomial.eval₂_add, hp, hq]
  | mul_X p i hp =>
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul, hp, map_mul, MvPolynomial.rename_X]
    congr 1
    rcases i with _ | (_ | ((i | i) | p)) <;> simp [image, TubeMacaulay.image, splitVariables]

theorem flatten_spatial (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) (j : TubeRegularSource.Index bits) :
    NestedPolynomial.flatten (spatial bits s j) = MvPolynomial.rename (splitVariables (CompactSource.term bits).arity)
      (TubeRegularHomogenization.polynomial bits s j) := flatten_substitution _ _

section System
variable {R : Type*} [CommRing R]

noncomputable def linearEquation (n : ℕ) (t : R) (ell : Option (Point n) → R) :
    MvPolynomial (Option (Option (Point n))) R :=
  MvPolynomial.C t * MvPolynomial.X none - ∑ i, MvPolynomial.C (ell i) * MvPolynomial.X (some i)

theorem linearEquation_homogeneous (n : ℕ) (t : R) (ell : Option (Point n) → R) :
    (linearEquation n t ell).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sub (MvPolynomial.isHomogeneous_C_mul_X _ _) _
  exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _)

theorem linearEquation_eval_chart (n : ℕ) (t : R) (ell z : Option (Point n) → R) :
    (linearEquation n t ell).eval₂ (RingHom.id R) (fun i => i.elim 1 z) = t - ∑ i, ell i * z i := by
  simp [linearEquation]

noncomputable def coordinateEquiv (n : ℕ) : Option (Option (Point n)) ≃ Fin (pointCount n + 1 + 1) :=
  (Equiv.optionCongr (TubeMacaulay.coordinateEquiv n)).trans (finSuccEquiv (pointCount n + 1)).symm

noncomputable def rowIndex (n : ℕ) (r : Fin (pointCount n + 1)) : Option (TubePolynomial.ProjectionIndex (Fin n)) :=
  match finSuccEquiv (pointCount n) r with
  | none => none
  | some k => some (TubeProjectionRow.decode n k.val)

noncomputable def rows (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (CompactSource.term bits).arity →+* R) (t : R)
    (ell : Option (TubeSource.Coordinate bits) → R) : Fin (pointCount (CompactSource.term bits).arity + 1 + 1) →
      MvPolynomial (Fin (pointCount (CompactSource.term bits).arity + 1 + 1)) R := fun r =>
  MvPolynomial.rename (coordinateEquiv (CompactSource.term bits).arity)
    (match finSuccEquiv (pointCount (CompactSource.term bits).arity + 1) r with
    | none => linearEquation _ t ell
    | some k => (spatial bits s (rowIndex (CompactSource.term bits).arity k)).map φ)

noncomputable def degrees (bits : List Bool) (r : Fin (pointCount (CompactSource.term bits).arity + 1 + 1)) : ℕ :=
  match finSuccEquiv (pointCount (CompactSource.term bits).arity + 1) r with
  | none => 1
  | some _ => TubeIndexed.degreeBound bits

theorem rows_homogeneous (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (CompactSource.term bits).arity →+* R) (t : R)
    (ell : Option (TubeSource.Coordinate bits) → R) (r : Fin (pointCount (CompactSource.term bits).arity + 1 + 1)) :
    (rows bits s φ t ell r).IsHomogeneous (degrees bits r) := by
  unfold rows degrees
  cases h : finSuccEquiv (pointCount (CompactSource.term bits).arity + 1) r with
  | none => exact (linearEquation_homogeneous _ t ell).rename_isHomogeneous
  | some k => exact ((spatial_homogeneous bits s _).map φ).rename_isHomogeneous

theorem rows_reciprocal (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (CompactSource.term bits).arity →+* R) (t : R)
    (ell : Option (TubeSource.Coordinate bits) → R) :
    rows bits s φ t ell (0 : Fin (pointCount (CompactSource.term bits).arity + 1)).succ =
      MvPolynomial.rename (coordinateEquiv (CompactSource.term bits).arity) ((spatial bits s none).map φ) := by
  simp only [rows, finSuccEquiv_succ, rowIndex, finSuccEquiv_zero]

theorem rows_original (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (CompactSource.term bits).arity →+* R) (t : R)
    (ell : Option (TubeSource.Coordinate bits) → R) (j : TubeSource.ProjectionIndex bits) :
    rows bits s φ t ell ((⟨TubeProjectionRow.code (CompactSource.term bits).arity j,
      TubeProjectionRow.code_lt _ j⟩ : Fin (pointCount (CompactSource.term bits).arity)).succ).succ =
      MvPolynomial.rename (coordinateEquiv (CompactSource.term bits).arity) ((spatial bits s (some j)).map φ) := by
  simp only [rows, finSuccEquiv_succ, rowIndex, TubeProjectionRow.decode_code]

end System

theorem det_zero_of_regular_point {K : Type*} [Field K] (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (CompactSource.term bits).arity →+* K) (t : K)
    (ell z : Option (TubeSource.Coordinate bits) → K) (W : ℕ)
    (hW : Macaulay.level (degrees bits) < 2 ^ W)
    (hp : ∀ j, (TubeRegularSource.polynomial bits s j).eval₂ (Int.castRingHom K)
      (fun i => i.elim (z none) (TubeMacaulay.values _ φ (fun k => z (some k)))) = 0)
    (ht : t = ∑ i, ell i * z i) :
    (Macaulay.matrix (rows bits s φ t ell) (degrees bits) W).det = 0 := by
  let x : Option (Option (TubeSource.Coordinate bits)) → K := fun i => i.elim 1 z
  let v : Fin (pointCount (CompactSource.term bits).arity + 1 + 1) → K :=
    fun i => x ((coordinateEquiv (CompactSource.term bits).arity).symm i)
  have hv : (fun i => v (coordinateEquiv (CompactSource.term bits).arity i)) = x := by
    funext i
    simp only [v, Equiv.symm_apply_apply]
  have hrows : ∀ r, MvPolynomial.eval v (rows bits s φ t ell r) = 0 := by
    intro r
    change (rows bits s φ t ell r).eval₂ (RingHom.id K) v = 0
    rw [rows, MvPolynomial.eval₂_rename]
    change (match finSuccEquiv (pointCount (CompactSource.term bits).arity + 1) r with
      | none => linearEquation _ t ell
      | some k => (spatial bits s (rowIndex (CompactSource.term bits).arity k)).map φ).eval₂
      (RingHom.id K) (fun i => v (coordinateEquiv (CompactSource.term bits).arity i)) = 0
    rw [hv]
    cases h : finSuccEquiv (pointCount (CompactSource.term bits).arity + 1) r with
    | none =>
      change (linearEquation _ t ell).eval₂ (RingHom.id K) (fun i => i.elim 1 z) = 0
      rw [linearEquation_eval_chart, ht, sub_self]
    | some k =>
      change ((spatial bits s (rowIndex (CompactSource.term bits).arity k)).map φ).eval₂
        (RingHom.id K) (fun i => i.elim 1 z) = 0
      rw [MvPolynomial.eval₂_map, RingHom.id_comp, spatial_eval_chart]
      exact hp _
  apply Macaulay.det_eq_zero_of_common_root _ _ W (rows_homogeneous bits s φ t ell) hW v hrows
  refine ⟨coordinateEquiv (CompactSource.term bits).arity none, ?_⟩
  simpa only [v, Equiv.symm_apply_apply, x, Option.elim_none] using (one_ne_zero : (1 : K) ≠ 0)

end LeanCanny.ETR.TubeRegularMacaulay
