/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeHomogenization
public import LeanCanny.Algebra.HomogeneousSubstitution
public import LeanCanny.Algebra.MacaulayRoots

/-! # Homogeneous tube projection rows over a parameter coefficient ring

Direction and perturbation variables become coefficient variables. Flattening
recovers the partially homogenized integer rows by an explicit variable
bijection. Adding one homogeneous linear projection equation gives a square
system for the Macaulay construction. The reciprocal regularity equation and
the eliminant identification remain separate obligations.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeMacaulay

open LeanCanny.Encoding
open Geometry TubeEncoding TubeProjectionEncoding
open LeanCanny.Algebra
open scoped BigOperators

abbrev Coefficients (n : ℕ) := MvPolynomial (Sum (Point n) TubePolynomial.Parameter) ℤ

noncomputable def image (n : ℕ) : Option (Variable n) → MvPolynomial (Option (Point n)) (Coefficients n)
  | none => MvPolynomial.X none
  | some (.inl (.inl i)) => MvPolynomial.X (some i)
  | some (.inl (.inr i)) => MvPolynomial.C (MvPolynomial.X (.inl i))
  | some (.inr p) => MvPolynomial.C (MvPolynomial.X (.inr p))

theorem image_homogeneous (n : ℕ) (i : Option (Variable n)) :
    (image n i).IsHomogeneous (WeightedHomogenization.weights (TubeHomogenization.pointWeight n) i) := by
  rcases i with _ | ((i | i) | p)
  · change (MvPolynomial.X (none : Option (Point n)) : MvPolynomial _ (Coefficients n)).IsHomogeneous 1
    exact MvPolynomial.isHomogeneous_X (R := Coefficients n) none
  · simpa only [WeightedHomogenization.weights, TubeHomogenization.weight_point, image] using
      (MvPolynomial.isHomogeneous_X (R := Coefficients n) (some i))
  · simpa only [WeightedHomogenization.weights, TubeHomogenization.weight_direction, image] using
      (MvPolynomial.isHomogeneous_C (σ := Option (Point n)) (MvPolynomial.X (.inl i) : Coefficients n))
  · simpa only [WeightedHomogenization.weights, TubeHomogenization.weight_parameter, image] using
      (MvPolynomial.isHomogeneous_C (σ := Option (Point n)) (MvPolynomial.X (.inr p) : Coefficients n))

noncomputable def spatial (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (j : TubeSource.ProjectionIndex bits) :
    MvPolynomial (Option (TubeSource.Coordinate bits)) (Coefficients (CompactSource.term bits).arity) :=
  (TubeHomogenization.polynomial bits s j).eval₂
    (MvPolynomial.C.comp (Int.castRingHom (Coefficients (CompactSource.term bits).arity)))
    (image (CompactSource.term bits).arity)

theorem spatial_homogeneous (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (j : TubeSource.ProjectionIndex bits) : (spatial bits s j).IsHomogeneous (TubeIndexed.degreeBound bits) :=
  HomogeneousSubstitution.homogeneous_eval₂ _ _ _ (TubeHomogenization.homogeneous bits s j) _ _ (image_homogeneous _)

def splitVariables (n : ℕ) : Option (Variable n) ≃ Sum (Option (Point n)) (Sum (Point n) TubePolynomial.Parameter) where
  toFun
    | none => .inl none
    | some (.inl (.inl i)) => .inl (some i)
    | some (.inl (.inr i)) => .inr (.inl i)
    | some (.inr p) => .inr (.inr p)
  invFun
    | .inl none => none
    | .inl (some i) => some (.inl (.inl i))
    | .inr (.inl i) => some (.inl (.inr i))
    | .inr (.inr p) => some (.inr p)
  left_inv := by rintro (_ | ((i | i) | p)) <;> rfl
  right_inv := by rintro ((_ | i) | (i | p)) <;> rfl

theorem flatten_substitution (n : ℕ) (p : MvPolynomial (Option (Variable n)) ℤ) :
    NestedPolynomial.flatten (p.eval₂ (MvPolynomial.C.comp (Int.castRingHom (Coefficients n))) (image n)) =
      MvPolynomial.rename (splitVariables n) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂_C, RingHom.comp_apply, NestedPolynomial.flatten_C]
    simp
  | add p q hp hq => simp only [map_add, MvPolynomial.eval₂_add, hp, hq]
  | mul_X p i hp =>
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul, hp, map_mul, MvPolynomial.rename_X]
    congr 1
    rcases i with _ | ((i | i) | p) <;> simp [image, splitVariables]

theorem flatten_spatial (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (j : TubeSource.ProjectionIndex bits) : NestedPolynomial.flatten (spatial bits s j) =
      MvPolynomial.rename (splitVariables (CompactSource.term bits).arity) (TubeHomogenization.polynomial bits s j) :=
  flatten_substitution _ _

noncomputable def values {R : Type*} [CommRing R] (n : ℕ) (φ : Coefficients n →+* R) (x : Point n → R) : Variable n → R :=
  Sum.elim (Sum.elim x (fun i => φ (MvPolynomial.X (.inl i)))) (fun p => φ (MvPolynomial.X (.inr p)))

theorem spatial_eval_chart {R : Type*} [CommRing R] (bits : List Bool)
    (s : Finset (PerturbedSource.Index bits)) (j : TubeSource.ProjectionIndex bits)
    (φ : Coefficients (CompactSource.term bits).arity →+* R) (x : TubeSource.Coordinate bits → R) :
    (spatial bits s j).eval₂ φ (fun i => i.elim 1 x) =
      (TubeSource.integerProjection bits s j).eval₂ (Int.castRingHom R) (values _ φ x) := by
  let e := MvPolynomial.eval₂Hom φ (fun i : Option (TubeSource.Coordinate bits) => i.elim 1 x)
  have hc : e.comp (MvPolynomial.C.comp (Int.castRingHom (Coefficients (CompactSource.term bits).arity))) =
      Int.castRingHom R := by ext a; simp [e]
  have hx : (fun i => e (image (CompactSource.term bits).arity i)) =
      (fun i : TubeHomogenization.Native bits => i.elim 1 (values _ φ x)) := by
    funext i
    rcases i with _ | ((i | i) | p) <;> simp [e, image, values]
  change e ((TubeHomogenization.polynomial bits s j).eval₂ _ _) = _
  rw [MvPolynomial.eval₂_comp_left, hc]
  change (TubeHomogenization.polynomial bits s j).eval₂ (Int.castRingHom R)
    (fun i => e (image (CompactSource.term bits).arity i)) = _
  rw [hx, TubeHomogenization.eval_chart]

section System
variable {R : Type*} [CommRing R]

noncomputable def linearEquation (n : ℕ) (t : R) (ell : Point n → R) : MvPolynomial (Option (Point n)) R :=
  MvPolynomial.C t * MvPolynomial.X none - ∑ i, MvPolynomial.C (ell i) * MvPolynomial.X (some i)

theorem linearEquation_homogeneous (n : ℕ) (t : R) (ell : Point n → R) :
    (linearEquation n t ell).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sub (MvPolynomial.isHomogeneous_C_mul_X _ _) _
  exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _)

theorem linearEquation_eval_chart (n : ℕ) (t : R) (ell x : Point n → R) :
    (linearEquation n t ell).eval₂ (RingHom.id R) (fun i => i.elim 1 x) = t - ∑ i, ell i * x i := by
  simp [linearEquation]

noncomputable def coordinateEquiv (n : ℕ) : Option (Point n) ≃ Fin (pointCount n + 1) :=
  (Equiv.optionCongr (pointEquiv n)).trans (finSuccEquiv (pointCount n)).symm

noncomputable def rows (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : Coefficients (CompactSource.term bits).arity →+* R) (t : R)
    (ell : Point (CompactSource.term bits).arity → R) :
    Fin (pointCount (CompactSource.term bits).arity + 1) →
      MvPolynomial (Fin (pointCount (CompactSource.term bits).arity + 1)) R := fun r =>
  MvPolynomial.rename (coordinateEquiv (CompactSource.term bits).arity)
    (match finSuccEquiv (pointCount (CompactSource.term bits).arity) r with
    | none => linearEquation _ t ell
    | some k => (spatial bits s (TubeProjectionRow.decode (CompactSource.term bits).arity k.val)).map φ)

noncomputable def degrees (bits : List Bool) (r : Fin (pointCount (CompactSource.term bits).arity + 1)) : ℕ :=
  match finSuccEquiv (pointCount (CompactSource.term bits).arity) r with
  | none => 1
  | some _ => TubeIndexed.degreeBound bits

theorem rows_homogeneous (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : Coefficients (CompactSource.term bits).arity →+* R) (t : R)
    (ell : Point (CompactSource.term bits).arity → R) (r : Fin (pointCount (CompactSource.term bits).arity + 1)) :
    (rows bits s φ t ell r).IsHomogeneous (degrees bits r) := by
  unfold rows degrees
  cases h : finSuccEquiv (pointCount (CompactSource.term bits).arity) r with
  | none => exact (linearEquation_homogeneous _ t ell).rename_isHomogeneous
  | some k => exact ((spatial_homogeneous bits s _).map φ).rename_isHomogeneous

theorem rows_code (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : Coefficients (CompactSource.term bits).arity →+* R) (t : R)
    (ell : Point (CompactSource.term bits).arity → R) (j : TubeSource.ProjectionIndex bits) :
    rows bits s φ t ell (⟨TubeProjectionRow.code (CompactSource.term bits).arity j,
      TubeProjectionRow.code_lt _ j⟩ : Fin (pointCount (CompactSource.term bits).arity)).succ =
      MvPolynomial.rename (coordinateEquiv (CompactSource.term bits).arity) ((spatial bits s j).map φ) := by
  simp only [rows, finSuccEquiv_succ, TubeProjectionRow.decode_code]

end System

theorem det_zero_of_projection_point {K : Type*} [Field K] (bits : List Bool)
    (s : Finset (PerturbedSource.Index bits))
    (φ : Coefficients (CompactSource.term bits).arity →+* K) (t : K)
    (ell x : TubeSource.Coordinate bits → K) (W : ℕ)
    (hW : Macaulay.level (degrees bits) < 2 ^ W)
    (hp : ∀ j, (TubeSource.integerProjection bits s j).eval₂ (Int.castRingHom K) (values _ φ x) = 0)
    (ht : t = ∑ i, ell i * x i) :
    (Macaulay.matrix (rows bits s φ t ell) (degrees bits) W).det = 0 := by
  let z : Option (TubeSource.Coordinate bits) → K := fun i => i.elim 1 x
  let v : Fin (pointCount (CompactSource.term bits).arity + 1) → K :=
    fun i => z ((coordinateEquiv (CompactSource.term bits).arity).symm i)
  have hv : (fun i => v (coordinateEquiv (CompactSource.term bits).arity i)) = z := by
    funext i
    simp only [v, Equiv.symm_apply_apply]
  have hrows : ∀ r, MvPolynomial.eval v (rows bits s φ t ell r) = 0 := by
    intro r
    change (rows bits s φ t ell r).eval₂ (RingHom.id K) v = 0
    rw [rows, MvPolynomial.eval₂_rename]
    change (match finSuccEquiv (pointCount (CompactSource.term bits).arity) r with
      | none => linearEquation _ t ell
      | some k => (spatial bits s (TubeProjectionRow.decode (CompactSource.term bits).arity k.val)).map φ).eval₂
      (RingHom.id K) (fun i => v (coordinateEquiv (CompactSource.term bits).arity i)) = 0
    rw [hv]
    cases h : finSuccEquiv (pointCount (CompactSource.term bits).arity) r with
    | none =>
      change (linearEquation _ t ell).eval₂ (RingHom.id K) (fun i => i.elim 1 x) = 0
      rw [linearEquation_eval_chart, ht, sub_self]
    | some k =>
      change ((spatial bits s (TubeProjectionRow.decode (CompactSource.term bits).arity k.val)).map φ).eval₂
        (RingHom.id K) (fun i => i.elim 1 x) = 0
      rw [MvPolynomial.eval₂_map, RingHom.id_comp, spatial_eval_chart]
      exact hp _
  apply Macaulay.det_eq_zero_of_common_root _ _ W (rows_homogeneous bits s φ t ell) hW v hrows
  refine ⟨coordinateEquiv (CompactSource.term bits).arity none, ?_⟩
  simpa only [v, Equiv.symm_apply_apply, z, Option.elim_none] using (one_ne_zero : (1 : K) ≠ 0)

end LeanCanny.ETR.TubeMacaulay
