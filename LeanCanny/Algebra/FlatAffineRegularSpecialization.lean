/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineGradientJacobian
public import LeanCanny.Algebra.RegularFiberSpecialization
public import LeanCanny.Algebra.PolynomialGridAvoidance
public import LeanCanny.Algebra.AffineDirectionAvoidance

/-! # Exceptional objective directions for fixed affine slices

Right-inverse variables encode regularity of the source/old-height
constraints. The generic Jacobian theorem applies to every guarded root.
Denominator clearing then excludes singular critical roots by a nonzero
objective polynomial. An input-size bound on this factor is separate.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineRegularSpecialization
open MvPolynomial FlatAffineCriticalStage
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {K : Type} {n : ℕ} [Field K]

abbrev Parameters (K : Type) [Field K] (n : ℕ) := MvPolynomial (Fin n) K
abbrev StageSpace (n : ℕ) := Fin 0 ⊕ Variables n
abbrev GuardSpace (s : Finset (Fin n)) := Fin n × Option s
abbrev PointSpace (s : Finset (Fin n)) := StageSpace n ⊕ GuardSpace s
abbrev EquationIndex (s : Finset (Fin n)) := Variables n ⊕ (Option s × Option s)

noncomputable def direction (A : Fin n → Fin n → K) (r : Fin (n + 1)) (i : Fin n) : Parameters K n :=
  Fin.cases (X i) (fun j => C (A j i)) r

noncomputable def levels (β : Fin n → K) (j : Fin n) : MvPolynomial (Fin 0) (Parameters K n) := C (C (β j))

noncomputable def stage (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) : Variables n → MvPolynomial (StageSpace n) (Parameters K n) :=
  row (p.map C) s (direction A) (levels β)

noncomputable def constraintEntry (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) : Option s → Fin n → MvPolynomial (StageSpace n) (Parameters K n)
  | none, i => rename ambient ((pderiv i p).map C)
  | some j, i => C (C (A j.val i))

noncomputable def guarded (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) :
    EquationIndex s → MvPolynomial (PointSpace s) (Parameters K n)
  | .inl r => rename Sum.inl (stage p s A β r)
  | .inr (i, j) => (∑ k, rename Sum.inl (constraintEntry p s A i k) * X (Sum.inr (k, j))) -
      if i = j then 1 else 0

noncomputable def jacobian (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) : MvPolynomial (PointSpace s) (Parameters K n) :=
  rename Sum.inl (TriangularPolynomialSystem.spatialJacobian (stage p s A β))

variable {L : Type} [Field L] [Algebra K L]

theorem eval_constraintEntry (φ : Parameters K n →+* L) (hφ : φ.comp C = algebraMap K L)
    (p : MvPolynomial (Fin n) K) (s : Finset (Fin n)) (A : Fin n → Fin n → K)
    (z : StageSpace n → L) (j : Option s) (i : Fin n) :
    (constraintEntry p s A j i).eval₂ φ z =
      GenericAffineCriticalJacobian.constraintMatrix p s A (z ∘ ambient) j i := by
  cases j with
  | none => simp only [constraintEntry, eval₂_rename, eval₂_map, hφ,
      GenericAffineCriticalJacobian.constraintMatrix, aeval_def]
  | some j =>
    simp only [constraintEntry, eval₂_C, GenericAffineCriticalJacobian.constraintMatrix]
    exact congrArg (fun f : K →+* L => f (A j.val i)) hφ

theorem guarded_roots (φ : Parameters K n →+* L) (hφ : φ.comp C = algebraMap K L)
    (p : MvPolynomial (Fin n) K) (s : Finset (Fin n)) (A : Fin n → Fin n → K) (β : Fin n → K)
    (z : PointSpace s → L) (hz : ∀ i, (guarded p s A β i).eval₂ φ z = 0) :
    (∀ i, (stage p s A β i).eval₂ φ (z ∘ Sum.inl) = 0) ∧
      Function.Surjective (GenericAffineCriticalJacobian.constraintMatrix p s A ((z ∘ Sum.inl) ∘ ambient)).mulVec := by
  refine ⟨?_, ?_⟩
  · intro i
    simpa only [guarded, eval₂_rename] using hz (Sum.inl i)
  · apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
    refine ⟨fun k j => z (Sum.inr (k, j)), ?_⟩
    apply Matrix.ext
    intro i j
    have H := hz (Sum.inr (i, j))
    simp only [guarded, eval₂_sub, eval₂_sum, eval₂_mul, eval₂_rename, eval₂_X,
      eval_constraintEntry φ hφ] at H
    have he : (if i = j then (1 : MvPolynomial (PointSpace s) (Parameters K n)) else 0).eval₂ φ z =
        if i = j then 1 else 0 := by split_ifs <;> simp
    rw [he] at H
    simpa only [Matrix.mul_apply, Matrix.one_apply] using sub_eq_zero.mp H

omit [Algebra K L] in
theorem eval_jacobian (φ : Parameters K n →+* L) (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (z : PointSpace s → L) :
    (jacobian p s A β).eval₂ φ z =
      (FlatAffineCriticalRegularity.matrix φ (p.map C) s (direction A) (levels β) (z ∘ Sum.inl)).det := by
  rw [jacobian, eval₂_rename]
  change (eval₂Hom φ (z ∘ Sum.inl)) (Matrix.det _) = _
  rw [RingHom.map_det]
  rfl

theorem guarded_complete (φ : Parameters K n →+* L) (hφ : φ.comp C = algebraMap K L)
    (p : MvPolynomial (Fin n) K) (s : Finset (Fin n)) (A : Fin n → Fin n → K) (β : Fin n → K)
    (z : StageSpace n → L) (hz : ∀ i, (stage p s A β i).eval₂ φ z = 0)
    (hreg : Function.Surjective (GenericAffineCriticalJacobian.constraintMatrix p s A (z ∘ ambient)).mulVec) :
    ∃ y : PointSpace s → L, y ∘ Sum.inl = z ∧ ∀ i, (guarded p s A β i).eval₂ φ y = 0 := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hreg
  let y : PointSpace s → L := Sum.elim z (fun q => B q.1 q.2)
  have hy : y ∘ Sum.inl = z := rfl
  refine ⟨y, hy, ?_⟩
  intro r
  cases r with
  | inl r => simpa only [guarded, eval₂_rename, hy] using hz r
  | inr q =>
    rcases q with ⟨i, j⟩
    have H := congrArg (fun M : Matrix (Option s) (Option s) L => M i j) hB
    simp only [Matrix.mul_apply, Matrix.one_apply] at H
    simp only [guarded, eval₂_sub, eval₂_sum, eval₂_mul, eval₂_rename, eval₂_X,
      eval_constraintEntry φ hφ, hy, y, Sum.elim_inr]
    have he : (if i = j then (1 : MvPolynomial (PointSpace s) (Parameters K n)) else 0).eval₂ φ y =
        if i = j then 1 else 0 := by split_ifs <;> simp
    rw [he]
    exact sub_eq_zero.mpr H

noncomputable def specialize (u : Fin n → ℕ) : Parameters K n →+* L :=
  eval₂Hom (algebraMap K L) (fun i => (u i : L))

theorem specialize_comp (u : Fin n → ℕ) : (specialize (K := K) (L := L) u).comp C = algebraMap K L := by
  ext k
  simp [specialize]

variable [CharZero K]
attribute [local irreducible] guarded jacobian

theorem exists_exceptional (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) :
    ∃ d : Parameters K n, d ≠ 0 ∧ ∀ (L : Type) [Field L]
      (φ : Parameters K n →+* L) (z : PointSpace s → L),
      φ d ≠ 0 → (∀ i, (guarded p s A β i).eval₂ φ z = 0) → (jacobian p s A β).eval₂ φ z ≠ 0 := by
  let F := FractionRing (Parameters K n)
  apply RegularFiberSpecialization.exists_exceptional (F := F) (guarded p s A β) (jacobian p s A β)
  intro L _ _ z hz
  let : Algebra K L := Algebra.compHom L (algebraMap K F)
  let : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
  let φ : Parameters K n →+* L := (algebraMap F L).comp (algebraMap (Parameters K n) F)
  have hφ : φ.comp C = algebraMap K L := by
    rw [← MvPolynomial.algebraMap_eq]
    dsimp only [φ]
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq K (Parameters K n) F,
      ← IsScalarTower.algebraMap_eq K F L]
  let ψ : Parameters K n →ₐ[K] L :=
    { φ with
      commutes' := by
        intro k
        rw [MvPolynomial.algebraMap_eq]
        exact congrArg (fun f : K →+* L => f k) hφ }
  have hψ : Function.Injective ψ := (algebraMap F L).injective.comp
    (IsFractionRing.injective (Parameters K n) F)
  have hind : AlgebraicIndependent K (fun i : Fin n => φ (X i)) :=
    (MvPolynomial.algebraicIndependent_X (Fin n) K).map (f := ψ) hψ.injOn
  have hr : ∀ i, (guarded p s A β i).eval₂ φ z = 0 := by
    intro i
    simpa only [aeval_def, eval₂_map] using hz i
  have H := guarded_roots φ hφ p s A β z hr
  rw [aeval_def, eval₂_map]
  change (jacobian p s A β).eval₂ φ z ≠ 0
  rw [eval_jacobian]
  apply FlatAffineGradientJacobian.det_ne_zero_of_comp C φ hφ p s A β (fun i => φ (X i))
    (direction A) _ (levels β) (z ∘ Sum.inl) hind H.1 _ H.2
  · intro r i
    refine Fin.cases rfl (fun j => ?_) r
    exact congrArg (fun f : K →+* L => f (A j i)) hφ
  · intro j _hj
    simp only [levels, eval₂_C]
    exact congrArg (fun f : K →+* L => f (β j)) hφ

/-- One natural-number direction works over every extension field, and can
avoid any additional prescribed nonzero objective polynomial. The bound here
is qualitative in the exceptional polynomial, not in source input size. -/
theorem exists_nat_regular (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (e : Parameters K n) (he : e ≠ 0) :
    ∃ B : ℕ, ∃ u : Fin n → ℕ, (∀ i, u i ≤ B) ∧
      e.eval (fun i => (u i : K)) ≠ 0 ∧
      ∀ (L : Type) [Field L] [Algebra K L] (z : StageSpace n → L),
        (∀ i, (stage p s A β i).eval₂ (specialize u) z = 0) →
        Function.Surjective (GenericAffineCriticalJacobian.constraintMatrix p s A (z ∘ ambient)).mulVec →
        (FlatAffineCriticalRegularity.matrix (specialize u) (p.map C) s (direction A) (levels β) z).det ≠ 0 := by
  obtain ⟨d, hd, hgood⟩ := exists_exceptional p s A β
  obtain ⟨u, hu, hnonzero⟩ := PolynomialGridAvoidance.exists_nat_eval_ne_zero (d * e)
    (mul_ne_zero hd he) (d * e).totalDegree le_rfl
  refine ⟨(d * e).totalDegree, u, hu, (mul_ne_zero_iff.mp (by simpa only [map_mul] using hnonzero)).2, ?_⟩
  intro L _ _ z hz hreg
  let φ : Parameters K n →+* L := specialize u
  have hφ : φ.comp C = algebraMap K L := specialize_comp u
  have hφprod : φ (d * e) ≠ 0 := by
    have H := MvPolynomial.hom_eval₂ (d * e) (RingHom.id K) (algebraMap K L) (fun i => (u i : K))
    simp only [eval₂_id, RingHom.comp_id, map_natCast] at H
    change (d * e).eval₂ (algebraMap K L) (fun i => (u i : L)) ≠ 0
    rw [← H]
    exact fun h => hnonzero ((algebraMap K L).injective (h.trans (map_zero _).symm))
  have hφd : φ d ≠ 0 := (mul_ne_zero_iff.mp (by simpa only [map_mul] using hφprod)).1
  obtain ⟨y, hy, hyroot⟩ := guarded_complete φ hφ p s A β z hz hreg
  have H := hgood L φ y hφd hyroot
  rw [eval_jacobian, hy] at H
  exact H

/-- A new natural-number height can avoid the old span and make every
critical root on a regular affine slice nonsingular. The size allowance is
not yet bounded as a function of the original source encoding. -/
theorem exists_nat_good (p : MvPolynomial (Fin n) K) (s : Finset (Fin n)) (hs : s.card < n)
    (A : Fin n → Fin n → K) (β : Fin n → K) :
    ∃ B : ℕ, ∃ u : Fin n → ℕ, (∀ i, u i ≤ B) ∧
      ∀ (L : Type) [Field L] [Algebra K L],
        (¬ ∃ c : s → L, ∀ i, (u i : L) = ∑ j : s, c j * algebraMap K L (A j.val i)) ∧
        ∀ z : StageSpace n → L, (∀ i, (stage p s A β i).eval₂ (specialize u) z = 0) →
          Function.Surjective (GenericAffineCriticalJacobian.constraintMatrix p s A (z ∘ ambient)).mulVec →
          (FlatAffineCriticalRegularity.matrix (specialize u) (p.map C) s (direction A) (levels β) z).det ≠ 0 := by
  obtain ⟨γ, hγ, hann⟩ := AffineDirectionAvoidance.exists_annihilator s hs A
  let e := AffineDirectionAvoidance.polynomial γ
  obtain ⟨B, u, hu, he, hgood⟩ := exists_nat_regular p s A β e (AffineDirectionAvoidance.ne_zero γ hγ)
  refine ⟨B, u, hu, ?_⟩
  intro L _ _
  have heL : e.eval₂ (algebraMap K L) (fun i => (u i : L)) ≠ 0 := by
    have H := MvPolynomial.hom_eval₂ e (RingHom.id K) (algebraMap K L) (fun i => (u i : K))
    simp only [eval₂_id, RingHom.comp_id, map_natCast] at H
    rw [← H]
    exact fun h => he ((algebraMap K L).injective (h.trans (map_zero _).symm))
  exact ⟨AffineDirectionAvoidance.not_in_span s A γ hann _ heL, hgood L⟩

end LeanCanny.Algebra.FlatAffineRegularSpecialization
