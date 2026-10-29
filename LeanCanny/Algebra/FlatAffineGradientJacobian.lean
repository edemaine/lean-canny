/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.GenericAffineCriticalJacobian

/-! # The gradient block of the actual affine critical-stage Jacobian -/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineGradientJacobian
open MvPolynomial FlatAffineCriticalStage FlatAffineCriticalRegularity
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {ι R T : Type*} {n : ℕ} [CommRing R] [CommRing T]

theorem ambient_entry (φ : R →+* T) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R)
    (z : (ι ⊕ Variables n) → T) (i k : Fin n) :
    matrix φ p s a b z (Sum.inl i) (Sum.inl k) =
      (pderiv k (pderiv i p)).eval₂ φ (z ∘ ambient) := by
  change (pderiv (ambient k) (gradient p a i)).eval₂ φ z = _
  have he : pderiv (ambient (ι := ι) k) (∑ j, C (a j i) * X (multiplier j)) = 0 := by
    simp [ambient, multiplier, pderiv_X]
  rw [gradient, map_sub, source_ambient, he, sub_zero, eval₂_rename]

theorem multiplier_entry (φ : R →+* T) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R)
    (z : (ι ⊕ Variables n) → T) (i : Fin n) (j : Fin (n + 1)) :
    matrix φ p s a b z (Sum.inl i) (Sum.inr j) = -φ (a j i) := by
  change (pderiv (multiplier j) (gradient p a i)).eval₂ φ z = _
  have he : pderiv (multiplier (ι := ι) j) (∑ r, C (a r i) * X (multiplier r)) = C (a j i) := by
    simp [multiplier, pderiv_X, Pi.single_apply]
  rw [gradient, map_sub, source_multiplier, he, zero_sub, eval₂_neg, eval₂_C]

section Field
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def directions (A : Fin n → Fin n → K) (v : Fin n → L) (r : Fin (n + 1)) (i : Fin n) : L :=
  Fin.cases (v i) (fun j => algebraMap K L (A j i)) r

theorem matrix_eq (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (v : Fin n → L) (b : Fin n → MvPolynomial ι L)
    (z : (ι ⊕ Variables n) → L) :
    matrix (RingHom.id L) (p.map (algebraMap K L)) s (directions A v) b z =
      GenericAffineCriticalJacobian.matrix p s A v (z ∘ ambient) := by
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl k =>
      rw [ambient_entry]
      simp only [pderiv_map, eval₂_map, RingHom.id_comp, GenericAffineCriticalJacobian.matrix, aeval_def]
    | inr r =>
      rw [multiplier_entry]
      rfl
  | inr r =>
    refine Fin.cases ?_ (fun r => ?_) r
    · cases j with
      | inl k =>
        rw [matrix_source_ambient]
        simp only [pderiv_map, eval₂_map, RingHom.id_comp, GenericAffineCriticalJacobian.matrix,
          Fin.cases_zero, aeval_def]
      | inr m =>
        rw [matrix_source_multiplier]
        rfl
    · cases j with
      | inl k =>
        rw [matrix_level_ambient]
        rfl
      | inr m =>
        rw [matrix_level_multiplier]
        rfl

theorem det_ne_zero [CharZero K] (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (v : Fin n → L)
    (b : Fin n → MvPolynomial ι L) (z : (ι ⊕ Variables n) → L)
    (hind : AlgebraicIndependent K v)
    (hroot : ∀ i, (row (p.map (algebraMap K L)) s (directions A v) b i).eval₂ (RingHom.id L) z = 0)
    (hlevel : ∀ j ∈ s, (b j).eval₂ (RingHom.id L) (z ∘ Sum.inl) = algebraMap K L (β j))
    (hconstraint : Function.Surjective
      (GenericAffineCriticalJacobian.constraintMatrix p s A (z ∘ ambient)).mulVec) :
    (matrix (RingHom.id L) (p.map (algebraMap K L)) s (directions A v) b z).det ≠ 0 := by
  have H := (roots_iff (RingHom.id L) (p.map (algebraMap K L)) s (directions A v) b z).mp hroot
  have hp : aeval (z ∘ ambient) p = 0 := by
    simpa only [eval₂_map, RingHom.id_comp, aeval_def] using H.1
  have hl (j : Fin n) (hj : j ∈ s) :
      ∑ i, algebraMap K L (A j i) * (z ∘ ambient) i = algebraMap K L (β j) := by
    have h := H.2.1 j hj
    simp only [RingHom.id_apply, directions, Fin.cases_succ] at h
    exact h.trans (hlevel j hj)
  have hg (i : Fin n) : aeval (z ∘ ambient) (pderiv i p) =
      v i * z (multiplier 0) + ∑ j, algebraMap K L (A j i) * z (multiplier j.succ) := by
    have h := H.2.2.1 i
    simpa only [pderiv_map, eval₂_map, RingHom.id_comp, aeval_def, RingHom.id_apply,
      Fin.sum_univ_succ, directions, Fin.cases_zero, Fin.cases_succ] using h
  have hi := GenericAffineCriticalJacobian.independent_of_surjective p s A (z ∘ ambient) hconstraint
  have hμ := GenericAffineCriticalJacobian.multiplier_ne_zero p s A v (z ∘ ambient)
    (fun j => z (multiplier j)) hg H.2.2.2 hi
  rw [matrix_eq]
  exact GenericAffineCriticalJacobian.det_ne_zero p s A β v (z ∘ ambient) (fun j => z (multiplier j))
    hind hp hl hg H.2.2.2 hμ hi

theorem matrix_eq_of_comp (α : K →+* R) (φ : R →+* L) (hφ : φ.comp α = algebraMap K L)
    (p : MvPolynomial (Fin n) K) (s : Finset (Fin n)) (A : Fin n → Fin n → K) (v : Fin n → L)
    (a : Fin (n + 1) → Fin n → R)
    (ha : ∀ r i, φ (a r i) = Fin.cases (v i) (fun j => algebraMap K L (A j i)) r)
    (b : Fin n → MvPolynomial ι R) (z : (ι ⊕ Variables n) → L) :
    matrix φ (p.map α) s a b z = GenericAffineCriticalJacobian.matrix p s A v (z ∘ ambient) := by
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl k =>
      rw [ambient_entry]
      simp only [pderiv_map, eval₂_map, hφ, GenericAffineCriticalJacobian.matrix, aeval_def]
    | inr r =>
      rw [multiplier_entry, ha]
      rfl
  | inr r =>
    refine Fin.cases ?_ (fun r => ?_) r
    · cases j with
      | inl k =>
        rw [matrix_source_ambient]
        simp only [pderiv_map, eval₂_map, hφ, GenericAffineCriticalJacobian.matrix, Fin.cases_zero, aeval_def]
      | inr m => rw [matrix_source_multiplier]; rfl
    · cases j with
      | inl k => rw [matrix_level_ambient, ha]; rfl
      | inr m => rw [matrix_level_multiplier]; rfl

theorem det_ne_zero_of_comp [CharZero K] (α : K →+* R) (φ : R →+* L) (hφ : φ.comp α = algebraMap K L)
    (p : MvPolynomial (Fin n) K) (s : Finset (Fin n)) (A : Fin n → Fin n → K) (β : Fin n → K)
    (v : Fin n → L) (a : Fin (n + 1) → Fin n → R)
    (ha : ∀ r i, φ (a r i) = Fin.cases (v i) (fun j => algebraMap K L (A j i)) r)
    (b : Fin n → MvPolynomial ι R) (z : (ι ⊕ Variables n) → L)
    (hind : AlgebraicIndependent K v)
    (hroot : ∀ i, (row (p.map α) s a b i).eval₂ φ z = 0)
    (hlevel : ∀ j ∈ s, (b j).eval₂ φ (z ∘ Sum.inl) = algebraMap K L (β j))
    (hconstraint : Function.Surjective (GenericAffineCriticalJacobian.constraintMatrix p s A (z ∘ ambient)).mulVec) :
    (matrix φ (p.map α) s a b z).det ≠ 0 := by
  have H := (roots_iff φ (p.map α) s a b z).mp hroot
  have hp : aeval (z ∘ ambient) p = 0 := by
    simpa only [eval₂_map, hφ, aeval_def] using H.1
  have hl (j : Fin n) (hj : j ∈ s) :
      ∑ i, algebraMap K L (A j i) * (z ∘ ambient) i = algebraMap K L (β j) := by
    have h := H.2.1 j hj
    simp only [ha, Fin.cases_succ] at h
    exact h.trans (hlevel j hj)
  have hg (i : Fin n) : aeval (z ∘ ambient) (pderiv i p) =
      v i * z (multiplier 0) + ∑ j, algebraMap K L (A j i) * z (multiplier j.succ) := by
    have h := H.2.2.1 i
    simpa only [pderiv_map, eval₂_map, hφ, aeval_def, ha, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ] using h
  have hi := GenericAffineCriticalJacobian.independent_of_surjective p s A (z ∘ ambient) hconstraint
  have hμ := GenericAffineCriticalJacobian.multiplier_ne_zero p s A v (z ∘ ambient)
    (fun j => z (multiplier j)) hg H.2.2.2 hi
  rw [matrix_eq_of_comp α φ hφ p s A v a ha]
  exact GenericAffineCriticalJacobian.det_ne_zero p s A β v (z ∘ ambient) (fun j => z (multiplier j))
    hind hp hl hg H.2.2.2 hμ hi

end Field

end LeanCanny.Algebra.FlatAffineGradientJacobian
