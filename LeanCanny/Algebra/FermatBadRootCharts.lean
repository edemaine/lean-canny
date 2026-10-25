/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCriticalBadSpecialization
public import LeanCanny.Algebra.HomogeneousBadCharts
public import LeanCanny.Algebra.ProjectiveRootCharts

/-! # Determinant-free charts for the pure-power critical bad-root test

The appended Jacobian vanishes at infinity because its actual degree is
strictly below its homogenization degree. Affine bad roots are detected by
normalized kernel vectors; infinity bad roots use only the explicit pure
powers. No derivative of a homogenized determinant needs to be generated.
-/

@[expose] public section
namespace LeanCanny.Algebra.FermatCriticalBadSpecialization
open MvPolynomial FermatCriticalHomogenization FermatCriticalBadSystem
open scoped Classical Matrix

variable {n : ℕ} {R K : Type*} [CommRing R] [Nontrivial R] [Field K]

theorem jacobian_degree_pred (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ)
    (hlow : low.totalDegree < N) (v : Fin n → R) :
    (jacobian low a N v).totalDegree ≤ (n + 1) * (N - 1) := by
  apply JacobianKernelCharts.degree_le (spatial low a N v) N
  intro i
  apply (spatial_degree low a N hlow v i).trans
  exact Fin.cases le_rfl (fun _ => Nat.sub_le N 1) i

theorem jacobian_degree_strict (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ)
    (hlow : low.totalDegree < N) (v : Fin n → R) :
    (jacobian low a N v).totalDegree < jacobianDegree n N :=
  (jacobian_degree_pred low a N hlow v).trans_lt
    (Nat.mul_lt_mul_of_pos_left (by omega : N - 1 < N) (by omega : 0 < n + 1))

noncomputable def optionRows (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ) (v : Fin n → R) :
    Option (Fin (n + 1)) → MvPolynomial (Option (Fin (n + 1))) R :=
  HomogeneousBadSystem.rows (spatial low a N v) (FermatCriticalInfinity.degrees n N)
    (jacobian low a N v) (jacobianDegree n N)

omit [Nontrivial R] in
theorem root_free_layout_iff (φ : R →+* K) (low : MvPolynomial (Fin (n + 1)) R)
    (a : R) (N : ℕ) (v : Fin n → R) :
    (∀ y : Fin (n + 2) → K, (∀ j, (rows low a N v j).eval₂ φ y = 0) → y = 0) ↔
      (∀ y : Option (Fin (n + 1)) → K, (∀ j, (optionRows low a N v j).eval₂ φ y = 0) → y = 0) := by
  constructor
  · intro h y hy
    let x : Fin (n + 2) → K := fun j => y (layout.symm j)
    have hx (j : Fin (n + 2)) : (rows low a N v j).eval₂ φ x = 0 := by
      simpa only [rows, optionRows, eval₂_rename, Function.comp_def, Equiv.symm_apply_apply, x]
        using hy (layout.symm j)
    have hz := h x hx
    funext j
    have he := congrFun hz (layout j)
    simpa only [x, Equiv.symm_apply_apply, Pi.zero_apply] using he
  · intro h y hy
    let x : Option (Fin (n + 1)) → K := fun j => y (layout j)
    have hx (j : Option (Fin (n + 1))) : (optionRows low a N v j).eval₂ φ x = 0 := by
      simpa only [rows, optionRows, eval₂_rename, Function.comp_def, Equiv.symm_apply_apply, x]
        using hy (layout j)
    have hz := h x hx
    funext j
    have he := congrFun hz (layout.symm j)
    simpa only [x, Equiv.apply_symm_apply, Pi.zero_apply] using he

omit [Nontrivial R] in
theorem eval_option_infinity (φ : R →+* K) (low : MvPolynomial (Fin (n + 1)) R)
    (a : R) (N : ℕ) (hlow : low.totalDegree < N) (hN : 1 < N) (v : Fin n → R)
    (x : Fin (n + 1) → K) (j : Fin (n + 1)) :
    (optionRows low a N v (some j)).eval₂ φ (fun i => i.elim 0 x) =
      (FermatCriticalInfinity.native a N v j).eval₂ φ x := by
  change (FermatCriticalHomogenization.rows low a N v j).eval₂ φ _ = _
  rw [← eval_map, FermatCriticalHomogenization.map_rows]
  rw [eval_infinity (low.map φ) (φ a) N ((PolynomialMapDegree.degree_le φ low).trans_lt hlow) hN]
  rw [← FermatCriticalInfinity.map_native, eval_map]

omit [Nontrivial R] in
theorem infinity_root_free_iff (φ : R →+* K) (low : MvPolynomial (Fin (n + 1)) R)
    (a : R) (N : ℕ) (hlow : low.totalDegree < N) (hN : 1 < N) (v : Fin n → R) :
    (∀ y : Option (Fin (n + 1)) → K, y none = 0 →
      (∀ i, (optionRows low a N v (some i)).eval₂ φ y = 0) → y = 0) ↔
      (∀ x : Fin (n + 1) → K, (∀ i, (FermatCriticalInfinity.native a N v i).eval₂ φ x = 0) → x = 0) := by
  constructor
  · intro h x hx
    have hz := h (fun i => i.elim 0 x) rfl (fun i => by
      rw [eval_option_infinity φ low a N hlow hN v x i]
      exact hx i)
    funext i
    exact congrFun hz (some i)
  · intro h y hy hrows
    let x : Fin (n + 1) → K := fun i => y (some i)
    have he : y = fun i => i.elim 0 x := by
      funext i
      cases i with
      | none => exact hy
      | some i => rfl
    have hx (i : Fin (n + 1)) : (FermatCriticalInfinity.native a N v i).eval₂ φ x = 0 := by
      have hh := hrows i
      rw [he, eval_option_infinity φ low a N hlow hN v x i] at hh
      exact hh
    have hz := h x hx
    funext i
    cases i with
    | none => exact hy
    | some i => exact congrFun hz i

theorem root_free_iff_kernel_infinity_charts (φ : R →+* K) (low : MvPolynomial (Fin (n + 1)) R)
    (a : R) (N : ℕ) (hlow : low.totalDegree < N) (hN : 1 < N) (v : Fin n → R) :
    (∀ y : Fin (n + 2) → K, (∀ j, (rows low a N v j).eval₂ φ y = 0) → y = 0) ↔
      (∀ i : Fin (n + 1), ¬ ∃ x u : Fin (n + 1) → K, u i = 1 ∧
        (∀ j, (spatial low a N v j).eval₂ φ x = 0) ∧
          JacobianKernelCharts.matrix φ (spatial low a N v) x *ᵥ u = 0) ∧
      (∀ i : Fin (n + 1), ¬ ∃ x : Fin (n + 1) → K, x i = 1 ∧
        ∀ j, (FermatCriticalInfinity.native a N v j).eval₂ φ x = 0) := by
  rw [root_free_layout_iff]
  have h := HomogeneousBadSystem.jacobian_root_free_iff φ (spatial low a N v)
    (FermatCriticalInfinity.degrees n N) (jacobianDegree n N) (spatial_degree low a N hlow v)
    (jacobian_degree_strict low a N hlow v)
  change (∀ y : Option (Fin (n + 1)) → K,
      (∀ i, (optionRows low a N v i).eval₂ φ y = 0) → y = 0) ↔ _ at h
  refine h.trans (and_congr Iff.rfl ?_)
  exact (infinity_root_free_iff φ low a N hlow hN v).trans
    (ProjectiveRootCharts.root_free_iff_charts (FermatCriticalInfinity.native a N v)
      (FermatCriticalInfinity.degrees n N) (FermatCriticalInfinity.homogeneous a N v) φ)

end LeanCanny.Algebra.FermatCriticalBadSpecialization
