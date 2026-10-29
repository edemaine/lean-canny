/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineCriticalOriginalJacobian
public import LeanCanny.Algebra.AffineConeFlag
public import LeanCanny.Algebra.HomogenizationAtInfinity

/-! # A projective bad-root system for affine-height critical stages

Homogenize the power-coordinate affine rows and append the original Lagrange
Jacobian. The appended degree is strictly above the actual determinant degree,
so its row vanishes at infinity. The remaining rows there are exactly the
leading-cone system. Finite affine slice regularity and leading-cone
transversality therefore exclude every generic nonzero projective bad root.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineCriticalPowerBadSystem
open MvPolynomial FlatAffineCriticalStage
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u
variable {K L : Type u} {n : ℕ} [Field K] [Field L] [Algebra K L]

def badDegree (n D : ℕ) : ℕ := (2 * n + 2) * D

noncomputable def rows (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) :
    Option (Variables n) → MvPolynomial (Option (Variables n)) (MvPolynomial (Fin n) K) :=
  HomogeneousBadSystem.rows (AffineCriticalPowerSystem.rows p D s A β)
    (AffineCriticalConeSystem.degrees D s) (AffineCriticalOriginalJacobian.jacobian p s A) (badDegree n D)

def degrees (D : ℕ) (s : Finset (Fin n)) : Option (Variables n) → ℕ :=
  HomogeneousBadSystem.degrees (AffineCriticalConeSystem.degrees D s) (badDegree n D)

theorem homogeneous (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (j : Option (Variables n)) :
    (rows p D s A β j).IsHomogeneous (degrees D s j) :=
  HomogeneousBadSystem.homogeneous _ _ _ _ j

theorem source_degree (low H : MvPolynomial (Fin n) K) (D : ℕ) (hlow : low.totalDegree < D)
    (hH : H.IsHomogeneous D) : (low + H).totalDegree ≤ D :=
  (totalDegree_add _ _).trans (max_le hlow.le hH.totalDegree_le)

theorem jacobian_degree_lt (low H : MvPolynomial (Fin n) K) (D : ℕ) (hlow : low.totalDegree < D)
    (hH : H.IsHomogeneous D) (s : Finset (Fin n)) (A : Fin n → Fin n → K) :
    (AffineCriticalOriginalJacobian.jacobian (low + H) s A).totalDegree < badDegree n D :=
  (AffineCriticalOriginalJacobian.degree_le (low + H) D (source_degree low H D hlow hH) s A).trans_lt
    (Nat.mul_lt_mul_of_pos_right (by omega) (by omega))

omit [Algebra K L] in
theorem eval_infinity (φ : MvPolynomial (Fin n) K →+* L)
    (low H : MvPolynomial (Fin n) K) (D : ℕ) (hlow : low.totalDegree < D)
    (hH : H.IsHomogeneous D) (hD : 1 < D) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (y : Option (Variables n) → L) (hy : y none = 0)
    (j : Variables n) : (rows (low + H) D s A β (some j)).eval₂ φ y =
      (AffineCriticalConeSystem.rows H D s A j).eval₂ φ (y ∘ some) := by
  change (WeightedHomogenization.homogenize (fun _ => 1) (AffineCriticalConeSystem.degrees D s j)
    (AffineCriticalPowerSystem.rows (low + H) D s A β j)).eval₂ φ y = _
  rw [AffineCriticalPowerSystem.split_rows]
  exact HomogenizationAtInfinity.eval_leading φ _ _ _
    (AffineCriticalPowerSystem.lower_degree low D hlow hD s β j)
    (AffineCriticalConeSystem.homogeneous H D hH s A j) y hy

theorem parameter_degree (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (j : Option (Variables n)) :
    NestedTotalDegree.Bound (rows p D s A β j) (2 * n + 1) := by
  cases j with
  | none => exact NestedTotalDegree.homogenize (AffineCriticalOriginalJacobian.parameter_degree p s A) _ _
  | some j =>
    intro e
    exact (NestedTotalDegree.homogenize (AffineCriticalPowerSystem.parameter_degree p D s A β j) _ _ e).trans (by omega)

def layout (n : ℕ) : Option (Variables n) ≃ Fin (2 * n + 2) :=
  HomogenizationLayout.variableEquiv (AffineCriticalConeSystem.layout n)

noncomputable def nativeRows (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (j : Fin (2 * n + 2)) :
    MvPolynomial (Fin (2 * n + 2)) (MvPolynomial (Fin n) K) :=
  rename (layout n) (rows p D s A β ((layout n).symm j))

def nativeDegrees (D : ℕ) (s : Finset (Fin n)) (j : Fin (2 * n + 2)) : ℕ :=
  degrees D s ((layout n).symm j)

theorem native_homogeneous (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (j : Fin (2 * n + 2)) :
    (nativeRows p D s A β j).IsHomogeneous (nativeDegrees D s j) :=
  (homogeneous p D s A β ((layout n).symm j)).rename_isHomogeneous

theorem native_parameter_degree (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (j : Fin (2 * n + 2)) :
    NestedTotalDegree.Bound (nativeRows p D s A β j) (2 * n + 1) :=
  NestedTotalDegree.rename (layout n) (parameter_degree p D s A β ((layout n).symm j))

theorem degrees_pos (D : ℕ) (hD : 1 < D) (s : Finset (Fin n)) (j : Option (Variables n)) :
    0 < degrees D s j := by
  cases j with
  | none => change 0 < badDegree n D; unfold badDegree; positivity
  | some j => exact AffineCriticalConeSystem.degrees_pos D hD s j

theorem degrees_le (D : ℕ) (hD : 1 < D) (s : Finset (Fin n)) (j : Option (Variables n)) :
    degrees D s j ≤ badDegree n D := by
  cases j with
  | none => exact le_rfl
  | some j =>
    apply (AffineCriticalConeSystem.degrees_le D s (by omega) j).trans
    change D ≤ (2 * n + 2) * D
    nlinarith

omit [Algebra K L] in
theorem no_root_of_native (φ : MvPolynomial (Fin n) K →+* L)
    (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K)
    (hfree : ∀ z : Fin (2 * n + 2) → L, (∀ j, (nativeRows p D s A β j).eval₂ φ z = 0) → z = 0)
    (y : Option (Variables n) → L) (hy : ∀ j, (rows p D s A β j).eval₂ φ y = 0) : y = 0 := by
  have hz : (y ∘ (layout n).symm) = 0 := by
    apply hfree
    intro j
    simpa only [nativeRows, eval₂_rename, Function.comp_def, Equiv.symm_apply_apply] using hy ((layout n).symm j)
  funext j
  have H := congrFun hz (layout n j)
  simpa only [Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] using H

omit [Algebra K L] in
theorem affine_regular_of_native (φ : MvPolynomial (Fin n) K →+* L)
    (low H : MvPolynomial (Fin n) K) (D : ℕ) (hlow : low.totalDegree < D)
    (hH : H.IsHomogeneous D) (hD : 1 < D) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K)
    (hfree : ∀ z : Fin (2 * n + 2) → L, (∀ j, (nativeRows (low + H) D s A β j).eval₂ φ z = 0) → z = 0)
    (z : Variables n → L) (hz : ∀ j, (AffineCriticalPowerSystem.rows (low + H) D s A β j).eval₂ φ z = 0) :
    (AffineCriticalOriginalJacobian.jacobian (low + H) s A).eval₂ φ z ≠ 0 := by
  intro hJ
  have hr := HomogeneousBadSystem.chart_root φ (AffineCriticalPowerSystem.rows (low + H) D s A β)
    (AffineCriticalConeSystem.degrees D s) (AffineCriticalOriginalJacobian.jacobian (low + H) s A)
    (badDegree n D) (AffineCriticalPowerSystem.degree_le low H D hlow hH hD s A β)
    (jacobian_degree_lt low H D hlow hH s A).le z hz hJ
  have H := no_root_of_native φ (low + H) D s A β hfree (fun i => i.elim 1 z) hr
  exact one_ne_zero (congrFun H none)

omit [Algebra K L] in
/-- The appended bad row vanishes at infinity, so a retained certificate
also retains the leading-cone direction, rather than just affine regularity. -/
theorem cone_free_of_native (φ : MvPolynomial (Fin n) K →+* L)
    (low H : MvPolynomial (Fin n) K) (D : ℕ) (hlow : low.totalDegree < D)
    (hH : H.IsHomogeneous D) (hD : 1 < D) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K)
    (hfree : ∀ z : Fin (2 * n + 2) → L, (∀ j, (nativeRows (low + H) D s A β j).eval₂ φ z = 0) → z = 0)
    (x : Variables n → L) (hx : ∀ j, (AffineCriticalConeSystem.rows H D s A j).eval₂ φ x = 0) : x = 0 := by
  let y : Option (Variables n) → L := fun j => j.elim 0 x
  have hy : ∀ j, (rows (low + H) D s A β j).eval₂ φ y = 0 := by
    intro j
    cases j with
    | none =>
      exact HomogenizationAtInfinity.eval_lower φ _ _ (jacobian_degree_lt low H D hlow hH s A) y rfl
    | some j =>
      rw [eval_infinity φ low H D hlow hH hD s A β y rfl j]
      exact hx j
  have H := no_root_of_native φ (low + H) D s A β hfree y hy
  funext j
  exact congrFun H (some j)

/-- All finite roots are regular in the original coordinates, and the cone
flag excludes infinity roots. No regularity of the power substitution is used. -/
theorem no_root [CharZero K] (φ : MvPolynomial (Fin n) K →+* L)
    (hφ : φ.comp C = algebraMap K L) (hinj : Function.Injective φ)
    (low H : MvPolynomial (Fin n) K) (D : ℕ) (hlow : low.totalDegree < D)
    (hH : H.IsHomogeneous D) (hD : 1 < D) (s : Finset (Fin n)) (hs : s.card < n)
    (A : Fin n → Fin n → K) (β : Fin n → K) (hcone : AffineConeFlag.Transverse (L := L) H s A)
    (hslice : ∀ x : Fin n → L, aeval x (low + H) = 0 →
      (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = algebraMap K L (β r)) →
      GenericAffineCriticalJacobian.ConstraintIndependent (low + H) s A x)
    (y : Option (Variables n) → L) (hy : ∀ j, (rows (low + H) D s A β j).eval₂ φ y = 0) : y = 0 := by
  apply HomogeneousBadSystem.no_nonzero_root φ (AffineCriticalPowerSystem.rows (low + H) D s A β)
    (AffineCriticalConeSystem.degrees D s) (AffineCriticalOriginalJacobian.jacobian (low + H) s A)
    (badDegree n D) (AffineCriticalPowerSystem.degree_le low H D hlow hH hD s A β)
    (jacobian_degree_lt low H D hlow hH s A).le
    (AffineCriticalOriginalJacobian.generic_regular φ hφ hinj (low + H) D s A β hslice) ?_ y hy
  intro z hz0 hz
  have hroot (j : Variables n) : (AffineCriticalConeSystem.rows H D s A j).eval₂ φ (z ∘ some) = 0 := by
    rw [← eval_infinity φ low H D hlow hH hD s A β z hz0 j]
    exact hz j
  have hx := AffineCriticalConeSystem.no_root φ hφ H D hH hD s hs A
    (AffineCriticalConeSystem.independent_parameters φ hφ hinj) hcone.1 hcone.2 (z ∘ some) hroot
  funext j
  cases j with
  | none => exact hz0
  | some j => exact congrFun hx j

theorem native_no_root [CharZero K] (φ : MvPolynomial (Fin n) K →+* L)
    (hφ : φ.comp C = algebraMap K L) (hinj : Function.Injective φ)
    (low H : MvPolynomial (Fin n) K) (D : ℕ) (hlow : low.totalDegree < D)
    (hH : H.IsHomogeneous D) (hD : 1 < D) (s : Finset (Fin n)) (hs : s.card < n)
    (A : Fin n → Fin n → K) (β : Fin n → K) (hcone : AffineConeFlag.Transverse (L := L) H s A)
    (hslice : ∀ x : Fin n → L, aeval x (low + H) = 0 →
      (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = algebraMap K L (β r)) →
      GenericAffineCriticalJacobian.ConstraintIndependent (low + H) s A x)
    (z : Fin (2 * n + 2) → L) (hz : ∀ j, (nativeRows (low + H) D s A β j).eval₂ φ z = 0) : z = 0 := by
  have hz' (j : Option (Variables n)) : (rows (low + H) D s A β j).eval₂ φ (z ∘ layout n) = 0 := by
    simpa only [nativeRows, eval₂_rename, Equiv.symm_apply_apply] using hz (layout n j)
  have H := no_root φ hφ hinj low H D hlow hH hD s hs A β hcone hslice (z ∘ layout n) hz'
  funext j
  have he := congrFun H ((layout n).symm j)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using he

end LeanCanny.Algebra.AffineCriticalPowerBadSystem
