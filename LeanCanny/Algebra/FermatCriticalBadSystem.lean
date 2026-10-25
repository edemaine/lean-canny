/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCriticalHomogenization
public import LeanCanny.Algebra.HomogeneousBadSystem
public import LeanCanny.Algebra.NestedTotalDegree

/-! # A bounded homogeneous system detecting singular critical points

The direction variables are coefficients. The original critical equations
have direction degree at most one, and their spatial Jacobian has coefficient
direction degree at most the spatial dimension. Homogenization and the native
finite-variable layout retain these bounds.
-/

@[expose] public section
namespace LeanCanny.Algebra.FermatCriticalBadSystem
open MvPolynomial FermatCriticalHomogenization
open scoped Classical BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {K : Type*} [CommRing K]

noncomputable def equations (low : MvPolynomial (Fin (n + 1)) K) (a : K) (N : ℕ) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) (MvPolynomial (Fin n) K) :=
  spatial (low.map C) (C a) N (fun i => X i)

theorem equations_eq (low : MvPolynomial (Fin (n + 1)) K) (a : K) (N : ℕ) :
    equations low a N = ProjectionCriticalFamily.spatialEquation ((polynomial low a N).map C) 0 (Fin.cons 1 (fun i => X i)) := by
  unfold equations
  rw [spatial_eq, ← map_polynomial C low a N]

noncomputable def jacobian (low : MvPolynomial (Fin (n + 1)) K) (a : K) (N : ℕ) :
    MvPolynomial (Fin (n + 1)) (MvPolynomial (Fin n) K) :=
  Matrix.det (fun i j => pderiv j (equations low a N i))

def jacobianDegree (n N : ℕ) : ℕ := (n + 1) * N

def degrees (n N : ℕ) : Option (Fin (n + 1)) → ℕ :=
  HomogeneousBadSystem.degrees (FermatCriticalInfinity.degrees n N) (jacobianDegree n N)

noncomputable def rows (low : MvPolynomial (Fin (n + 1)) K) (a : K) (N : ℕ) :
    Option (Fin (n + 1)) → MvPolynomial (Option (Fin (n + 1))) (MvPolynomial (Fin n) K) :=
  HomogeneousBadSystem.rows (equations low a N) (FermatCriticalInfinity.degrees n N)
    (jacobian low a N) (jacobianDegree n N)

def layout : Option (Fin (n + 1)) ≃ Fin (n + 2) := HomogenizationLayout.variableEquiv (Equiv.refl _)

def nativeDegrees (n N : ℕ) : Fin (n + 2) → ℕ := fun j => degrees n N (layout.symm j)

noncomputable def nativeRows (low : MvPolynomial (Fin (n + 1)) K) (a : K) (N : ℕ)
    (j : Fin (n + 2)) : MvPolynomial (Fin (n + 2)) (MvPolynomial (Fin n) K) :=
  rename layout (rows low a N (layout.symm j))

theorem degrees_pos (N : ℕ) (hN : 1 < N) (i : Option (Fin (n + 1))) : 0 < degrees n N i := by
  cases i with
  | none => simp only [degrees, HomogeneousBadSystem.degrees, Option.elim_none, jacobianDegree]; positivity
  | some i => exact FermatCriticalInfinity.degrees_pos N hN i

theorem homogeneous (low : MvPolynomial (Fin (n + 1)) K) (a : K) (N : ℕ) (j : Fin (n + 2)) :
    (nativeRows low a N j).IsHomogeneous (nativeDegrees n N j) :=
  (HomogeneousBadSystem.homogeneous _ _ _ _ (layout.symm j)).rename_isHomogeneous

variable [Nontrivial K]

theorem equations_degree (low : MvPolynomial (Fin (n + 1)) K) (a : K) (N : ℕ)
    (hlow : low.totalDegree < N) (i : Fin (n + 1)) :
    (equations low a N i).totalDegree ≤ FermatCriticalInfinity.degrees n N i := by
  apply spatial_degree
  exact (PolynomialMapDegree.degree_le C low).trans_lt hlow

theorem jacobian_degree (low : MvPolynomial (Fin (n + 1)) K) (a : K) (N : ℕ)
    (hlow : low.totalDegree < N) : (jacobian low a N).totalDegree ≤ jacobianDegree n N := by
  have hq (i : Fin (n + 1)) : (equations low a N i).totalDegree ≤ N :=
    (equations_degree low a N hlow i).trans (by
      refine Fin.cases le_rfl (fun _ => Nat.sub_le N 1) i)
  rw [jacobian, Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro π _
  rw [Units.smul_def]
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  exact (Finset.sum_le_sum fun j _ =>
    (PartialDerivativeDegree.degree_le _ _).trans ((Nat.sub_le _ _).trans (hq (π j)))).trans_eq (by simp [jacobianDegree])

theorem equations_parameter_degree (low : MvPolynomial (Fin (n + 1)) K) (a : K) (N : ℕ)
    (j : Fin (n + 1)) : NestedTotalDegree.Bound (equations low a N j) 1 := by
  rw [equations_eq]
  refine Fin.cases ?_ (fun i => ?_) j
  · intro e
    simp only [ProjectionCriticalFamily.spatialEquation, ite_true, coeff_map, totalDegree_C]
    exact Nat.zero_le _
  · intro e
    simp only [ProjectionCriticalFamily.spatialEquation, ite_eq_right (Fin.succ_ne_zero i),
      pderiv_map, coeff_sub, coeff_C_mul, Fin.cons_succ, coeff_map]
    apply (totalDegree_sub _ _).trans
    apply max_le
    · simp only [totalDegree_C]; exact Nat.zero_le _
    · apply (totalDegree_mul _ _).trans
      simp only [totalDegree_X, totalDegree_C, Nat.add_zero, le_refl]

theorem jacobian_parameter_degree (low : MvPolynomial (Fin (n + 1)) K) (a : K) (N : ℕ) :
    NestedTotalDegree.Bound (jacobian low a N) (n + 1) := by
  have h := NestedTotalDegree.det (fun i j => pderiv j (equations low a N i)) 1
    (fun i j => NestedTotalDegree.pderiv (equations_parameter_degree low a N i) j)
  simpa only [jacobian, Fintype.card_fin, Nat.mul_one] using h

theorem rows_parameter_degree (low : MvPolynomial (Fin (n + 1)) K) (a : K) (N : ℕ)
    (j : Option (Fin (n + 1))) : NestedTotalDegree.Bound (rows low a N j) (n + 1) := by
  cases j with
  | none => exact NestedTotalDegree.homogenize (jacobian_parameter_degree low a N) _ _
  | some j =>
    intro e
    exact (NestedTotalDegree.homogenize (equations_parameter_degree low a N j) _ _ e).trans (by omega)

theorem native_parameter_degree (low : MvPolynomial (Fin (n + 1)) K) (a : K) (N : ℕ)
    (j : Fin (n + 2)) (e : Fin (n + 2) →₀ ℕ) : ((nativeRows low a N j).coeff e).totalDegree ≤ n + 1 :=
  NestedTotalDegree.rename layout (rows_parameter_degree low a N (layout.symm j)) e

end LeanCanny.Algebra.FermatCriticalBadSystem
