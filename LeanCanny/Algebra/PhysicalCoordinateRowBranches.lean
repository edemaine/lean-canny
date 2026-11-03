/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCriticalRows
/-! # Sparse coordinate-normal branches of literal physical critical rows -/
@[expose] public section
namespace LeanCanny.Algebra.PhysicalPowerCriticalRows
open MvPolynomial FlatAffineCriticalStage
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {ι τ : Type*} {n : ℕ}

theorem coordinate_normal_sum (c : Fin (n+1)→ℤ) (f i : Fin (n+1)) (v : Fin (n+2)→MvPolynomial τ ℤ) :
    (∑ j,C (coordinateNormals 2 c f j i)*v j)=
      (if i=f then v 0+v 0 else 0)+C (c i)*v i.succ := by
  simp [coordinateNormals,Fin.sum_univ_succ,apply_ite,eq_comm,two_mul]

theorem coordinate_height_sum (c : Fin (n+1)→ℤ) (f i : Fin (n+1)) (v : Fin (n+1)→MvPolynomial τ ℤ) :
    (∑ j,C (coordinateNormals 2 c f i.succ j)*v j)=C (c i)*v i := by
  simp [coordinateNormals,apply_ite,eq_comm]

theorem renamed_gradient (p : MvPolynomial (Fin (n+1)) ℤ) (s : Finset (Fin (n+1)))
    (c : Fin (n+1)→ℤ) (f i : Fin (n+1)) (H : Fin (n+1)→MvPolynomial ι ℤ)
    (e : (ι⊕Variables (n+1))→τ) :
    rename e (FlatAffineCriticalStage.row p s (coordinateNormals 2 c f) H (.inl i))=
      rename (e∘ambient) (pderiv i p)-
      (if i=f then X (e (multiplier 0))+X (e (multiplier 0)) else 0)-
      C (c i)*X (e (multiplier i.succ)) := by
  simp only [FlatAffineCriticalStage.row,FlatAffineCriticalStage.gradient,map_sub,rename_rename,map_sum,map_mul,rename_C,rename_X]
  rw [coordinate_normal_sum,sub_add_eq_sub_sub]

theorem renamed_equation (p : MvPolynomial (Fin (n+1)) ℤ) (s : Finset (Fin (n+1)))
    (c : Fin (n+1)→ℤ) (f : Fin (n+1)) (H : Fin (n+1)→MvPolynomial ι ℤ)
    (e : (ι⊕Variables (n+1))→τ) :
    rename e (FlatAffineCriticalStage.row p s (coordinateNormals 2 c f) H (.inr 0))=
      rename (e∘ambient) p := by
  simp only [FlatAffineCriticalStage.row,Fin.cases_zero,rename_rename]

theorem renamed_height (p : MvPolynomial (Fin (n+1)) ℤ) (s : Finset (Fin (n+1)))
    (c : Fin (n+1)→ℤ) (f i : Fin (n+1)) (H : Fin (n+1)→MvPolynomial ι ℤ)
    (e : (ι⊕Variables (n+1))→τ) :
    rename e (FlatAffineCriticalStage.row p s (coordinateNormals 2 c f) H (.inr i.succ))=
      if i∈s then C (c i)*X (e (ambient i))-rename (e∘Sum.inl) (H i)
      else X (e (multiplier i.succ)) := by
  by_cases hi : i∈s
  · simp only [FlatAffineCriticalStage.row,Fin.cases_succ,ite_eq_left hi,map_sub,
      AffineHeightPolynomial.polynomial,map_sum,map_mul,rename_C,rename_X,rename_rename]
    rw [coordinate_height_sum]
  · simp only [FlatAffineCriticalStage.row,Fin.cases_succ,ite_eq_right hi,rename_X]

end LeanCanny.Algebra.PhysicalPowerCriticalRows
