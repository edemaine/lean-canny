/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCoordinateCoarsening
public import LeanCanny.Algebra.FermatScaledCoordinateCone

/-! # Coarsening remains finite for nonzero scaled coordinate normals

Each height may use its own nonzero integer scale. This includes doubled
normal rows used to encode ancestral midpoint levels exactly.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineScaledCoordinateCoarsening
open MvPolynomial FlatAffineCriticalTower FlatAffineTowerCoarsening
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem coordinate_cone (c : ℤ) (hc : c ≠ 0) (D : ℕ) (hD : 1 < D)
    (scale : Fin n → ℤ) (hscale : ∀ j, scale j ≠ 0) (s : Finset (Fin n)) (h : Fin n) :
    FlatAffinePowerTower.ConeRootFree (C c * ∑ i : Fin n, X i ^ D) (s.erase h)
      (Fin.cases (fun i => scale h * FermatCoordinateCone.normal h i)
        (fun j i => scale j * FermatCoordinateCone.normal j i)) := by
  apply FlatAffinePowerTower.coneRootFree_of_critical
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have hs' (j : Fin n) : (scale j : ℚ) ≠ 0 := by exact_mod_cast hscale j
  have H := FermatScaledCoordinateCone.criticalRootFree (K := ℚ) (L := ℂ) (c : ℚ) hc' D hD
    (scale h : ℚ) (hs' h) (fun j => (scale j : ℚ)) hs' (s.erase h) h (by simp)
  convert H using 1 <;> simp [FermatAffineConeFlag.form, FermatCoordinateCone.normal, apply_ite]

theorem cone (c : ℤ) (hc : c ≠ 0) (D : ℕ) (hD : 1 < D)
    (scale : Fin n → ℤ) (hscale : ∀ j, scale j ≠ 0)
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → ℤ) (h : Fin n)
    (hnormal : ∀ j i, a k j.succ i = scale j * FermatCoordinateCone.normal j i)
    (hcone : ∀ t : Fin k, FlatAffinePowerTower.ConeRootFree (C c * ∑ i : Fin n, X i ^ D) (s t.val) (a t.val)) :
    ∀ t : Fin (k + 1), FlatAffinePowerTower.ConeRootFree (C c * ∑ i : Fin n, X i ^ D)
      (active s k h t.val) (directions a k h t.val) := by
  intro t
  by_cases ht : t.val = k
  · simp only [active, directions, ht, ite_true]
    have HE : FlatAffineCriticalCoarsening.table (a k) h =
        Fin.cases (fun i => scale h * FermatCoordinateCone.normal h i)
          (fun j i => scale j * FermatCoordinateCone.normal j i) := by
      funext j i
      refine Fin.cases ?_ (fun r => ?_) j
      · exact hnormal h i
      · exact hnormal r i
    rw [HE]
    exact coordinate_cone c hc D hD scale hscale (s k) h
  · simpa only [active, directions, ite_eq_right ht] using hcone ⟨t.val, by omega⟩

theorem finite_roots (low : MvPolynomial (Fin n) ℤ) (c : ℤ) (hc : c ≠ 0)
    (D : ℕ) (hD : 1 < D) (hlow : low.totalDegree < D)
    (scale : Fin n → ℤ) (hscale : ∀ j, scale j ≠ 0)
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → ℤ)
    (b : (t : ℕ) → Fin n → Level n t ℤ) (h : Fin n)
    (hnormal : ∀ j i, a k j.succ i = scale j * FermatCoordinateCone.normal j i)
    (hcone : ∀ t : Fin k, FlatAffinePowerTower.ConeRootFree (C c * ∑ i : Fin n, X i ^ D) (s t.val) (a t.val)) :
    {z : Fin ((k + 1) * width n) → ℝ | ∀ i,
      (FlatAffineCriticalTower.system (low + C c * ∑ i : Fin n, X i ^ D)
        (active s k h) (directions a k h) b (k + 1) i).eval₂ (Int.castRingHom ℝ) z = 0}.Finite := by
  apply FlatAffinePowerTower.finite_real_original_roots low _ D hlow ?_ hD _ _ _
    (cone c hc D hD scale hscale s a h hnormal hcone)
  apply IsHomogeneous.C_mul
  apply IsHomogeneous.sum
  intro i _
  simpa only [one_mul] using (isHomogeneous_X (R := ℤ) i).pow D

end LeanCanny.Algebra.FlatAffineScaledCoordinateCoarsening
