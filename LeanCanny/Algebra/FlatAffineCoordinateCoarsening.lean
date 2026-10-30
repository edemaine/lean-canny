/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineTowerCoarsening
public import LeanCanny.Algebra.FlatAffinePowerOriginal
public import LeanCanny.Algebra.FlatAffinePowerConeBridge
public import LeanCanny.Algebra.FermatCoordinateCone

/-! # Finite coarser critical roots for coordinate heights

The removed coordinate is automatically outside the remaining active set.
The pure-power leading form therefore excludes roots at infinity for the
coarser system. Earlier stages retain their original cone certificates.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineCoordinateCoarsening
open MvPolynomial FlatAffineCriticalTower FlatAffineTowerCoarsening
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

theorem coordinate_cone (c : ℤ) (hc : c ≠ 0) (D : ℕ) (hD : 1 < D)
    (s : Finset (Fin n)) (h : Fin n) :
    FlatAffinePowerTower.ConeRootFree (C c * ∑ i : Fin n, X i ^ D) (s.erase h)
      (Fin.cases (FermatCoordinateCone.normal h) FermatCoordinateCone.normal) := by
  apply FlatAffinePowerTower.coneRootFree_of_critical
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have H := FermatCoordinateCone.criticalRootFree (K := ℚ) (L := ℂ) (c : ℚ) hc' D hD
    (s.erase h) h (by simp)
  convert H using 1 <;> simp [FermatAffineConeFlag.form, FermatCoordinateCone.normal]
  rfl

theorem cone (c : ℤ) (hc : c ≠ 0) (D : ℕ) (hD : 1 < D)
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → ℤ) (h : Fin n)
    (hnormal : ∀ j i, a k j.succ i = FermatCoordinateCone.normal j i)
    (hcone : ∀ t : Fin k, FlatAffinePowerTower.ConeRootFree (C c * ∑ i : Fin n, X i ^ D)
      (s t.val) (a t.val)) :
    ∀ t : Fin (k + 1), FlatAffinePowerTower.ConeRootFree (C c * ∑ i : Fin n, X i ^ D)
      (active s k h t.val) (directions a k h t.val) := by
  intro t
  by_cases ht : t.val = k
  · simp only [active, directions, ht, ite_true]
    have HE : FlatAffineCriticalCoarsening.table (a k) h =
        Fin.cases (FermatCoordinateCone.normal h) FermatCoordinateCone.normal := by
      funext j i
      refine Fin.cases ?_ (fun r => ?_) j
      · exact hnormal h i
      · exact hnormal r i
    rw [HE]
    exact coordinate_cone c hc D hD (s k) h
  · simpa only [active, directions, ite_eq_right ht] using hcone ⟨t.val, by omega⟩

theorem finite_roots (low : MvPolynomial (Fin n) ℤ) (c : ℤ) (hc : c ≠ 0)
    (D : ℕ) (hD : 1 < D) (hlow : low.totalDegree < D)
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → ℤ)
    (b : (t : ℕ) → Fin n → Level n t ℤ) (h : Fin n)
    (hnormal : ∀ j i, a k j.succ i = FermatCoordinateCone.normal j i)
    (hcone : ∀ t : Fin k, FlatAffinePowerTower.ConeRootFree (C c * ∑ i : Fin n, X i ^ D)
      (s t.val) (a t.val)) :
    {z : Fin ((k + 1) * width n) → ℝ | ∀ i,
      (FlatAffineCriticalTower.system (low + C c * ∑ i : Fin n, X i ^ D)
        (active s k h) (directions a k h) b (k + 1) i).eval₂ (Int.castRingHom ℝ) z = 0}.Finite := by
  apply FlatAffinePowerTower.finite_real_original_roots low _ D hlow ?_ hD _ _ _
    (cone c hc D hD s a h hnormal hcone)
  apply IsHomogeneous.C_mul
  apply IsHomogeneous.sum
  intro i _
  simpa only [one_mul] using (isHomogeneous_X (R := ℤ) i).pow D

end LeanCanny.Algebra.FlatAffineCoordinateCoarsening
