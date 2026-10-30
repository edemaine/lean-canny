/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffinePowerOriginal
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Transporting varying-height power roots to original critical equations

Odd-power root equivalence is unnecessary for this direction. Substitution
preserves all zero rows and the exact value of every active height row.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffinePowerTower
open MvPolynomial FlatAffineCriticalTower FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

theorem roots_except_original {K : Type*} [Field K] (φ : ℤ →+* K)
    (p : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : 1 < D)
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → ℤ)
    (b : (t : ℕ) → Fin n → Level n t ℤ) (z : Index n k → K) (r : Index n k)
    (hz : ∀ i, i ≠ r → (system p D (fun t : Fin k => s t.val) (fun t => a t.val)
      (fun t => b t.val) i).eval₂ φ z = 0) :
    ∀ i, i ≠ r → (FlatAffineCriticalTower.system p s a b k i).eval₂ φ (powerPoint D z) = 0 := by
  intro i hi
  obtain ⟨⟨t, j⟩, rfl⟩ := (rowEquiv n k).surjective i
  apply (row_zero_iff_original φ p D hD s a b z t j).mp
  simpa only [system_row] using hz (rowEquiv n k (t, j)) hi

theorem height_value_original {K : Type*} [Field K] (φ : ℤ →+* K)
    (p : MvPolynomial (Fin n) ℤ) (D : ℕ) (s : ℕ → Finset (Fin n))
    (a : ℕ → Fin (n + 1) → Fin n → ℤ) (b : (t : ℕ) → Fin n → Level n t ℤ)
    (z : Index n k → K) (t : Fin k) (h : Fin n) (hs : h ∈ s t.val) :
    (FlatAffineCriticalTower.system p s a b k (multiplier t h.succ)).eval₂ φ (powerPoint D z) =
      (row p D (fun t : Fin k => s t.val) (fun t => a t.val) (fun t => b t.val) t (Sum.inr h.succ)).eval₂ φ z := by
  rw [multiplier_eq, FlatAffineCriticalIndexedRows.level_row]
  simp only [row, Fin.cases_succ, hs, ite_true, eval₂_sub,
    eval_height_powerPoint, eval_level_powerPoint]

theorem continuous_powerPoint {T : Type*} [TopologicalSpace T] (D : ℕ)
    (z : T → Index n k → ℝ) (hz : Continuous z) : Continuous (fun t => powerPoint D (z t)) := by
  apply continuous_pi
  intro j
  unfold powerPoint
  cases ((rowEquiv n k).symm j).2 with
  | inl _ => exact (continuous_apply j).comp hz
  | inr _ => exact ((continuous_apply j).comp hz).pow (D - 1)

theorem shifted_of_original (p : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : 1 < D)
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → ℤ)
    (b : (t : ℕ) → Fin n → Level n t ℤ) (z : Index n k → ℝ)
    (t : Fin k) (h : Fin n) (hs : h ∈ s t.val) (v : ℝ)
    (hz : ∀ i, (FlatAffineCriticalTower.system p s a b k i).eval₂ (Int.castRingHom ℝ) (powerPoint D z) =
      if i = multiplier t h.succ then v else 0) :
    ∀ i, (system p D (fun t : Fin k => s t.val) (fun t => a t.val) (fun t => b t.val) i).eval₂
      (Int.castRingHom ℝ) z = if i = multiplier t h.succ then v else 0 := by
  intro i
  by_cases hi : i = multiplier t h.succ
  · subst i
    have HE := system_row p D (fun t : Fin k => s t.val) (fun t => a t.val) (fun t => b t.val) t (Sum.inr h.succ)
    exact (congrArg (fun q => q.eval₂ (Int.castRingHom ℝ) z) HE).trans
      ((height_value_original (Int.castRingHom ℝ) p D s a b z t h hs).symm.trans (hz _))
  · rw [ite_eq_right hi]
    obtain ⟨⟨q, j⟩, rfl⟩ := (rowEquiv n k).surjective i
    rw [system_row]
    exact (row_zero_iff_original (Int.castRingHom ℝ) p D hD s a b z q j).mpr
      ((hz _).trans (ite_eq_right hi))

end LeanCanny.Algebra.FlatAffinePowerTower
