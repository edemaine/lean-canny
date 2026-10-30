/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CoordinateTerminalCritical

/-! # Critical lifts at terminal slices with scaled coordinate normals

Every feasible terminal point has a critical lift even when the source root
is multiple. Scaling all coordinate normals divides the explicit multiplier
vector and preserves the original terminal equations.
-/

@[expose] public section
namespace LeanCanny.Geometry.ScaledCoordinateTerminalCritical
open LeanCanny.Algebra MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {ι : Type*}

noncomputable def table (c : ℤ) (r : Fin n) (j : Fin (n + 1)) (i : Fin n) : ℤ :=
  c * CoordinateTerminalCritical.table r j i
noncomputable def multipliers (c : ℤ) (p : MvPolynomial (Fin n) ℤ) (r : Fin n) (z : Fin n → ℝ)
    (j : Fin (n + 1)) : ℝ := CoordinateTerminalCritical.multipliers p r z j / (c : ℝ)

lemma gradient_sum (c : ℤ) (r : Fin n) (mu : Fin (n + 1) → ℝ) (i : Fin n) :
    (∑ j, ((table c r j i : ℤ) : ℝ) * mu j) =
      (c : ℝ) * ((if i = r then mu 0 else 0) + mu i.succ) := by
  rw [← CoordinateTerminalCritical.gradient_sum r mu i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [table, Int.cast_mul, mul_assoc]

theorem exists_root (c : ℤ) (hc : c ≠ 0) (p : MvPolynomial (Fin n) ℤ)
    (r : Fin n) (b : Fin n → MvPolynomial ι ℤ) (x : ι → ℝ) (z : Fin n → ℝ)
    (hp : p.eval₂ (Int.castRingHom ℝ) z = 0)
    (hl : ∀ j ∈ Finset.univ.erase r, ∑ i, ((table c r j.succ i : ℤ) : ℝ) * z i = (b j).eval₂ (Int.castRingHom ℝ) x) :
    ∀ j, (FlatAffineCriticalStage.row p (Finset.univ.erase r) (table c r) b j).eval₂ (Int.castRingHom ℝ)
      (Sum.elim x (Sum.elim z (multipliers c p r z))) = 0 := by
  have HC : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  apply (FlatAffineCriticalStage.roots_iff (Int.castRingHom ℝ) p (Finset.univ.erase r) (table c r) b _).mpr
  refine ⟨hp, hl, ?_, ?_⟩
  · intro i
    change (pderiv i p).eval₂ (Int.castRingHom ℝ) z = ∑ j, ((table c r j i : ℤ) : ℝ) * multipliers c p r z j
    rw [gradient_sum]
    by_cases hi : i = r
    · simp only [multipliers, CoordinateTerminalCritical.multipliers, Fin.cases_zero, Fin.cases_succ, hi, ite_true, zero_div, add_zero]
      exact (mul_div_cancel₀ _ HC).symm
    · simp only [multipliers, CoordinateTerminalCritical.multipliers, Fin.cases_zero, Fin.cases_succ, hi, ite_false, zero_add]
      exact (mul_div_cancel₀ _ HC).symm
  · intro j hj
    have HE : j = r := by simpa only [Finset.mem_erase, Finset.mem_univ, and_true, not_not] using hj
    change multipliers c p r z j.succ = 0
    subst j
    simp only [multipliers, CoordinateTerminalCritical.multipliers, Fin.cases_succ, ite_true, zero_div]

end LeanCanny.Geometry.ScaledCoordinateTerminalCritical
