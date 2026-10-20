/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.Separation
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-! # A degeneracy in symmetric projection-coordinate recovery

For the three affine solutions (-1,0), (0,0), and (1,0), changing the second
projection coefficient does not change the eliminant. At the middle projected
root, the reflected plus/minus polynomials share the whole cubic. Thus the
fixed symmetric shifts in Canny's report, equations (13)--(15), do not always
give a linear GCD, even when the original projected roots are distinct.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymmetricRecoveryDegeneracy
open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

def node (u : K) : Fin 3 → K := ![-u, 0, u]

def point (i : Fin 3) : Fin 2 → K := ![node (1 : K) i, 0]

def projection (c : Fin 2 → K) (i : Fin 3) : K := ∑ j, c j * point i j

noncomputable def eliminant (c : Fin 2 → K) : K[X] := ∏ i : Fin 3, (X - C (projection c i))

noncomputable def cubic (u : K) : K[X] := X * (X - C u) * (X + C u)

theorem projection_eq (c : Fin 2 → K) (i : Fin 3) : projection c i = c 0 * node (1 : K) i := by
  simp [projection, point, Fin.sum_univ_two]

theorem eliminant_eq (c : Fin 2 → K) : eliminant c = cubic (c 0) := by
  simp only [eliminant, projection_eq, Fin.prod_univ_succ, node, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, mul_neg, mul_one, mul_zero, C_neg, C_0, sub_neg_eq_add, sub_zero, Fin.prod_univ_zero, mul_one]
  unfold cubic
  ring

theorem eliminant_update_second (c : Fin 2 → K) (a : K) :
    eliminant (Function.update c 1 (c 1 + a)) = eliminant c := by
  rw [eliminant_eq, eliminant_eq]
  simp

theorem cubic_monic (u : K) : (cubic u).Monic :=
  (monic_X.mul (monic_X_sub_C u)).mul (monic_X_add_C u)

theorem cubic_degree (u : K) : (cubic u).natDegree = 3 := by
  rw [cubic, (monic_X.mul (monic_X_sub_C u)).natDegree_mul (monic_X_add_C u),
    monic_X.natDegree_mul (monic_X_sub_C u), natDegree_X, natDegree_X_sub_C, natDegree_X_add_C]

theorem cubic_reflection (u : K) : (cubic u).comp (-X) = -cubic u := by
  simp only [cubic, mul_comp, sub_comp, add_comp, X_comp, C_comp]
  ring

theorem source_zero_iff (x : Fin 2 → K) :
    (x 0 ^ 3 - x 0 = 0 ∧ x 1 = 0) ↔ ∃ i : Fin 3, x = point i := by
  constructor
  · rintro ⟨hx, hy⟩
    have hprod : x 0 * (x 0 - 1) * (x 0 + 1) = 0 := by linear_combination hx
    rcases (mul_eq_zero.mp hprod) with h | hm
    · rcases mul_eq_zero.mp h with hz | ho
      · refine ⟨1, ?_⟩
        ext j
        fin_cases j <;> simp [point, node, hz, hy]
      · have hz : x 0 = 1 := sub_eq_zero.mp ho
        refine ⟨2, ?_⟩
        ext j
        fin_cases j <;> simp [point, node, hz, hy]
    · have hz : x 0 = -1 := eq_neg_of_add_eq_zero_left hm
      refine ⟨0, ?_⟩
      ext j
      fin_cases j <;> simp [point, node, hz, hy]
  · rintro ⟨i, rfl⟩
    fin_cases i <;> norm_num [point, node]

theorem no_roots_at_infinity (x : Fin 3 → K) (h0 : x 0 = 0)
    (h1 : x 1 ^ 3 - x 1 * x 0 ^ 2 = 0) (h2 : x 2 = 0) : x = 0 := by
  have hz : x 1 = 0 := by
    rw [h0, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] at h1
    exact eq_zero_of_pow_eq_zero h1
  ext i
  fin_cases i <;> simp [h0, hz, h2]

section
variable [CharZero K]

theorem node_injective (u : K) (hu : u ≠ 0) : Function.Injective (node u) := by
  have hneg : -u ≠ 0 := neg_ne_zero.mpr hu
  have hnu : -u ≠ u := by
    intro h
    have he : (2 : K) * u = 0 := by linear_combination -h
    exact (mul_ne_zero (by norm_num) hu) he
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp only [node] at h
  all_goals first | rfl | exact False.elim (hneg h) | exact False.elim (hneg h.symm) |
    exact False.elim (hu h) | exact False.elim (hu h.symm) | exact False.elim (hnu h) | exact False.elim (hnu h.symm)

theorem cubic_separable (u : K) (hu : u ≠ 0) : (cubic u).Separable := by
  have hp : cubic u = ∏ i : Fin 3, (X - C (node u i)) := by
    simp [Fin.prod_univ_succ, node, cubic]
    ring
  rw [hp]
  exact separable_prod_X_sub_C_iff.mpr (node_injective u hu)

theorem eliminant_separable (c : Fin 2 → K) (hc : c 0 ≠ 0) : (eliminant c).Separable := by
  rw [eliminant_eq]
  exact cubic_separable _ hc


end

variable [DecidableEq K]

theorem reflected_gcd_degree (u : K) : (gcd (cubic u) ((cubic u).comp (-X))).natDegree = 3 := by
  classical
  have hd : cubic u ∣ (cubic u).comp (-X) := ⟨-1, by rw [cubic_reflection]; ring⟩
  rw [gcd_eq_normalize (gcd_dvd_left _ _) (dvd_gcd (dvd_refl _) hd), natDegree_normalize, cubic_degree]

theorem symmetric_pair_not_linear (c : Fin 2 → K) :
    (gcd (eliminant (Function.update c 1 (c 1 - 1)))
      ((eliminant (Function.update c 1 (c 1 + 1))).comp (-X))).natDegree ≠ 1 := by
  classical
  have hm := eliminant_update_second c (-1)
  rw [show c 1 + (-1) = c 1 - 1 by ring] at hm
  rw [hm, eliminant_update_second c 1, eliminant_eq, reflected_gcd_degree]
  decide

end LeanCanny.Algebra.SymmetricRecoveryDegeneracy
