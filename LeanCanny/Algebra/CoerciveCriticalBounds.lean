/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MvCoefficientMass
public import LeanCanny.Algebra.NestedCoefficientMass
public import LeanCanny.Algebra.WeightedHomogenization
public import LeanCanny.Algebra.CoerciveCriticalHomogenization

/-! # Arithmetic budgets for coercive critical systems

The integer gradient of the square and its homogenization have mass bounded
by twice the original degree times the square of the original mass. Parameter
coefficients of the homogeneous critical system are linear in each parameter.
These are arithmetic polynomial bounds; no native encoding claim is made.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoerciveCriticalBounds
open scoped Classical BigOperators
open MvPolynomial
set_option backward.isDefEq.respectTransparency false

variable {σ : Type*} [Fintype σ]

noncomputable def coefficientBudget (q : MvPolynomial σ ℤ) (D : ℕ) : ℕ :=
  (2 * D + 2) * (MvMass.mass q ^ 2 + 1)

omit [Fintype σ] in
theorem squareGradient_mass (q : MvPolynomial σ ℤ) (D : ℕ) (hD : q.totalDegree ≤ D) (i : σ) :
    MvMass.mass (pderiv i (q ^ 2)) ≤ 2 * D * MvMass.mass q ^ 2 := by
  apply (MvMass.pderiv_le _ _).trans
  exact Nat.mul_le_mul ((MvPolynomial.totalDegree_pow q 2).trans (Nat.mul_le_mul_left 2 hD))
    (MvMass.pow_le q 2)

omit [Fintype σ] in
/-- Homogenization never increases integer coefficient mass. -/
theorem homogenize_mass_le (w : σ → ℕ) (L : ℕ) (p : MvPolynomial σ ℤ) :
    MvMass.mass (WeightedHomogenization.homogenize w L p) ≤ MvMass.mass p := by
  unfold WeightedHomogenization.homogenize
  apply (MvMass.sum_le _ _).trans
  simp only [MvMass.monomial]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

omit [Fintype σ] in
theorem homogenizedGradient_mass (q : MvPolynomial σ ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : σ) :
    MvMass.mass (WeightedHomogenization.homogenize (fun _ => 1) (2 * D + 1)
      (pderiv i (q ^ 2))) ≤ 2 * D * MvMass.mass q ^ 2 :=
  (homogenize_mass_le _ _ _).trans (squareGradient_mass q D hD i)

omit [Fintype σ] in
theorem integerGradient_mass (q : MvPolynomial σ ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (s : ℤ) (i : σ) :
    MvMass.mass (pderiv i (q ^ 2) +
      monomial (Finsupp.single i (2 * D + 1)) (((2 * D + 2 : ℕ) : ℤ) * s)) ≤
      2 * D * MvMass.mass q ^ 2 + (2 * D + 2) * s.natAbs := by
  apply (MvMass.add_le _ _).trans
  exact Nat.add_le_add (squareGradient_mass q D hD i)
    (by simp only [MvMass.monomial, Int.natAbs_mul, Int.natAbs_natCast]; exact le_rfl)

abbrev Coefficient := Polynomial (Polynomial ℤ)

/-- The two degree bounds concern outer `s` and inner `T`, respectively. -/
structure EntryBounds (p : Coefficient) (M : ℕ) : Prop where
  mass : NestedMass.mass p ≤ M
  outerDegree : p.natDegree ≤ 1
  innerDegree : ∀ k, (p.coeff k).natDegree ≤ 1

namespace EntryBounds

lemma zero : EntryBounds (0 : Coefficient) 0 := ⟨by simp, by simp, by simp⟩

lemma mono {p : Coefficient} {M N : ℕ} (h : EntryBounds p M) (hMN : M ≤ N) : EntryBounds p N :=
  ⟨h.mass.trans hMN, h.outerDegree, h.innerDegree⟩

lemma add {p q : Coefficient} {M N : ℕ} (hp : EntryBounds p M) (hq : EntryBounds q N) :
    EntryBounds (p + q) (M + N) := by
  refine ⟨(NestedMass.add_le _ _).trans (Nat.add_le_add hp.mass hq.mass),
    (Polynomial.natDegree_add_le _ _).trans (max_le hp.outerDegree hq.outerDegree), ?_⟩
  intro k
  rw [Polynomial.coeff_add]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (hp.innerDegree k) (hq.innerDegree k))

lemma sub {p q : Coefficient} {M N : ℕ} (hp : EntryBounds p M) (hq : EntryBounds q N) :
    EntryBounds (p - q) (M + N) := by
  refine ⟨(NestedMass.sub_le _ _).trans (Nat.add_le_add hp.mass hq.mass),
    (Polynomial.natDegree_sub_le _ _).trans (max_le hp.outerDegree hq.outerDegree), ?_⟩
  intro k
  rw [Polynomial.coeff_sub]
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le (hp.innerDegree k) (hq.innerDegree k))

lemma integer (a : ℤ) : EntryBounds (a : Coefficient) a.natAbs := by
  have he : (a : Coefficient) = Polynomial.C (Polynomial.C a) := by simp
  rw [he]
  refine ⟨by simp only [NestedMass.C, coefficientMass_C]; exact le_rfl,
    by simp only [Polynomial.natDegree_C]; exact Nat.zero_le _, ?_⟩
  intro k
  rw [Polynomial.coeff_C]
  split_ifs <;> simp only [Polynomial.natDegree_C, Polynomial.natDegree_zero, Nat.zero_le]

lemma parameter_s (a : ℤ) : EntryBounds ((a : Coefficient) * Polynomial.X) a.natAbs := by
  have he : (a : Coefficient) * Polynomial.X = Polynomial.monomial 1 (Polynomial.C a) := by
    rw [show (a : Coefficient) = Polynomial.C (Polynomial.C a) by simp, Polynomial.C_mul_X_eq_monomial]
  rw [he]
  refine ⟨by simp only [NestedMass.monomial, coefficientMass_C]; exact le_rfl,
    Polynomial.natDegree_monomial_le _, ?_⟩
  intro k
  rw [Polynomial.coeff_monomial]
  split_ifs <;> simp only [Polynomial.natDegree_C, Polynomial.natDegree_zero, Nat.zero_le]

lemma parameter_t : EntryBounds (Polynomial.C Polynomial.X : Coefficient) 1 := by
  refine ⟨?_, by simp, ?_⟩
  · rw [NestedMass.C]
    change coefficientMass (Polynomial.monomial 1 (1 : ℤ)) ≤ 1
    simp only [coefficientMass_monomial]
    decide
  · intro k
    rw [Polynomial.coeff_C]
    split_ifs <;> simp only [Polynomial.natDegree_X, Polynomial.natDegree_zero, le_refl, Nat.zero_le]

lemma ite_zero {p : Coefficient} {M : ℕ} (h : EntryBounds p M) (P : Prop) [Decidable P] :
    EntryBounds (if P then p else 0) M := by
  split_ifs
  · exact h
  · exact zero.mono (Nat.zero_le _)

end EntryBounds

omit [Fintype σ] in
lemma coefficientBudget_ge_two (q : MvPolynomial σ ℤ) (D : ℕ) : 2 ≤ coefficientBudget q D := by
  exact (show 2 * 1 ≤ (2 * D + 2) * (MvMass.mass q ^ 2 + 1) from
    Nat.mul_le_mul (by omega) (by omega))

/-- Every actual homogeneous row coefficient has bounded total integer mass
and degree at most one in each of the two coefficient parameters. -/
theorem system_coefficient_bounds (q : MvPolynomial σ ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (coordinate : σ) (j : Option σ) (e : Option σ →₀ ℕ) :
    EntryBounds ((CoerciveCriticalHomogenization.system q D coordinate j).coeff e)
      (coefficientBudget q D) := by
  cases j with
  | none =>
    rw [CoerciveCriticalHomogenization.system, CoerciveCriticalHomogenization.nativeSystem,
      MvPolynomial.coeff_sub, MvPolynomial.C_mul_X_eq_monomial, MvPolynomial.coeff_monomial,
      MvPolynomial.coeff_X]
    exact ((EntryBounds.parameter_t.ite_zero _).sub ((EntryBounds.integer 1).ite_zero _)).mono
      (coefficientBudget_ge_two q D)
  | some j =>
    let p := WeightedHomogenization.homogenize (fun _ : σ => 1) (2 * D + 1) (pderiv j (q ^ 2))
    have hmap : p.map (Int.castRingHom Coefficient) =
        WeightedHomogenization.homogenize (fun _ => 1) (2 * D + 1)
          (pderiv j ((q.map (Int.castRingHom Coefficient)) ^ 2)) := by
      dsimp only [p]
      rw [WeightedHomogenization.map_homogenize, ← MvPolynomial.pderiv_map, map_pow]
    have hp : EntryBounds (p.coeff e : Coefficient) (2 * D * MvMass.mass q ^ 2) :=
      (EntryBounds.integer _).mono ((MvMass.coeff_le p e).trans (homogenizedGradient_mass q D hD j))
    have hs : EntryBounds
        (((2 * D + 2 : ℕ) : Coefficient) * CoerciveCriticalHomogenization.sParameter) (2 * D + 2) := by
      simpa only [Int.cast_natCast, Int.natAbs_natCast, CoerciveCriticalHomogenization.sParameter] using
        EntryBounds.parameter_s ((2 * D + 2 : ℕ) : ℤ)
    rw [CoerciveCriticalHomogenization.system, CoerciveCriticalHomogenization.nativeSystem]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [← hmap, MvPolynomial.coeff_map, MvPolynomial.coeff_monomial]
    apply (hp.add (hs.ite_zero _)).mono
    have h := Nat.mul_le_mul_right (MvMass.mass q ^ 2) (show 2 * D ≤ 2 * D + 2 by omega)
    unfold coefficientBudget
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem system_coefficient_mass (q : MvPolynomial σ ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (coordinate : σ) (j : Option σ) (e : Option σ →₀ ℕ) :
    NestedMass.mass ((CoerciveCriticalHomogenization.system q D coordinate j).coeff e) ≤
      coefficientBudget q D :=
  (system_coefficient_bounds q D hD coordinate j e).mass

theorem system_coefficient_s_degree (q : MvPolynomial σ ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (coordinate : σ) (j : Option σ) (e : Option σ →₀ ℕ) :
    ((CoerciveCriticalHomogenization.system q D coordinate j).coeff e).natDegree ≤ 1 :=
  (system_coefficient_bounds q D hD coordinate j e).outerDegree

theorem system_coefficient_t_degree (q : MvPolynomial σ ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (coordinate : σ) (j : Option σ) (e : Option σ →₀ ℕ) (k : ℕ) :
    (((CoerciveCriticalHomogenization.system q D coordinate j).coeff e).coeff k).natDegree ≤ 1 :=
  (system_coefficient_bounds q D hD coordinate j e).innerDegree k

section FinLayout
variable {n : ℕ}

theorem finSystem_coefficient_bounds (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (coordinate : Fin n) (j : Fin (n + 1)) (e : Fin (n + 1) →₀ ℕ) :
    EntryBounds ((CoerciveCriticalHomogenization.finSystem q D coordinate j).coeff e)
      (coefficientBudget q D) := by
  let f := CoerciveCriticalHomogenization.layout (n := n)
  have he : e = (e.mapDomain f.symm).mapDomain f := by
    ext i
    simp only [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  have hc : (CoerciveCriticalHomogenization.finSystem q D coordinate j).coeff e =
      (CoerciveCriticalHomogenization.system q D coordinate (f.symm j)).coeff (e.mapDomain f.symm) := by
    unfold CoerciveCriticalHomogenization.finSystem
    conv_lhs => rw [he]
    rw [MvPolynomial.coeff_rename_mapDomain f f.injective]
  rw [hc]
  exact system_coefficient_bounds q D hD coordinate _ _


/-- Entry budgets in the finite layout used by the full Macaulay matrix. -/
theorem finSystem_entryBounds (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (coordinate : Fin n) (j : Fin (n + 1)) (e : Fin (n + 1) →₀ ℕ) :
    EntryBounds ((CoerciveCriticalHomogenization.finSystem q D coordinate j).coeff e)
      (coefficientBudget q D) :=
  finSystem_coefficient_bounds q D hD coordinate j e

end FinLayout
end LeanCanny.Algebra.CoerciveCriticalBounds
