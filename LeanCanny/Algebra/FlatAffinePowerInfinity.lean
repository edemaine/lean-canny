/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffinePowerTower

/-! # Leading cone exclusion for an entire affine power tower

At infinity, the first nonzero stage has zero ancestral levels. Its leading
cone critical equations exclude that stage. Induction therefore excludes
all nonzero infinity roots without assuming smoothness of any affine slice.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffinePowerTower
open MvPolynomial FlatAffineCriticalTower FlatAffineCriticalStage
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {n k : ℕ}

noncomputable def leadingRow (H : MvPolynomial (Fin n) ℤ) (D : ℕ) (s : Fin k → Finset (Fin n))
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (b : (t : Fin k) → Fin n → Level n t.val ℤ)
    (t : Fin k) : Variables n → MvPolynomial (Index n k) ℤ
  | .inl i => gradient H D a t i
  | .inr r => Fin.cases (rename (current t) H)
      (fun j => if j ∈ s t then height t (a t j.succ) - levelLinear t (b t j)
        else X (multiplier t j.succ)) r

lemma row_eval_infinity {K : Type*} [Field K] (phi : ℤ →+* K)
    (low H : MvPolynomial (Fin n) ℤ) (D : ℕ) (hlow : low.totalDegree < D)
    (hH : H.IsHomogeneous D) (hD : 1 < D) (s : Fin k → Finset (Fin n))
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (b : (t : Fin k) → Fin n → Level n t.val ℤ)
    (y : Option (Index n k) → K) (hy : y none = 0) (t : Fin k) (j : Variables n) :
    (WeightedHomogenization.homogenize (fun _ => 1) (rowDegree D j)
      (row (low + H) D s a b t j)).eval₂ phi y =
      (leadingRow H D s a b t j).eval₂ phi (y ∘ some) := by
  cases j with
  | inl i =>
    change (WeightedHomogenization.homogenize (fun _ => 1) (D - 1) (gradient (low + H) D a t i)).eval₂ phi y = _
    rw [gradient_split]
    exact HomogenizationAtInfinity.eval_leading phi _ _ _
      (lower_gradient_degree low D hlow hD t i) (gradient_homogeneous H D hH a t i) y hy
  | inr r =>
    refine Fin.cases ?_ (fun j => ?_) r
    · change (WeightedHomogenization.homogenize (fun _ => 1) D (rename (current t) (low + H))).eval₂ phi y = _
      rw [map_add, add_comm]
      exact HomogenizationAtInfinity.eval_leading phi _ _ _
        ((totalDegree_rename_le _ _).trans_lt hlow) hH.rename_isHomogeneous y hy
    · by_cases hj : j ∈ s t
      · simp only [row, rowDegree, leadingRow, Fin.cases_succ, hj, ite_true]
        have he : height t (a t j.succ) - levelPolynomial t (b t j) =
            (height t (a t j.succ) - levelLinear t (b t j)) + (-C (levelConstant t (b t j))) := by
          unfold levelPolynomial
          ring
        rw [he]
        apply HomogenizationAtInfinity.eval_leading phi _ _ _ ?_
          ((height_homogeneous t _).sub (levelLinear_homogeneous t _)) y hy
        simp only [totalDegree_neg, totalDegree_C]
        decide
      · simp only [row, rowDegree, leadingRow, Fin.cases_succ, hj, ite_false]
        exact HomogenizationAtInfinity.eval_homogeneous phi _ 1 (isHomogeneous_X _ _) y

lemma levelLinear_eval_zero {K : Type*} [CommRing K] (phi : ℤ →+* K)
    (t : Fin k) (b : Level n t.val ℤ) (z : Index n k → K)
    (hz : ∀ j : Fin t.val, ∀ i : Fin n, z (current ⟨j.val, j.isLt.trans t.isLt⟩ i) = 0) :
    (levelLinear t b).eval₂ phi z = 0 := by
  cases b with
  | constant c => simp only [levelLinear, eval₂_zero]
  | height j a => simp only [levelLinear, height, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X, hz, mul_zero, Finset.sum_const_zero]
  | midpoint l r a =>
    simp only [levelLinear, eval₂_add, height, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X, hz, mul_zero,
      Finset.sum_const_zero, add_zero]

/-- The original leading-cone critical equations, with all multiplier slots. -/
def ConeRootFree (H : MvPolynomial (Fin n) ℤ) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → ℤ) : Prop :=
  ∀ (x : Fin n → ℂ) (mu : Fin (n + 1) → ℂ), H.eval₂ (Int.castRingHom ℂ) x = 0 →
    (∀ r ∈ s, ∑ i, (a r.succ i : ℂ) * x i = 0) →
    (∀ i, (pderiv i H).eval₂ (Int.castRingHom ℂ) x = ∑ r, (a r i : ℂ) * mu r) →
    (∀ r, r ∉ s → mu r.succ = 0) → x = 0 ∧ mu = 0

/-- Stagewise cone exclusion forces every coordinate of the leading tower
zero. The induction uses only earlier ambient coordinates in each level. -/
theorem leading_roots_zero (H : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : 1 < D)
    (s : Fin k → Finset (Fin n)) (a : Fin k → Fin (n + 1) → Fin n → ℤ)
    (b : (t : Fin k) → Fin n → Level n t.val ℤ) (hcone : ∀ t, ConeRootFree H (s t) (a t))
    (z : Index n k → ℂ) (hz : ∀ t j, (leadingRow H D s a b t j).eval₂ (Int.castRingHom ℂ) z = 0) : z = 0 := by
  have hs : ∀ m, ∀ hm : m < k, ∀ j : Variables n, z (rowEquiv n k (⟨m, hm⟩, j)) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro hm
      let t : Fin k := ⟨m, hm⟩
      have hb (r : Fin n) : (levelLinear t (b t r)).eval₂ (Int.castRingHom ℂ) z = 0 := by
        apply levelLinear_eval_zero
        intro j i
        exact ih j.val j.isLt (j.isLt.trans hm) (Sum.inl i)
      have hp : H.eval₂ (Int.castRingHom ℂ) (z ∘ current t) = 0 := by
        simpa only [leadingRow, Fin.cases_zero, eval₂_rename] using hz t (Sum.inr 0)
      have hl (r : Fin n) (hr : r ∈ s t) : ∑ i, (a t r.succ i : ℂ) * z (current t i) = 0 := by
        have h := hz t (Sum.inr r.succ)
        simp only [leadingRow, Fin.cases_succ, hr, ite_true, eval₂_sub, hb, sub_zero,
          height, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X, Int.coe_castRingHom] at h
        exact h
      have hg (i : Fin n) : (pderiv i H).eval₂ (Int.castRingHom ℂ) (z ∘ current t) =
          ∑ r, (a t r i : ℂ) * z (multiplier t r) ^ (D - 1) := by
        have h := hz t (Sum.inl i)
        simpa only [leadingRow, gradient, eval₂_sub, eval₂_rename, eval₂_sum, eval₂_mul, eval₂_C,
          eval₂_pow, eval₂_X, Int.coe_castRingHom, sub_eq_zero] using h
      have hu (r : Fin n) (hr : r ∉ s t) : z (multiplier t r.succ) ^ (D - 1) = 0 := by
        have h := hz t (Sum.inr r.succ)
        simp only [leadingRow, Fin.cases_succ, hr, ite_false, eval₂_X] at h
        rw [h, zero_pow (by omega : D - 1 ≠ 0)]
      obtain ⟨hx, hmu⟩ := hcone t (z ∘ current t) (fun r => z (multiplier t r) ^ (D - 1)) hp hl hg hu
      intro j
      cases j with
      | inl i => exact congrFun hx i
      | inr r => exact (pow_eq_zero_iff (by omega : D - 1 ≠ 0)).mp (congrFun hmu r)
  funext j
  obtain ⟨⟨t, r⟩, rfl⟩ := (rowEquiv n k).surjective j
  exact hs t.val t.isLt r

/-- Singular affine slices require no Jacobian premise: cone exclusion alone
excludes roots at infinity of the full shared ancestry tower. -/
theorem noInfinity (low H : MvPolynomial (Fin n) ℤ) (D : ℕ) (hlow : low.totalDegree < D)
    (hH : H.IsHomogeneous D) (hD : 1 < D) (s : Fin k → Finset (Fin n))
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (b : (t : Fin k) → Fin n → Level n t.val ℤ)
    (hcone : ∀ t, ConeRootFree H (s t) (a t)) :
    AffineFiniteCoordinates.NoInfinity (system (low + H) D s a b) (degrees D) := by
  intro y hy hroot
  have hz : y ∘ some = 0 := by
    apply leading_roots_zero H D hD s a b hcone
    intro t j
    have h := hroot (rowEquiv n k (t, j))
    rw [system_row, degrees_row, row_eval_infinity (Int.castRingHom ℂ) low H D hlow hH hD s a b y hy] at h
    exact h
  funext j
  cases j with
  | none => exact hy
  | some i => exact congrFun hz i

/-- Every root of the complete power tower is finite, including all singular
roots and roots whose objective multipliers vanish. -/
theorem finite_roots {K : Type*} [Field K] [CharZero K]
    (low H : MvPolynomial (Fin n) ℤ) (D : ℕ) (hlow : low.totalDegree < D)
    (hH : H.IsHomogeneous D) (hD : 1 < D) (s : Fin k → Finset (Fin n))
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (b : (t : Fin k) → Fin n → Level n t.val ℤ)
    (hcone : ∀ t, ConeRootFree H (s t) (a t)) :
    {z : Index n k → K | ∀ i, (system (low + H) D s a b i).eval₂ (Int.castRingHom K) z = 0}.Finite :=
  AffineFiniteCoordinates.finite_roots (system (low + H) D s a b) (degrees D)
    (system_degree low H D hlow hH hD s a b) (degrees_pos D hD)
    (noInfinity low H D hlow hH hD s a b hcone)

end LeanCanny.Algebra.FlatAffinePowerTower
